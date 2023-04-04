import itertools
import math
from dataclasses import dataclass, field
from functools import cached_property
from typing import (
    ClassVar,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Self,
    Set,
    Sized,
    TextIO,
    Tuple,
    cast,
)

import click
import z3
from dd.autoref import BDD
from dd.autoref import Function as BDDFunction

from ..adt.examples import consensus
from ..adt.problem import Problem
from ..adt.utils import to_bool


@click.group
def run() -> None:
    pass


def suffixate(strings: List[str], suffix: str) -> List[str]:
    return [string + suffix for string in strings]


def fixpoint(
    bdd: BDD,
    maximal_arity_of_transitions: int,
    initial: BDDFunction,
    transitions: BDDFunction,
    variables: List[str],
) -> BDDFunction:
    primed = dict(zip(suffixate(variables, "'"), variables))
    subs = [
        dict(zip(variables, suffixate(variables, "_" + str(i))))
        for i in range(maximal_arity_of_transitions)
    ]
    states = initial

    old_states = None

    while old_states != states:
        old_states = states
        next_states = transitions
        exist_set = set()
        for sub in subs:
            next_states &= bdd.let(sub, states)
            exist_set |= set(sub.values())

        next1 = bdd.exist(exist_set, next_states)
        unprimed_next = bdd.let(primed, next1)

        states = states | unprimed_next

    return states


@dataclass
class ModelWrapper:
    model: z3.ModelRef

    @cached_property
    def elements(self) -> List[z3.Const]:
        return list(self.model.get_universe(self.model.get_sort(0)))

    @cached_property
    def indexed_elements(self) -> Mapping[z3.Const, int]:
        return {e: i for i, e in enumerate(self.elements)}

    @cached_property
    def int_elements(self) -> List[int]:
        return list(self.indexed_elements.values())

    @cached_property
    def element_indexes(self) -> Mapping[int, z3.Const]:
        return dict(enumerate(self.elements))

    def indexed_eval(self, exp: z3.ExprRef) -> int:
        return self.indexed_elements[cast(z3.Const, self.eval(exp))]

    def eval(self, exp: z3.ExprRef) -> z3.ExprRef:
        return self.model.eval(exp, model_completion=True)

    def to_element(self, index: int) -> z3.Const:
        return self.element_indexes[index]

    def to_elements(self, vector: Tuple[int, ...]) -> Tuple[z3.Const, ...]:
        return tuple(self.to_element(index) for index in vector)


@dataclass(eq=True, frozen=True)
class AssignedElement:
    model: int
    element: int


@dataclass(eq=True, frozen=True)
class ArgumentElement:
    model: int
    argument: int
    element: int

    @classmethod
    def from_assigned(cls, assigned: AssignedElement, argument: int) -> Self:
        return cls(assigned.model, argument, assigned.element)


@dataclass(eq=True, frozen=True)
class InstanceElement:
    quantifier: int
    model: int
    argument: int
    element: int

    @classmethod
    def from_argument(cls, argument: ArgumentElement, quantifier: int) -> Self:
        return cls(quantifier, argument.model, argument.argument, argument.element)


def bits_for(size: int) -> int:
    return math.ceil(math.log(size, 2))


def bits_for_sized(container: Sized) -> int:
    return bits_for(len(container))


@dataclass
class ModelsRepresentation:
    universes: List[Mapping[z3.Const, int]]
    indexed_universes: List[Mapping[int, z3.Const]]
    universes_bits: List[int]
    variables: List[List[str]]

    @classmethod
    def from_models(cls, models: List[ModelWrapper]) -> "ModelsRepresentation":
        universes: List[Mapping[z3.Const, int]] = []
        indexed_universes: List[Mapping[int, z3.Const]] = []
        universes_bits: List[int] = []
        variables: List[List[str]] = []

        for i, model in enumerate(models):
            universes.append(model.indexed_elements)
            indexed_universes.append(model.element_indexes)
            bits = bits_for_sized(model.elements)
            universes_bits.append(bits)
            variables.append([f"x_{i}_{j}" for j in range(bits)])

        return cls(universes, indexed_universes, universes_bits, variables)


@dataclass
class BDDSystem:
    problem: Problem
    terms: List[z3.ExprRef]
    bdd: BDD = field(default_factory=BDD)
    arguments: ClassVar[int] = 2

    def __post_init__(self) -> None:
        self.bdd.declare(*self.all_vars_with_suffixes)

    @cached_property
    def models(self) -> List[ModelWrapper]:
        return list(map(ModelWrapper, self.problem.generate_models(self.terms)[:5]))

    @cached_property
    def models_representation(self) -> ModelsRepresentation:
        return ModelsRepresentation.from_models(self.models)

    @cached_property
    def universes_bits(self) -> List[int]:
        return self.models_representation.universes_bits

    @cached_property
    def variables(self) -> List[List[str]]:
        return self.models_representation.variables

    @cached_property
    def all_vars(self) -> List[str]:
        return list(itertools.chain(*self.variables))

    @cached_property
    def quantifier_bits(self) -> int:
        return bits_for_sized(self.problem.quantified_assertions)

    @cached_property
    def quantifier_vars(self) -> List[str]:
        return [f"q_{j}" for j in range(self.quantifier_bits)]

    @cached_property
    def all_vars_with_suffixes(self) -> List[str]:
        all_vars_with_suffixes = []

        argument_suffixes = [f"_{j}" for j in range(self.arguments + 1)]

        for suffix in ["", "'"] + argument_suffixes:
            all_vars_with_suffixes.extend(suffixate(self.all_vars, suffix))

        all_vars_with_suffixes.extend(self.quantifier_vars)

        return all_vars_with_suffixes

    @cached_property
    def initial_states(self) -> BDDFunction:
        initial = self.bdd.false

        for constant in self.problem.constants:
            vector = tuple(model.indexed_eval(constant) for model in self.models)
            cube = self.bdd.add_expr(self.to_vars(vector))
            initial = initial | cube

        return initial

    @cached_property
    def transitions(self) -> BDDFunction:
        combined_transitions = self.bdd.false

        for f in self.problem.functions:
            transitions = self.bdd.true
            for i, model in enumerate(self.models):
                model_transitions = self.bdd.false
                for vector in itertools.product(model.int_elements, repeat=f.arity()):
                    pre_state = self.bdd.true
                    for j, e in enumerate(vector):
                        pre_state &= self.bdd.add_expr(
                            self.to_model_vars(i, e, "_" + str(j))
                        )

                    result_element = model.indexed_eval(f(*model.to_elements(vector)))
                    post_state = self.bdd.add_expr(
                        self.to_model_vars(i, result_element, "'")
                    )

                    transition = pre_state & post_state
                    model_transitions |= transition

                transitions &= model_transitions

            combined_transitions |= transitions

        return combined_transitions

    @cached_property
    def reachable_states(self) -> BDDFunction:
        return fixpoint(
            self.bdd,
            self.arguments,
            self.initial_states,
            self.transitions,
            self.all_vars,
        )

    @cached_property
    def instantiations(self) -> List[BDDFunction]:
        result: List[BDDFunction] = []

        for i, model in enumerate(self.models):
            print(f"Model #{i}")
            instantiations = self.bdd.false

            for j, quantifier in enumerate(self.problem.quantified_assertions):
                print(f"Quantifier #{j}")

                for vector in itertools.product(
                    model.int_elements, repeat=quantifier.num_vars
                ):
                    instantiation = self.bdd.add_expr(self.to_quantifier_var(j))
                    for k, e in enumerate(vector):
                        instantiation &= self.bdd.add_expr(
                            self.to_model_vars(i, e, "_" + str(k))
                        )

                    evaluation = to_bool(
                        model.eval(quantifier.instantiate(*model.to_elements(vector)))
                    )

                    print(f"> {vector} {evaluation}")

                    if not evaluation:
                        instantiations |= instantiation

            print(f"> {self.bdd.to_expr(instantiations)}")
            print(self.assignments_to_instance_elements(instantiations, {0}, {0, 1, 2}))
            result.append(instantiations)

        return result

    def to_model_bits(self, model_index: int, element: int) -> str:
        return f"{{0:0{self.universes_bits[model_index]}b}}".format(element)

    def to_quantifier_bits(self, quantifier: int) -> str:
        return f"{{0:0{self.quantifier_bits}b}}".format(quantifier)

    def to_quantifier_var(self, quantifier: int) -> str:
        return self.to_cube("q", "", self.to_quantifier_bits(quantifier))

    def to_var(
        self, model_index: int, element_index: int, bit: str, prime: str = ""
    ) -> str:
        variable = f"x_{model_index}_{element_index}{prime}"
        if bit == "0":
            return "~" + variable
        else:
            return variable

    def to_literal(self, prefix: str, suffix: str, index: int, bit: str) -> str:
        variable = f"{prefix}_{index}{suffix}"
        if bit == "0":
            return "~" + variable
        else:
            return variable

    def to_cube(self, prefix: str, suffix: str, bits: str) -> str:
        return r" /\ ".join(
            self.to_literal(prefix, suffix, j, bit)
            for j, bit in enumerate(reversed(bits))
        )

    def to_vars(self, vector: Tuple[int, ...]) -> str:
        return r" /\ ".join(
            self.to_cube(f"x_{i}", "", self.to_model_bits(i, element))
            # self.to_var(i, j, bit)
            for i, element in enumerate(vector)
            # for j, bit in enumerate(reversed(self.to_model_bits(i, element)))
        )

    def to_model_vars(
        self, model_index: int, element_index: int, prime: str = ""
    ) -> str:
        return self.to_cube(
            f"x_{model_index}", prime, self.to_model_bits(model_index, element_index)
        )

    def show_models(self, rounds: int, *, quiet: bool = False) -> Set[Tuple[int, ...]]:
        terms: Set[z3.ExprRef] = set(self.problem.constants)

        tuples = set()

        if not quiet:
            print("Showing models")

        for _round in range(rounds):
            for term in terms:
                elements = [model.indexed_eval(term) for model in self.models]

                if not quiet:
                    print(f"Term {term}: {elements}")

                tuples.add(tuple(elements))

            next_unary_terms = {
                f(t) for t in terms for f in self.problem.functions if f.arity() == 1
            }
            next_binary_terms = {
                g(t1, t2)
                for t1 in terms
                for t2 in terms
                for g in self.problem.functions
                if g.arity() == 2
            }

            terms = next_unary_terms | next_binary_terms

        return tuples

    @staticmethod
    def bits_to_int(bits: Mapping[int, bool]) -> int:
        result = 0
        for bit, value in bits.items():
            if value:
                result += 2**bit

        return result

    def assignment_to_element(
        self, assignment: Mapping[str, bool], model: int, suffix: str
    ) -> AssignedElement:
        prefix = f"x_{model}_"

        return AssignedElement(
            model, self.assignment_to_int(assignment, prefix, suffix)
        )

    def assignment_to_int(
        self, assignment: Mapping[str, bool], prefix: str, suffix: str
    ) -> int:
        bits = {}
        for key, value in assignment.items():
            if key.startswith(prefix) and key.endswith(suffix):
                bit = int(key.removeprefix(prefix).removesuffix(suffix))
                bits[bit] = value

        return self.bits_to_int(bits)

    def assignment_to_quantifier(self, assignment: Mapping[str, bool]) -> int:
        return self.assignment_to_int(assignment, f"q_", "")

    def assignment_to_elements(
        self,
        assignment: Mapping[str, bool],
        care_models: Set[int],
        care_arguments: Set[int],
    ) -> Set[ArgumentElement]:
        return {
            ArgumentElement.from_assigned(
                self.assignment_to_element(assignment, i, f"_{j}"), j
            )
            for i in care_models
            for j in care_arguments
        }

    def assignment_to_instance_elements(
        self,
        assignment: Mapping[str, bool],
        care_models: Set[int],
        care_arguments: Set[int],
    ) -> Set[InstanceElement]:
        return {
            InstanceElement.from_argument(
                ArgumentElement.from_assigned(
                    self.assignment_to_element(assignment, i, f"_{j}"), j
                ),
                self.assignment_to_quantifier(assignment),
            )
            for i in care_models
            for j in care_arguments
        }

    def assignments_to_instance_elements(
        self,
        e: BDDFunction,
        /,
        care_models: Optional[Set[int]] = None,
        care_arguments: Optional[Set[int]] = None,
    ) -> Set[FrozenSet[InstanceElement]]:
        if care_models is None:
            care_models = set(range(len(self.models)))

        if care_arguments is None:
            care_arguments = set(range(self.arguments + 1))

        return {
            frozenset(
                self.assignment_to_instance_elements(
                    assignment, care_models, care_arguments
                )
            )
            for assignment in self.bdd.pick_iter(e)
        }

    def assignments_to_elements(
        self,
        e: BDDFunction,
        /,
        care_models: Optional[Set[int]] = None,
        care_arguments: Optional[Set[int]] = None,
    ) -> Set[FrozenSet[ArgumentElement]]:
        if care_models is None:
            care_models = set(range(len(self.models)))

        if care_arguments is None:
            care_arguments = set(range(self.arguments + 1))

        return {
            frozenset(
                self.assignment_to_elements(assignment, care_models, care_arguments)
            )
            for assignment in self.bdd.pick_iter(
                e, care_vars=self.all_vars_with_suffixes
            )
        }

    def single_argument_assignments_to_elements(
        self, e: BDDFunction
    ) -> Set[Tuple[int, ...]]:
        return {
            tuple(
                self.assignment_to_element(assignment, i, "").element
                for i in range(len(self.models))
            )
            for assignment in self.bdd.pick_iter(e, care_vars=self.all_vars)
        }


@run.command
@click.argument("smt_file", type=click.File("r"))
def parse(smt_file: TextIO) -> None:
    print("Running BDD search")

    problem = Problem.from_smt_file(smt_file)

    terms = cast(List[z3.ExprRef], list(problem.constants)[:10])

    print(terms)

    system = BDDSystem(problem, terms)

    print(system.assignments_to_elements(system.initial_states))


@run.command
def go() -> None:
    system = BDDSystem(*consensus())

    print("Quantifiers to instantiations")

    for i, model_instantiations in enumerate(system.instantiations):
        print(f"Model #{i}")
        print(
            system.assignments_to_instance_elements(
                model_instantiations, {i}, {0, 1, 2}
            )
        )

    print("Next up: BDD per model for quantifiers x elements (i.e. instantiations)")

    #
    # "x₁₂₃₄₅₆₇₈₉₀₋"
    # "x¹²³⁴⁵⁶⁷⁸⁹⁰⁻"


# given m models
# E: D1 x D2 x ... x Dm -> Bool
# E(e1, ..., em) <-> exists ground term t s.t. forall i in 1 .. m. Ii(t) = ei

# compute E iteratively until we reach a fixpoint
# initially, for every constant c
#   E(I1(c), ..., Im(c))
# then, for every function f(x)
#   E(e1, ..., em) -> E(I1(f)(e1), ..., Im(f)(em))
#   e1 = 0 -> e1' = I1(f)(0) = 1
#   e1 = 1 -> e1' = ...
#   ...
#   em = 0 -> em' = ...
# then for every f(x, y)
#   E(x1, ..., xm) & E(y1, ..., ym) -> E(I1(f)(x1, y1), ..., Im(f)(xm, ym))
#   x1 = 0 & y1 = 0 -> e1' = I1(f)(0, 0) = 1

# E0(e1, ..., em) = V_{c} e1 = I1(c) & ... & em = Im(c)
# E1(e1, ..., em) = V_{f1} exists x1, ..., xm. E0(x1, ..., xm) & TR_f1(x1, ..., xm, e1, ..., em)
#                 | V_{f2} exists x1, ..., xm, y1, ..., ym. E0(x1, ..., xm) & E0(y1, ..., ym) & TR_f2(x, y, e)
#   ...
# ...
# E8
# E9 = E8

# what we really want is
# g: D1 x ... x Dm -> Terms
