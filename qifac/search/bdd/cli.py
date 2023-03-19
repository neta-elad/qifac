import itertools
import math
from dataclasses import dataclass, field
from functools import cached_property
from typing import Dict, List, Mapping, Set, Tuple, cast

import click
import z3
from dd.autoref import BDD
from dd.autoref import Function as BDDFunction

from ..adt.examples import consensus
from ..adt.problem import Problem


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
        dict(zip(variables, suffixate(variables, str(i))))
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


# def show_model(model: z3.ModelRef, problem: Problem) -> None:
#     elements = {e: i for i, e in enumerate(model.get_universe(model.get_sort(0)))}
#
#     def eval(exp):
#         return elements[model.eval(exp, model_completion=True)]
#
#     print(tabulate([[eval(c) for c in problem.constants]], headers=[str(c) for c in problem.constants]))
#
#     for f in problem.functions:
#         if f.arity() == 1:
#             print(tabulate([[i, eval(f(e))] for e, i in elements.items()], headers=["", str(f)]))


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

    def eval(self, exp: z3.ExprRef) -> int:
        return self.indexed_elements[
            cast(z3.Const, self.model.eval(exp, model_completion=True))
        ]

    def to_element(self, index: int) -> z3.Const:
        return self.element_indexes[index]

    def to_elements(self, vector: Tuple[int, ...]) -> Tuple[z3.Const, ...]:
        return tuple(self.to_element(index) for index in vector)


# @run.command
# def test() -> None:
#     print("Running BDD test")
#
#     bdd = BDD()
#     bdd.declare("x", "y", "x'", "y'", "x0", "y0", "x1", "y1")
#
#     def print_assignments(e):
#         print(f"Printing assignments for {bdd.to_expr(e)}")
#         for ass in bdd.pick_iter(e, care_vars=["x", "y"]):
#             print("> " + str(ass))
#
#     initial = bdd.add_expr(r"~x /\ ~y")
#
#     print_assignments(initial)
#
#     all_transitions = bdd.false
#     all_transitions = bdd.ite(bdd.add_expr(r"~x0 /\ ~y0"), bdd.add_expr(r"~x' /\ y'"), all_transitions)
#     all_transitions = bdd.ite(bdd.add_expr(r"(~x0 /\ ~y0) /\ (~x1 /\ y1)"), bdd.add_expr(r"x' /\ ~y'"), all_transitions)
#
#     reachable = fixpoint(bdd, 2, initial, all_transitions, ["x", "y"])
#
#     print_assignments(reachable)


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
            bits = math.ceil(math.log(len(model.elements), 2))
            universes_bits.append(bits)
            variables.append([f"x^{i}_{j}" for j in range(bits)])

        return cls(universes, indexed_universes, universes_bits, variables)


@dataclass
class BDDSystem:
    problem: Problem
    terms: List[z3.ExprRef]
    bdd: BDD = field(default_factory=BDD)

    def __post_init__(self) -> None:
        self.bdd.declare(*self.all_vars_with_suffixes)

    @cached_property
    def models(self) -> List[ModelWrapper]:
        return list(map(ModelWrapper, self.problem.generate_models(self.terms)))

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
    def all_vars_with_suffixes(self) -> List[str]:
        all_vars_with_suffixes = []

        for suffix in ["", "'", "0", "1", "2", "3"]:
            all_vars_with_suffixes.extend(suffixate(self.all_vars, suffix))

        return all_vars_with_suffixes

    @cached_property
    def initial_states(self) -> BDDFunction:
        initial = self.bdd.false

        print("Calculating initial state")

        for constant in self.problem.constants:
            vector = tuple(model.eval(constant) for model in self.models)
            cube = self.bdd.add_expr(self.to_vars(vector))
            initial = initial | cube

        return initial

    @cached_property
    def transitions(self) -> BDDFunction:
        combined_transitions = self.bdd.true

        for i, model in enumerate(self.models):
            transitions = self.bdd.false
            for f in self.problem.functions:
                for vector in itertools.product(model.int_elements, repeat=f.arity()):
                    conditions = self.bdd.true
                    for j, e in enumerate(vector):
                        conditions &= self.bdd.add_expr(
                            self.to_model_vars(i, e, str(j))
                        )

                    result = self.bdd.add_expr(
                        self.to_model_vars(i, model.eval(f(*model.to_elements(vector))))
                    )

                    transitions = self.bdd.ite(conditions, result, transitions)

            combined_transitions &= transitions

        return combined_transitions

    @cached_property
    def reachable_states(self) -> BDDFunction:
        print("Calculating reachable states")

        return fixpoint(
            self.bdd, 1, self.initial_states, self.transitions, self.all_vars
        )

    def to_model_bits(self, model_index: int, element: int) -> str:
        return f"{{0:0{self.universes_bits[model_index]}b}}".format(element)

    def to_var(
        self, model_index: int, element_index: int, bit: str, prime: str = ""
    ) -> str:
        variable = f"x^{model_index}_{element_index}{prime}"
        if bit == "0":
            return "~" + variable
        else:
            return variable

    def to_vars(self, vector: Tuple[int, ...]) -> str:
        return r" /\ ".join(
            self.to_var(i, j, bit)
            for i, element in enumerate(vector)
            for j, bit in enumerate(reversed(self.to_model_bits(i, element)))
        )

    def to_model_vars(
        self, model_index: int, element_index: int, prime: str = ""
    ) -> str:
        return r" /\ ".join(
            self.to_var(model_index, j, bit, prime)
            for j, bit in enumerate(
                reversed(self.to_model_bits(model_index, element_index))
            )
        )

    def show_models(self, rounds: int) -> Set[Tuple[int, ...]]:
        terms: Set[z3.ExprRef] = set(self.problem.constants)

        table = []

        tuples = set()

        print("Showing models")

        for _round in range(rounds):
            for term in terms:
                elements = [model.eval(term) for model in self.models]

                print(f"Term {term}: {elements}")

                tuples.add(tuple(elements))
                table.append([str(term)] + list(map(str, elements)))

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

            terms = next_unary_terms  # | next_binary_terms

        # print(tabulate(table))

        return tuples

    @staticmethod
    def bits_to_int(bits: Mapping[int, bool]) -> int:
        result = 0
        for bit, value in bits.items():
            if value:
                result += 2**bit

        return result

    def assignment_to_elements(self, assignment: Mapping[str, bool]) -> Tuple[int, ...]:
        variables: Dict[int, Dict[int, bool]] = {}
        for key, value in assignment.items():
            index, bit = map(int, key.removeprefix("x^").split("_", maxsplit=2))
            variables.setdefault(index, {})
            variables[index][bit] = value

        return tuple(
            self.bits_to_int(variables[index]) for index in range(len(self.models))
        )

    def assignments_to_elements(self, e: BDDFunction) -> Set[Tuple[int, ...]]:
        return {
            self.assignment_to_elements(assignment)
            for assignment in self.bdd.pick_iter(e, care_vars=self.all_vars)
        }


@run.command
def go() -> None:
    print("Running BDD search")

    system = BDDSystem(*consensus())

    print(f"Considering terms {system.terms}")

    print(system.show_models(1))
    print(system.assignments_to_elements(system.initial_states))

    print(system.show_models(2))
    print(system.assignments_to_elements(system.reachable_states))

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
