from dataclasses import dataclass, field, replace
from functools import cached_property, reduce
from itertools import product
from operator import and_, or_
from typing import Generic, List, Mapping, Optional, Self, Set, Tuple, TypeVar

import z3
from dd.autoref import Function as BDDFunction

from .bdd import BDD
from .system import System, Vector
from .universe import Value

Key = TypeVar("Key")


@dataclass(eq=True, frozen=True)
class Transition:
    system: System
    arity: int
    expression: BDDFunction

    def apply(self, states: BDDFunction) -> BDDFunction:
        copies = []
        all_variables: Set[str] = set()
        for i in range(self.arity):
            substitution = reduce(
                or_,
                (
                    dict(
                        zip(
                            model.universe.variables,
                            model.universe.with_prefix(i).variables,
                        )
                    )
                    for model in self.system.models
                ),
            )
            all_variables.update(substitution.values())
            copies.append(self.system.bdd.let(substitution, states))

        next_states = self.expression & reduce(and_, copies)

        return states | self.system.bdd.exists(all_variables, next_states)


@dataclass
class Iteration(Generic[Key]):
    pre: BDDFunction
    mapping: Mapping[Key, Transition]
    bdd: BDD = field(default=BDD.default(), kw_only=True)

    @cached_property
    def post_mapping(self) -> Mapping[Key, BDDFunction]:
        return {
            key: transition.apply(self.pre) for key, transition in self.mapping.items()
        }

    @cached_property
    def post(self) -> BDDFunction:
        return reduce(or_, self.post_mapping.values())

    @cached_property
    def next(self) -> Self:
        return replace(self, pre=self.post)

    def __contains__(self, item: Vector[Value]) -> bool:
        return (item.cube & self.post) != self.bdd.true

    def __getitem__(self, item: Vector[Value]) -> Key:
        for key, value in self.post_mapping.items():
            if (item.cube & value) != self.bdd.true:
                return key

        raise KeyError("Could not find vector in iteration")

    def witnesses(self, item: Vector[Value]) -> Tuple[Vector[Value], ...]:
        self[item]

        return tuple()


@dataclass
class Fixpoint:
    system: System

    @cached_property
    def initial(self) -> Mapping[z3.FuncDeclRef, BDDFunction]:
        return {
            constant.decl(): self.system.eval(constant).cube
            for constant in self.system.problem.constants
        }

    @cached_property
    def transitions(self) -> Mapping[z3.FuncDeclRef, Transition]:
        combined_transitions = {}

        for f in self.system.problem.functions:
            transitions = self.system.bdd.true
            for i, model in enumerate(self.system.models):
                model_transitions = self.system.bdd.false
                for vector in map(
                    lambda raw_vector: Vector(self.system.bdd, raw_vector),
                    product(model.universe.elements, repeat=f.arity()),
                ):
                    pre_state = vector.cube

                    result = model.eval(
                        f(*(element.value for element in vector.elements))
                    )

                    post_state = self.system.bdd.to_expression(result.binary.cube)

                    model_transitions |= pre_state & post_state

                transitions &= model_transitions

            combined_transitions[f] = Transition(self.system, f.arity(), transitions)

        return combined_transitions

    @cached_property
    def iterations(self) -> List[Iteration[z3.FuncDeclRef]]:
        iterations = [Iteration(self.system.bdd.false, self.transitions)]

        previous_reachable = None

        while iterations[-1].post != previous_reachable:
            previous_reachable = iterations[-1].post
            iterations.append(iterations[-1].next)

        return iterations

    @cached_property
    def reachable(self) -> BDDFunction:
        return self.iterations[-1].post

    def find_iteration(self, vector: Vector[z3.Const]) -> Optional[int]:
        for i, iteration in enumerate(self.iterations):
            if vector in iteration:
                return i

        return None

    def reconstruct(self, vector: Vector[z3.Const]) -> Optional[z3.ExprRef]:
        iteration = self.find_iteration(vector)
        if iteration is None:
            return None

        f = self.iterations[iteration][vector]

        print(f)

        return None
