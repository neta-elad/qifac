from dataclasses import dataclass, field, replace
from functools import cached_property, reduce
from itertools import product
from operator import and_, or_
from typing import Generic, List, Mapping, Optional, Self, Set, Tuple, TypeVar

import z3
from dd.autoref import Function as BDDFunction

from .bdd import BDD
from .system import System
from .universe import Value
from .vector import Vector

Key = TypeVar("Key")


@dataclass(eq=True, frozen=True)
class Transition:
    system: System
    arity: int
    expression: BDDFunction

    def apply(self, states: BDDFunction) -> Tuple[Set[str], BDDFunction]:
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

        next_states = self.expression & reduce(and_, copies, self.system.bdd.true)

        return all_variables, next_states

    def next(self, states: BDDFunction) -> BDDFunction:
        all_variables, next_states = self.apply(states)

        return states | self.system.bdd.exists(all_variables, next_states)


@dataclass
class Iteration(Generic[Key]):
    pre: BDDFunction
    mapping: Mapping[Key, Transition]
    bdd: BDD = field(default=BDD.default(), kw_only=True)

    @cached_property
    def unquantified_post(self) -> Mapping[Key, BDDFunction]:
        return {
            key: transition.apply(self.pre)[1]
            for key, transition in self.mapping.items()
        }

    @cached_property
    def post_mapping(self) -> Mapping[Key, BDDFunction]:
        return {
            key: transition.next(self.pre) for key, transition in self.mapping.items()
        }

    @cached_property
    def post(self) -> BDDFunction:
        return reduce(or_, self.post_mapping.values())

    @cached_property
    def next(self) -> Self:
        return replace(self, pre=self.post)

    def __contains__(self, item: Vector[Value]) -> bool:
        return (item.cube & self.post) != self.bdd.false

    def __getitem__(self, item: Vector[Value]) -> Key:
        for key, value in self.post_mapping.items():
            if (item.cube & value) != self.bdd.false:
                return key

        raise KeyError("Could not find vector in iteration")


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

        for c in self.system.problem.constants:
            decl = c.decl()
            combined_transitions[decl] = Transition(
                self.system, 0, self.system.eval(c).cube
            )

        for f in self.system.problem.functions:
            transitions = self.system.bdd.true
            for i, model in enumerate(self.system.models):
                model_transitions = self.system.bdd.false
                for vector in map(
                    lambda raw_vector: Vector(raw_vector),
                    product(model.universe.elements, repeat=f.arity()),
                ):
                    pre_state = vector.argument_cube

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

        iterations.pop()

        return iterations

    @cached_property
    def reachable(self) -> BDDFunction:
        return self.iterations[-1].post

    def find_iteration(self, vector: Vector[z3.Const]) -> Optional[int]:
        for i, iteration in enumerate(self.iterations):
            if vector in iteration:
                return i

        return None

    def reconstruct(self, vector: Vector[z3.Const]) -> z3.ExprRef:
        iteration_index = self.find_iteration(vector)
        if iteration_index is None:
            raise ValueError("Unreachable vector")

        iteration = self.iterations[iteration_index]
        f = iteration[vector]

        post = iteration.unquantified_post[f]

        pre_state = post & vector.cube

        assignment = self.system.assignment(pre_state)

        return f(
            *[
                self.reconstruct(assignment.for_argument(i).vector)
                for i in range(f.arity())
            ]
        )

    def __len__(self) -> int:
        return len(self.iterations)
