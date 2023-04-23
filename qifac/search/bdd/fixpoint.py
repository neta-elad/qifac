from dataclasses import dataclass
from functools import cached_property, reduce
from operator import or_
from typing import Generic, List, Mapping, TypeVar

from dd.autoref import Function as BDDFunction

from .bdd import BDD

Key = TypeVar("Key")


@dataclass(eq=True, frozen=True)
class Transition:
    arity: int
    expression: BDDFunction


@dataclass
class Iteration(Generic[Key]):
    bdd: BDD
    mapping: Mapping[Key, BDDFunction]

    @cached_property
    def reachable(self) -> BDDFunction:
        return reduce(or_, self.mapping.values(), self.bdd.false)


@dataclass
class Fixpoint(Generic[Key]):
    bdd: BDD
    initial: Mapping[Key, BDDFunction]
    transitions: Mapping[Key, Transition]

    @cached_property
    def iterations(self) -> List[Iteration[Key]]:
        iterations = []

        iterations.append(Iteration(self.bdd, self.initial))

        return iterations

    @cached_property
    def reachable(self) -> BDDFunction:
        return self.iterations[-1].reachable
        # primed = dict(zip(suffixate(variables, "'"), variables))
        # subs = [
        #     dict(zip(variables, suffixate(variables, "_" + str(i))))
        #     for i in range(maximal_arity_of_transitions)
        # ]
        # states = initial
        #
        # old_states = None
        #
        # while old_states != states:
        #     old_states = states
        #     next_states = transitions
        #     exist_set = set()
        #     for sub in subs:
        #         next_states &= bdd.let(sub, states)
        #         exist_set |= set(sub.values())
        #
        #     next1 = bdd.exist(exist_set, next_states)
        #     unprimed_next = bdd.let(primed, next1)
        #
        #     states = states | unprimed_next
        #
        # return states
