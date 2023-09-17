import itertools
from dataclasses import dataclass
from typing import Tuple, List, Dict

import z3
from z3 import substitute, Var, substitute_vars

from .fixpoint import Fixpoint


@dataclass
class Instantiations:
    fixpoint: Fixpoint

    def check_assertions(self, instantiation: Tuple[z3.ExprRef]) -> Tuple[bool]:
        for assertion in self.fixpoint.system.problem.forall_assertions:
            if assertion.num_vars() != len(instantiation):
                continue
            assert assertion.is_forall(), f"{assertion=}"
            instantiated_assertion = substitute_vars(assertion.body(), *instantiation)
            return tuple(
                m.eval(instantiated_assertion) for m in self.fixpoint.system.models
            )

    def all_false_instantiations(
        self, arity: int
    ) -> Dict[Tuple[bool], Tuple[z3.ExprRef]]:
        result = dict()
        for values in itertools.product(
            self.fixpoint.reachable_vectors.values(), repeat=arity
        ):
            possible_ins = tuple(self.fixpoint.reconstruct(value) for value in values)
            evaluations = self.check_assertions(possible_ins)
            if not all(evaluations):
                # TODO: If one eval is strictly better than another (Contains false
                #       in all the same places + at least one more) we only want to
                #       keep it.
                result[evaluations] = possible_ins
        return result
