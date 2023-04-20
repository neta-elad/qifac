from dataclasses import dataclass, field
from functools import cached_property
from typing import ClassVar, List, Tuple

import z3
from dd.autoref import BDD

from ..adt.problem import Problem
from .universe import Universe, from_models


@dataclass
class System:
    problem: Problem
    terms: List[z3.ExprRef]
    bdd: BDD = field(default_factory=BDD)
    arguments: ClassVar[int] = 2
    models_amount: ClassVar[int] = 3

    # def __post_init__(self) -> None:
    #     self.bdd.declare(*self.all_vars_with_suffixes)

    @cached_property
    def universes(self) -> Tuple[Universe, ...]:
        return from_models(
            self.problem.generate_models(self.terms)[: self.models_amount]
        )
