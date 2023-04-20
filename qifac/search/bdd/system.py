from dataclasses import dataclass, field
from functools import cached_property
from typing import ClassVar, List, Set, Tuple

import z3
from dd.autoref import BDD

from ..adt.problem import Problem
from .universe import Universe, from_models


@dataclass
class System:
    problem: Problem
    terms: List[z3.ExprRef]
    bdd: BDD = field(default_factory=BDD)
    max_arguments: ClassVar[int] = 2
    models_amount: ClassVar[int] = 3

    # def __post_init__(self) -> None:
    #     self.bdd.declare(*self.all_vars_with_suffixes)

    @cached_property
    def universes(self) -> Tuple[Universe, ...]:
        return from_models(
            self.problem.generate_models(self.terms)[: self.models_amount]
        )

    @cached_property
    def output_variables(self) -> Set[str]:
        return {
            variable for universe in self.universes for variable in universe.variables
        }

    @cached_property
    def argument_variables(self) -> Set[str]:
        return {
            variable
            for universe in self.universes
            for argument in range(self.max_arguments)
            for variable in universe.with_prefix(argument).variables
        }

    @cached_property
    def variables(self) -> Set[str]:
        return self.output_variables | self.argument_variables
