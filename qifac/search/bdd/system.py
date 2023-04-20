from dataclasses import dataclass, field
from functools import cached_property
from typing import ClassVar, List, Set, Tuple

import z3
from dd.autoref import BDD

from ..adt.problem import Problem, QuantifiedAssertion
from .model import Model, from_refs
from .universe import Universe, from_iterable


@dataclass
class System:
    problem: Problem
    terms: List[z3.ExprRef]
    bdd: BDD = field(default_factory=BDD)
    max_arguments: ClassVar[int] = 2
    models_amount: ClassVar[int] = 3

    def __post_init__(self) -> None:
        self.bdd.declare(*self.variables)

    @cached_property
    def models(self) -> Tuple[Model, ...]:
        return from_refs(self.problem.generate_models(self.terms)[: self.models_amount])

    @cached_property
    def output_variables(self) -> Set[str]:
        return {
            variable for model in self.models for variable in model.universe.variables
        }

    @cached_property
    def argument_variables(self) -> Set[str]:
        return {
            variable
            for universe in self.models
            for argument in range(self.max_arguments)
            for variable in universe.universe.with_prefix(argument).variables
        }

    @cached_property
    def element_variables(self) -> Set[str]:
        return self.output_variables | self.argument_variables

    @cached_property
    def axioms(self) -> Universe[QuantifiedAssertion]:
        return from_iterable(self.problem.quantified_assertions).with_prefix(
            "q", add=False
        )

    @cached_property
    def variables(self) -> Set[str]:
        return self.element_variables | self.axioms.variables
