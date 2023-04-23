from dataclasses import dataclass, field
from functools import cached_property
from typing import ClassVar, Iterable, List, Set, Tuple

import z3
from dd.autoref import Function as BDDFunction

from ..adt.problem import Problem, QuantifiedAssertion
from .assignment import Assignment, from_raw
from .bdd import BDD
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
        self.bdd.declare(self.variables)

    @cached_property
    def models(self) -> Tuple[Model, ...]:
        return from_refs(self.problem.generate_models(self.terms)[: self.models_amount])

    @cached_property
    def element_universes(self) -> Tuple[Universe[z3.Const], ...]:
        return tuple(model.universe for model in self.models)

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

    @cached_property
    def initial_states(self) -> BDDFunction:
        initial = self.bdd.false

        for constant in self.problem.constants:
            vector = tuple(model.eval(constant) for model in self.models)
            cube = self.bdd.true
            for element in vector:
                cube &= self.bdd.to_expression(element.binary.cube)
            initial = initial | cube

        return initial

    def assignments(self, expression: BDDFunction) -> Iterable[Assignment[z3.Const]]:
        return (
            from_raw(assignment, self.element_universes)
            for assignment in self.bdd.assignments(expression)
        )
