from dataclasses import dataclass, field
from functools import cached_property
from itertools import product
from typing import ClassVar, Iterable, List, Set, Tuple

import z3
from dd.autoref import Function as BDDFunction

from ..adt.problem import Problem, QuantifiedAssertion
from .assignment import Assignment, from_raw
from .bdd import BDD
from .model import Model, from_refs
from .universe import Universe, from_iterable
from .vector import Vector


@dataclass
class System:
    problem: Problem
    terms: List[z3.ExprRef]
    bdd: BDD = field(default=BDD.default(), kw_only=True)
    max_arguments: ClassVar[int] = 3
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
    def elements(self) -> Iterable[Vector[z3.Const]]:
        return map(
            lambda vector: Vector(vector),
            product(*[model.universe.elements for model in self.models]),
        )

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

    def assignment(self, expression: BDDFunction) -> Assignment[z3.Const]:
        return from_raw(self.bdd.assignment(expression), self.element_universes)

    def eval(self, expression: z3.ExprRef) -> Vector[z3.Const]:
        return Vector(tuple(model.eval(expression) for model in self.models))

    def reachable_vectors(self, depth: int) -> Set[Vector[z3.Const]]:
        vectors = set()
        terms: Set[z3.ExprRef] = set(self.problem.constants)

        for i in range(depth + 1):
            for term in terms:
                vectors.add(self.eval(term))

            new_terms = set()

            for f in self.problem.functions:
                inputs = product(terms, repeat=f.arity())
                for arguments in inputs:
                    new_terms.add(f(*arguments))

            terms = new_terms

        return vectors
