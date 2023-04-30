from dataclasses import dataclass
from functools import cached_property
from typing import Iterable, Mapping, Self, Set

import dd.autoref as dd

from . import RawAssignment
from .utils import decode, encode


@dataclass
class BDD:
    bdd: dd.BDD

    @classmethod
    def default(cls, bdd: dd.BDD = dd.BDD()) -> Self:
        return cls(bdd)

    @cached_property
    def false(self) -> dd.Function:
        return self.bdd.false

    @cached_property
    def true(self) -> dd.Function:
        return self.bdd.true

    def declare(self, variables: Iterable[str]) -> None:
        self.bdd.declare(*(encode(variable) for variable in variables))

    def let(
        self, substitution: Mapping[str, str], expression: dd.Function
    ) -> dd.Function:
        return self.bdd.let(
            {encode(key): encode(value) for key, value in substitution.items()},
            expression,
        )

    def exists(self, variables: Set[str], expression: dd.Function) -> dd.Function:
        return self.bdd.exist({encode(variable) for variable in variables}, expression)

    def to_expression(self, expression: str) -> dd.Function:
        return self.bdd.add_expr(encode(expression))

    def to_string(self, expression: dd.Function) -> str:
        return decode(self.bdd.to_expr(expression))

    def assignments(self, expression: dd.Function) -> Iterable[RawAssignment]:
        return (
            {decode(key): value for key, value in assignment.items()}
            for assignment in self.bdd.pick_iter(expression)
        )

    def assignment(self, expression: dd.Function) -> RawAssignment:
        return {decode(key): value for key, value in self.bdd.pick(expression).items()}

    def __hash__(self) -> int:
        return id(self)
