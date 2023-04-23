from dataclasses import dataclass, field
from functools import cached_property
from typing import Iterable

import dd.autoref as dd

from . import RawAssignment
from .utils import decode, encode


@dataclass
class BDD:
    bdd: dd.BDD = field(default_factory=dd.BDD)

    @cached_property
    def false(self) -> dd.Function:
        return self.bdd.false

    @cached_property
    def true(self) -> dd.Function:
        return self.bdd.true

    def declare(self, variables: Iterable[str]) -> None:
        self.bdd.declare(*(encode(variable) for variable in variables))

    def to_expression(self, expression: str) -> dd.Function:
        return self.bdd.add_expr(encode(expression))

    def to_string(self, expression: dd.Function) -> str:
        return decode(self.bdd.to_expr(expression))

    def assignments(self, expression: dd.Function) -> Iterable[RawAssignment]:
        return (
            {decode(key): value for key, value in assignment.items()}
            for assignment in self.bdd.pick_iter(expression)
        )
