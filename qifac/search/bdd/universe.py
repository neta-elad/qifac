import math
import re
from dataclasses import dataclass, field, replace
from functools import cached_property
from typing import Generic, Iterable, Optional, Pattern, Self, Tuple, TypeVar, Union

import z3

from . import RawAssignment
from .binary import Binary
from .utils import SUBSCRIPTS, parse_subscript, to_subscript, to_superscript

Value = TypeVar("Value", covariant=True)


@dataclass(eq=True, frozen=True)
class Element(Generic[Value]):
    value: Value
    index: int
    universe: "Universe[Value]"
    prefix: str = field(default="x")

    @cached_property
    def binary(self) -> Binary:
        return Binary(
            self.index,
            self.universe.size,
            f"{self.prefix}{self.universe.suffix}",
        )

    def with_prefix(self, prefix: Union[str, int], *, add: bool = True) -> Self:
        if isinstance(prefix, int):
            prefix = to_subscript(prefix)

        if add:
            prefix += self.prefix

        return replace(self, prefix=prefix)


AnyElement = Union[z3.Const, int, Element[Value]]


@dataclass(eq=True, frozen=True)
class Universe(Generic[Value]):
    raw_elements: Tuple[Value, ...]
    name: Optional[int] = field(default=None, kw_only=True)
    prefix: str = field(default="x", kw_only=True)

    def __post_init__(self) -> None:
        if not self.raw_elements:
            raise ValueError("Empty universe")

    def __len__(self) -> int:
        return len(self.raw_elements)

    def __getitem__(self, item: AnyElement[Value]) -> Element[Value]:
        return self.normalize(item)

    @cached_property
    def size(self) -> int:
        return max(1, math.ceil(math.log(len(self), 2)))  # Sort!0 Sort!1 Sort!2
        # todo: does evaluating Sort!0 work as expected?

    @cached_property
    def elements(self) -> Tuple[Element[Value], ...]:
        return tuple(
            Element(element, i, self, self.prefix)
            for i, element in enumerate(self.raw_elements)
        )

    @cached_property
    def variables(self) -> list[str]:
        return [
            variable
            for element in self.elements
            for variable in element.binary.variables
        ]

    @cached_property
    def suffix(self) -> str:
        if self.name is None:
            return ""

        return to_superscript(self.name)

    @cached_property
    def variable_regex(self) -> Pattern[str]:
        return re.compile(
            rf"^{self.prefix}{self.suffix}(?P<subscript>[{SUBSCRIPTS}]+)$"
        )

    def parse_variable(self, variable: str) -> Optional[int]:
        if (match := self.variable_regex.match(variable)) is not None:
            return parse_subscript(match["subscript"])
        return None

    def normalize(self, element: AnyElement[Value]) -> Element[Value]:
        match element:
            case int() as index:
                return self.elements[index]

            case Element():
                return element

            case _:
                return self.elements[self.raw_elements.index(element)]

    def with_prefix(self, prefix: Union[str, int], *, add: bool = True) -> Self:
        if isinstance(prefix, int):
            prefix = to_subscript(prefix)

        if add:
            prefix += self.prefix

        return replace(self, prefix=prefix)

    def parse(self, assignment: RawAssignment) -> Element[Value]:
        index = sum(
            2 ** (self.size - 1 - index)
            for variable, value in assignment.items()
            if value
            if (index := self.parse_variable(variable)) is not None
        )

        return self[index]


def from_iterable(
    iterable: Iterable[Value], *, name: Optional[int] = None
) -> Universe[Value]:
    return Universe(tuple(iterable), name=name)
