import math
from dataclasses import dataclass, field, replace
from functools import cached_property
from typing import Generic, Iterable, Optional, Self, Set, Tuple, TypeVar, Union

import z3

from .binary import Binary
from .utils import to_subscript, to_superscript

Value = TypeVar("Value", covariant=True)
Value2 = TypeVar("Value2", covariant=True)


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
    name: Optional[int] = field(default=None)
    prefix: str = field(default="x")

    def __post_init__(self) -> None:
        if not self.raw_elements:
            raise ValueError("Empty universe")

    def __len__(self) -> int:
        return len(self.raw_elements)

    def __getitem__(self, item: AnyElement[Value]) -> Element[Value]:
        return self.normalize(item)

    @cached_property
    def size(self) -> int:
        return max(1, math.ceil(math.log(len(self), 2)))

    @cached_property
    def elements(self) -> Tuple[Element[Value], ...]:
        return tuple(
            Element(element, i, self, self.prefix)
            for i, element in enumerate(self.raw_elements)
        )

    @cached_property
    def variables(self) -> Set[str]:
        return {
            variable
            for element in self.elements
            for variable in element.binary.variables
        }

    @cached_property
    def suffix(self) -> str:
        if self.name is None:
            return ""

        return to_superscript(self.name)

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


def from_iterable(
    iterable: Iterable[Value], *, name: Optional[int] = None
) -> Universe[Value]:
    return Universe(tuple(iterable), name)


def from_model(model: z3.ModelRef, *, name: Optional[int] = None) -> Universe[z3.Const]:
    return from_iterable(model.get_universe(model.get_sort(0)), name=name)


def from_models(models: Iterable[z3.ModelRef]) -> Tuple[Universe[z3.Const], ...]:
    return tuple(from_model(model, name=i) for i, model in enumerate(models))
