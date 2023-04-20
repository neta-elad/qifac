import math
from dataclasses import dataclass, field, replace
from functools import cached_property
from typing import Iterable, Self, Set, Tuple, Union

import z3

from .binary import Binary
from .utils import to_subscript, to_superscript


@dataclass(eq=True, frozen=True)
class Element:
    element: z3.Const
    index: int
    universe: "Universe"
    prefix: str = field(default="")

    @cached_property
    def binary(self) -> Binary:
        return Binary(
            self.index,
            self.universe.size,
            f"{self.prefix}x{to_superscript(self.universe.name)}",
        )

    def with_prefix(self, prefix: Union[str, int]) -> Self:
        if isinstance(prefix, int):
            prefix = to_subscript(prefix)

        return replace(self, prefix=prefix)


AnyElement = Union[z3.Const, int, Element]


@dataclass(eq=True, frozen=True)
class Universe:
    raw_elements: Tuple[z3.Const, ...]
    name: int = field(default=0)
    prefix: str = field(default="")

    def __post_init__(self) -> None:
        if not self.raw_elements:
            raise ValueError("Empty universe")

    @classmethod
    def from_iterable(cls, iterable: Iterable[z3.Const], *, name: int = 0) -> Self:
        return cls(tuple(iterable), name)

    @classmethod
    def from_model(cls, model: z3.ModelRef, *, name: int = 0) -> Self:
        return cls.from_iterable(model.get_universe(model.get_sort(0)), name=name)

    def __len__(self) -> int:
        return len(self.raw_elements)

    def __getitem__(self, item: AnyElement) -> Element:
        return self.normalize(item)

    @cached_property
    def size(self) -> int:
        return max(1, math.ceil(math.log(len(self), 2)))

    @cached_property
    def elements(self) -> Tuple[Element, ...]:
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

    def normalize(self, element: AnyElement) -> Element:
        match element:
            case int() as index:
                return self.elements[index]

            case Element():
                return element

            case _:
                return self.elements[self.raw_elements.index(element)]

    def with_prefix(self, prefix: Union[str, int]) -> Self:
        if isinstance(prefix, int):
            prefix = to_subscript(prefix)

        return replace(self, prefix=prefix)


def from_models(models: Iterable[z3.ModelRef]) -> Tuple[Universe, ...]:
    return tuple(Universe.from_model(model, name=i) for i, model in enumerate(models))
