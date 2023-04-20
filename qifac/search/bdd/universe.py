import math
from dataclasses import dataclass, field
from functools import cached_property
from typing import Iterable, Self, Tuple, Union

import z3

from .binary import Binary
from .utils import to_superscript


@dataclass(eq=True, frozen=True)
class Element:
    element: z3.Const
    index: int
    universe: "Universe"

    @cached_property
    def binary(self) -> Binary:
        return Binary(
            self.index, self.universe.size, f"x{to_superscript(self.universe.index)}"
        )


AnyElement = Union[z3.Const, int, Element]


@dataclass(eq=True, frozen=True)
class Universe:
    raw_elements: Tuple[z3.Const, ...]
    index: int = field(default=0)

    def __post_init__(self) -> None:
        if not self.raw_elements:
            raise ValueError("Empty universe")

    @classmethod
    def from_iterable(cls, iterable: Iterable[z3.Const], index: int = 0) -> Self:
        return cls(tuple(iterable), index)

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
            Element(element, i, self) for i, element in enumerate(self.raw_elements)
        )

    def normalize(self, element: AnyElement) -> Element:
        match element:
            case int() as index:
                return self.elements[index]

            case Element():
                return element

            case _:
                return self.elements[self.raw_elements.index(element)]
