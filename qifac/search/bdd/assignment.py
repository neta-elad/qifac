from dataclasses import dataclass, replace
from functools import cached_property
from typing import Generic, Mapping, Self, Tuple

from . import RawAssignment
from .universe import Element, Universe, Value
from .vector import Vector


@dataclass
class Assignment(Generic[Value]):
    universes: Tuple[Universe[Value], ...]
    raw: RawAssignment

    @cached_property
    def mapping(self) -> Mapping[Universe[Value], Element[Value]]:
        return {universe: universe.parse(self.raw) for universe in self.universes}

    @cached_property
    def tuple(self) -> Tuple[Element[Value], ...]:
        return tuple(self.mapping.values())

    @cached_property
    def vector(self) -> Vector[Value]:
        return Vector(self.tuple)

    def for_argument(self, argument: int) -> Self:
        return replace(
            self,
            universes=tuple(
                universe.with_prefix(argument) for universe in self.universes
            ),
        )


def from_raw(
    raw: RawAssignment, universes: Tuple[Universe[Value], ...]
) -> Assignment[Value]:
    return Assignment(universes, raw)
