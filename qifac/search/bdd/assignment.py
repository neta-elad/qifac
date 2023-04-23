from dataclasses import dataclass
from functools import cached_property
from typing import Generic, Mapping, Tuple

from . import RawAssignment
from .universe import Element, Universe, Value


@dataclass
class Assignment(Generic[Value]):
    mapping: Mapping[Universe[Value], Element[Value]]

    @cached_property
    def vector(self) -> Tuple[Element[Value], ...]:
        return tuple(self.mapping.values())


def from_raw(
    raw: RawAssignment, universes: Tuple[Universe[Value], ...]
) -> Assignment[Value]:
    return Assignment({universe: universe.parse(raw) for universe in universes})
