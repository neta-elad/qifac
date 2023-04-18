import math
from dataclasses import dataclass
from typing import Self, Sized

from .binary import Binary


@dataclass(eq=True, frozen=True)
class Range:
    size: int

    def __post_init__(self) -> None:
        if self.size <= 0:
            raise ValueError(f"Ranges must have at least size 1")

    @classmethod
    def from_max(cls, maximum: int) -> Self:
        return cls(math.ceil(math.log(maximum + 1, 2)))

    @classmethod
    def for_sized(cls, container: Sized) -> Self:
        return cls.from_max(len(container) - 1)

    def get(self, value: int) -> Binary:
        return Binary(value, self.size)

    def __call__(self, value: int) -> Binary:
        return self.get(value)
