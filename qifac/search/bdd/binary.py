from dataclasses import dataclass
from functools import cached_property
from typing import List, Self

from .utils import to_subscript


@dataclass(eq=True, frozen=True)
class Binary:
    value: int
    size: int

    def __post_init__(self) -> None:
        if self.value >= 2**self.size:
            raise ValueError(f"Cannot represent {self.value} with {self.size} bits")

    @classmethod
    def from_binary(cls, binary: str) -> Self:
        return cls(int(binary, 2), len(binary))

    @cached_property
    def binary(self) -> str:
        return f"{{0:0{self.size}b}}".format(self.value)

    @cached_property
    def boolean(self) -> List[bool]:
        return [digit == "1" for digit in self.binary]

    @cached_property
    def cube(self) -> str:
        return self.as_cube()

    def as_cube(self, variable: str = "x") -> str:
        return r" /\ ".join(
            self.as_literal(variable, digit, value)
            for digit, value in enumerate(self.boolean)
        )

    @staticmethod
    def as_literal(variable: str, digit: int, value: bool) -> str:
        literal = f"{variable}{to_subscript(digit)}"

        if value:
            return literal
        else:
            return "~" + literal
