from dataclasses import dataclass, field
from functools import cached_property
from typing import List, Optional, Self, Set

from .utils import to_subscript


@dataclass(eq=True, frozen=True)
class Binary:
    value: int
    size: int
    default_variable: str = field(default="x")

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

    @cached_property
    def variables(self) -> Set[str]:
        return self.get_variables()

    def as_cube(self, variable: Optional[str] = None) -> str:
        variable = self.get_variable(variable)

        return r" /\ ".join(
            self.as_literal(variable, digit, value)
            for digit, value in enumerate(self.boolean)
        )

    def get_variable(self, variable: Optional[str] = None) -> str:
        if variable is None:
            return self.default_variable

        return variable

    def get_variables(self, variable: Optional[str] = None) -> Set[str]:
        variable = self.get_variable(variable)

        return {f"{variable}{to_subscript(digit)}" for digit in range(self.size)}

    @staticmethod
    def as_literal(variable: str, digit: int, value: bool) -> str:
        literal = f"{variable}{to_subscript(digit)}"

        if value:
            return literal
        else:
            return "~" + literal
