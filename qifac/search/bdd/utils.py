from functools import reduce
from typing import Iterable

SUBSCRIPTS = "₀₁₂₃₄₅₆₇₈₉"
SUPERSCRIPTS = "⁰¹²³⁴⁵⁶⁷⁸⁹"


def to_digits(number: int, big_endian: bool = False) -> Iterable[int]:
    if not big_endian:
        yield from reversed(list(to_digits(number, big_endian=True)))
    elif number == 0:
        yield 0
    else:
        while number > 0:
            yield number % 10
            number //= 10


def to_number(digits: Iterable[int], big_endian: bool = False) -> int:
    if big_endian:
        return to_number(reversed(list(digits)), big_endian=False)

    return reduce(lambda number, digit: number * 10 + digit, digits, 0)


def to_subscript(number: int) -> str:
    return "".join(SUBSCRIPTS[digit] for digit in to_digits(number))


def to_superscript(number: int) -> str:
    return "".join(SUPERSCRIPTS[digit] for digit in to_digits(number))


def parse_subscript(number: str) -> int:
    return to_number(SUBSCRIPTS.index(digit) for digit in number)


def parse_superscript(number: str) -> int:
    return to_number(SUPERSCRIPTS.index(digit) for digit in number)


def encode(string: str) -> str:
    for i, char in enumerate(SUBSCRIPTS):
        string = string.replace(char, f"_{i}")

    for i, char in enumerate(SUPERSCRIPTS):
        string = string.replace(char, f"^{i}")

    return string


def decode(string: str) -> str:
    for i, char in enumerate(SUBSCRIPTS):
        string = string.replace(f"_{i}", char)

    for i, char in enumerate(SUPERSCRIPTS):
        string = string.replace(f"^{i}", char)

    return string
