from typing import Iterable

SUBSCRIPTS = "₀₁₂₃₄₅₆₇₈₉"
SUPERSCRIPTS = "⁰¹²³⁴⁵⁶⁷⁸⁹"


def digits(number: int, big_endian: bool = True) -> Iterable[int]:
    if not big_endian:
        yield from reversed(list(digits(number)))
    elif number == 0:
        yield 0
    else:
        while number > 0:
            yield number % 10
            number //= 10


def to_subscript(number: int) -> str:
    return "".join(SUBSCRIPTS[digit] for digit in digits(number, big_endian=False))


def to_superscript(number: int) -> str:
    return "".join(SUPERSCRIPTS[digit] for digit in digits(number, big_endian=False))


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
