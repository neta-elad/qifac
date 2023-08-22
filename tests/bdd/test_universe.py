import pytest
import z3

from qifac.search.bdd.universe import from_iterable


def test_basic() -> None:
    a, b, c = z3.Ints("a b c")

    with pytest.raises(ValueError):
        from_iterable([])

    universe1 = from_iterable([a])
    universe2 = from_iterable([a, b])
    universe3 = from_iterable([a, b, c])

    assert universe1.size == 1
    assert universe2.size == 1
    assert universe3.size == 2

    for universe in (universe1, universe2, universe3):
        assert len(universe) <= 2**universe.size

    assert universe3[0].value == a
    assert universe3[1].index == 1


def test_element() -> None:
    a, b, c = z3.Ints("a b c")
    universe = from_iterable([a, b, c], name=1)

    assert universe[2].binary.binary == "10"
    assert universe[1].binary.cube == r"~x¹₀ /\ x¹₁"
    assert universe[0].with_prefix(3).binary.cube == r"~₃x¹₀ /\ ~₃x¹₁"
    assert universe.with_prefix(3)[0].binary.cube == r"~₃x¹₀ /\ ~₃x¹₁"


def test_variables() -> None:
    a, b, c = z3.Ints("a b c")
    universe = from_iterable([a, b, c], name=1)

    assert set(universe.with_prefix(2).variables) == {"₂x¹₀", "₂x¹₁"}


def test_parse() -> None:
    a, b, c = z3.Ints("a b c")
    universe = from_iterable([a, b, c], name=1)

    assert universe.parse_variable("x¹₁") == 1
    assert universe.parse_variable("y¹₁") is None

    assert universe.parse({"x¹₀": False, "x¹₁": False}).value == a
    assert universe.parse({"x¹₀": False, "x¹₁": True}).value == b
    assert universe.parse({"x¹₀": True, "x¹₁": False}).value == c
