import z3

from qifac.search.bdd.assignment import from_raw
from qifac.search.bdd.universe import from_iterable


def test_assignment() -> None:
    a, b, c = z3.Ints("a b c")
    u, v = z3.Ints("u v")

    universe1 = from_iterable([a, b, c], name=0)
    universe2 = from_iterable([u, v], name=1).with_prefix("y", add=False)

    raw_assignment = {"x⁰₀": True, "x⁰₁": False, "y¹₀": True}

    e1, e2 = from_raw(raw_assignment, (universe1, universe2)).vector
    assert e1.value == c
    assert e2.value == v
