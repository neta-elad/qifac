import pytest
import z3

from qifac.search.bdd.universe import Universe, from_models


def test_basic() -> None:
    a, b, c = z3.Ints("a b c")

    with pytest.raises(ValueError):
        Universe.from_iterable([])

    universe1 = Universe.from_iterable([a])
    universe2 = Universe.from_iterable([a, b])
    universe3 = Universe.from_iterable([a, b, c])

    assert universe1.size == 1
    assert universe2.size == 1
    assert universe3.size == 2

    assert universe3[0].element == a
    assert universe3[1].index == 1


def test_element() -> None:
    a, b, c = z3.Ints("a b c")
    universe = Universe.from_iterable([a, b, c], name=1)

    assert universe[2].binary.binary == "10"
    assert universe[1].binary.cube == r"~x¹₀ /\ x¹₁"
    assert universe[0].with_prefix(3).binary.cube == r"~₃x¹₀ /\ ~₃x¹₁"
    assert universe.with_prefix(3)[0].binary.cube == r"~₃x¹₀ /\ ~₃x¹₁"


def test_variables() -> None:
    a, b, c = z3.Ints("a b c")
    universe = Universe.from_iterable([a, b, c], name=1)

    assert universe.with_prefix(2).variables == {"₂x¹₀", "₂x¹₁"}


def test_model() -> None:
    Node = z3.DeclareSort("Node")
    a, b = z3.Consts("a b", Node)

    formula = a != b
    solver = z3.Solver()

    assert solver.check(formula) == z3.sat

    model = solver.model()
    universe = Universe.from_model(model)
    assert universe.size == 1

    assert from_models([model]) == (universe,)
