import pytest
import z3

from qifac.search.bdd.universe import Universe


def test_universe():
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
    assert universe3[2].binary.binary == "10"
    assert universe3[1].binary.cube == r"~x₀ /\ x₁"