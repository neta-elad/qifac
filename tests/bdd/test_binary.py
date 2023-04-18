import pytest

from qifac.search.bdd.binary import Binary


def test_binary():
    with pytest.raises(ValueError):
        Binary(2, 1)

    number = Binary(2, 3)

    assert number.binary == "010"
    assert number.boolean == [False, True, False]
    assert number.cube == r"~x₀ /\ x₁ /\ ~x₂"
