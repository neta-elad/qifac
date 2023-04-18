import pytest

from qifac.search.bdd.range import Range


def test_range():
    with pytest.raises(ValueError):
        Range(0)

    with pytest.raises(ValueError):
        Range.for_sized([])

    assert Range.from_max(2).size == 2
    assert Range.from_max(3).size == 2

    assert Range.for_sized([0, 0, 0]).size == 2
    assert Range.for_sized([0, 0]).size == 1
