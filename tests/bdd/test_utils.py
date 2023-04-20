import qifac.search.bdd.utils as utils


def test_digits() -> None:
    assert list(utils.digits(975)) == [5, 7, 9]
    assert list(utils.digits(873, big_endian=False)) == [8, 7, 3]


def test_scripts() -> None:
    assert utils.to_subscript(382) == "₃₈₂"
    assert utils.to_superscript(733) == "⁷³³"
