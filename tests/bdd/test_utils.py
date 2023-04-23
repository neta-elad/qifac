import qifac.search.bdd.utils as utils


def test_digits() -> None:
    assert list(utils.to_digits(873)) == [8, 7, 3]
    assert list(utils.to_digits(975, big_endian=True)) == [5, 7, 9]


def test_scripts() -> None:
    assert utils.to_subscript(382) == "₃₈₂"
    assert utils.to_superscript(733) == "⁷³³"


def test_number() -> None:
    assert utils.to_number([3, 6, 2]) == 362
    assert utils.to_number([7, 8, 1], big_endian=True) == 187


def test_parse() -> None:
    assert utils.parse_subscript("₃₈₂") == 382
    assert utils.parse_superscript("⁷³³") == 733


def test_encode() -> None:
    assert (
        utils.encode(f"{utils.to_subscript(103)}x{utils.to_superscript(93)}")
        == "_1_0_3x^9^3"
    )


def test_decode() -> None:
    assert utils.decode("_2_3_1x^9^0") == "₂₃₁x⁹⁰"
