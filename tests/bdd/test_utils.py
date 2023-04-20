import qifac.search.bdd.utils as utils


def test_digits() -> None:
    assert list(utils.digits(975)) == [5, 7, 9]
    assert list(utils.digits(873, big_endian=False)) == [8, 7, 3]


def test_scripts() -> None:
    assert utils.to_subscript(382) == "₃₈₂"
    assert utils.to_superscript(733) == "⁷³³"


def test_encode() -> None:
    assert (
        utils.encode(f"{utils.to_subscript(103)}x{utils.to_superscript(93)}")
        == "_1_0_3x^9^3"
    )


def test_decode() -> None:
    assert utils.decode("_2_3_1x^9^0") == "₂₃₁x⁹⁰"
