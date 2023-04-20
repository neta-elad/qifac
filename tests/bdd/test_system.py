import pytest

from qifac.search.adt.examples import consensus
from qifac.search.bdd.system import System


@pytest.fixture
def system() -> System:
    return System(*consensus())


def test_universes(system: System) -> None:
    assert len(system.universes) == System.models_amount


def test_variables(system: System) -> None:
    assert system.output_variables == {"x⁰₀", "x¹₀", "x²₀", "x²₁"}
    assert system.argument_variables == {
        "₀x⁰₀",
        "₀x¹₀",
        "₀x²₀",
        "₀x²₁",
        "₁x⁰₀",
        "₁x¹₀",
        "₁x²₀",
        "₁x²₁",
    }
    assert (
        system.element_variables == system.output_variables | system.argument_variables
    )
