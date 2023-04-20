import pytest

from qifac.search.adt.examples import consensus
from qifac.search.bdd.system import System


@pytest.fixture
def system():
    return System(*consensus())


def test_universes(system):
    assert len(system.universes) == System.models_amount
