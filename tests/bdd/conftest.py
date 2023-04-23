import pytest

from qifac.search.adt.examples import consensus
from qifac.search.bdd.system import System


@pytest.fixture
def system() -> System:
    return System(*consensus())
