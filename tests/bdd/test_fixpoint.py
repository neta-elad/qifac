from qifac.search.bdd.fixpoint import Fixpoint
from qifac.search.bdd.system import System


def test_fixpoint(system: System) -> None:
    fixpoint = Fixpoint(system)

    for i, iteration in enumerate(fixpoint.iterations):
        fixpoint_vectors = {
            assignment.vector for assignment in system.assignments(iteration.post)
        }
        manual_vectors = system.reachable_vectors(i)

        assert manual_vectors <= fixpoint_vectors

    reachable = {
        assignment.vector for assignment in system.assignments(fixpoint.reachable)
    }

    for i in range(3):
        assert system.reachable_vectors(i) <= reachable
