from qifac.search.bdd.fixpoint import Fixpoint
from qifac.search.bdd.system import System, Vector


def test_fixpoint(system: System) -> None:
    fixpoint = Fixpoint(system)

    for assignment in system.assignments(fixpoint.iterations[0].post):
        print(assignment)

        print(fixpoint.reconstruct(Vector(fixpoint.system.bdd, assignment.vector)))
