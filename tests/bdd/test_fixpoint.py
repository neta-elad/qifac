from qifac.search.bdd.bdd import BDD
from qifac.search.bdd.fixpoint import Fixpoint
from qifac.search.bdd.system import System


def test_fixpoint(system: System) -> None:
    fixpoint = Fixpoint(system)

    initial = fixpoint.iterations[0]

    bdd = BDD.default()

    # for key, transition in initial.mapping.items():
    #     print(f"> {key} {bdd.to_string(transition.expression)}")

    print()

    print(f"{len(fixpoint)} iterations")

    print("Constants")
    for c in system.problem.constants:
        print(f"{c}: {system.eval(c).indices}")

    print("Initial")
    print(bdd.to_string(initial.post))

    print("Transitions")
    for key, transition in initial.mapping.items():
        print(f"{key}: {bdd.to_string(transition.expression)}")

    for i, iteration in enumerate(fixpoint.iterations):
        print(f"Iteration #{i}")
        for assignment in system.assignments(iteration.post):
            print(
                f"{fixpoint.reconstruct(assignment.vector)}: {assignment.vector.indices}"
            )
