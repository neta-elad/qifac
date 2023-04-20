from qifac.search.adt.examples import consensus
from qifac.search.bdd.cli import BDDSystem


def test_reachable() -> None:
    system = BDDSystem(*consensus())

    assert system.show_models(
        1, quiet=True
    ) == system.single_argument_assignments_to_elements(system.initial_states)

    assert system.show_models(
        3, quiet=True
    ) <= system.single_argument_assignments_to_elements(system.reachable_states)
