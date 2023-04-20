import z3

from qifac.search.bdd.model import from_ref, from_refs


def test_model() -> None:
    Node = z3.DeclareSort("Node")
    a, b = z3.Consts("a b", Node)

    formula = a != b
    solver = z3.Solver()

    assert solver.check(formula) == z3.sat

    model = solver.model()
    universe = from_ref(model, name=0)
    assert universe.universe.size == 1

    assert from_refs([model]) == (universe,)
