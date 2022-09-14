import z3

from qifac.cegar import cegar_from_solver, remove_quantifiers


def test_remove_quantifiers():
    x, y, c, d = z3.Ints("x y c d")

    formula = z3.And(z3.ForAll(x, z3.Not(x > c)), z3.ForAll(x, x > d))

    print()
    print(remove_quantifiers(formula))


def test_cegar():
    sort = z3.DeclareSort("sort")

    x, y, c, d = z3.Consts("x y c d", sort)

    solver = z3.Solver()

    solver.add(c != d)
    solver.add(z3.ForAll(y, z3.Or(y == c, y == d)))
    solver.add(z3.ForAll(x, x == c))

    assert cegar_from_solver(solver) == [c != d, z3.ForAll(x, x == c)]
