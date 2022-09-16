import z3

from qifac.cegar import (
    cegar_from_assertions,
    eval_quantifier,
    interpret_functions,
    remove_quantifiers,
)
from qifac.cegar.hitter import Hitter


def test_minimal_hitting_set():
    bs = [z3.Bool(f"b{i}") for i in range(10)]
    hitter = Hitter(set(bs))

    hitter.add(set(bs[0:2]))
    hitter.add(set(bs[4:6]))
    hitter.add({bs[0], bs[5], bs[8]})

    minimum = hitter.minimum()

    assert len(minimum) == 2

    assert bs[0] in minimum or bs[5] in minimum


def test_remove_quantifiers():
    x, y, c, d = z3.Ints("x y c d")

    formula = z3.And(z3.ForAll(x, z3.Not(x > c)), z3.ForAll(x, x > d))

    print()
    print(remove_quantifiers(formula))


def test_interpret_functions():
    x, c = z3.Ints("x c")
    f = z3.Function("f", z3.IntSort(), z3.IntSort())

    formula = z3.ForAll(x, x == c)

    solver = z3.Solver()
    solver.check(formula)
    model = solver.model()

    print()
    print(interpret_functions(model, c != f(c), set()))


def test_cegar():
    sort = z3.DeclareSort("sort")

    x, y, c, d = z3.Consts("x y c d", sort)

    solver = z3.Solver()

    solver.add(c != d)
    solver.add(z3.ForAll(y, z3.Or(y == c, y == d)))
    solver.add(z3.ForAll(x, x == c))

    assert cegar_from_assertions(set(solver.assertions())) == {
        c != d,
        z3.ForAll(x, x == c),
    }


def test_simple_cegar():
    sort = z3.DeclareSort("sort")
    x, c, d = z3.Consts("x c d", sort)
    f = z3.Function("f", sort, sort)

    assert1 = c == f(c)
    assert2 = c != d
    assert3 = z3.ForAll(x, x != f(x))

    solver = z3.Solver()

    solver.add(assert1)

    assert solver.check() == z3.sat

    model = solver.model()

    print()

    print(model.eval(assert2))
    print(eval_quantifier(model, model.eval(assert2)))

    solver.add(assert2)

    assert solver.check() == z3.sat

    model = solver.model()

    print(model.eval(assert3))
    print(eval_quantifier(model, model.eval(assert3)))

    solver.add(assert3)

    assert solver.check() == z3.unsat
