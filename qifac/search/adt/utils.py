from typing import Any, cast

import z3


def to_bool(x: Any) -> bool:
    if x is True or x is False:
        return x
    elif z3.is_true(x) or z3.is_false(x):
        return z3.is_true(x)
    else:
        solver = z3.Solver()
        solver.add(x)
        result = solver.check()
        assert result != z3.unknown, f"Cannot assert truth value {x}"
        return result == z3.sat



def cast_bool(expression: z3.ExprRef) -> z3.BoolRef:
    return cast(z3.BoolRef, expression)


class Relation(z3.FuncDeclRef):
    def __call__(self, *args: z3.ExprRef) -> z3.BoolRef:
        pass


def cast_relation(relation: z3.FuncDeclRef) -> Relation:
    return cast(Relation, relation)
