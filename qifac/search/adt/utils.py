from typing import Any, cast

import z3


def to_bool(x: Any) -> bool:
    if x is True or x is False:
        return x
    else:
        assert z3.is_true(x) or z3.is_false(x), f"Cannot convert to bool {x}"
        return z3.is_true(x)


def cast_bool(expression: z3.ExprRef) -> z3.BoolRef:
    return cast(z3.BoolRef, expression)


class Relation(z3.FuncDeclRef):
    def __call__(self, *args: z3.ExprRef) -> z3.BoolRef:
        pass


def cast_relation(relation: z3.FuncDeclRef) -> Relation:
    return cast(Relation, relation)
