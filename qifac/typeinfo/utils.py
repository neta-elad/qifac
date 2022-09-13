from typing import Any, Optional, Set, Tuple

import z3
from pysmt.fnode import FNode


def get_antecedent(term: FNode) -> Optional[FNode]:
    if term.is_implies():
        return term.arg(0)

    if term.is_or() and term.arg(0).is_not():
        return term.arg(0).arg(0)

    return None


def is_type_level(term: FNode) -> bool:
    if not term.is_quantifier():
        return False

    return all(str(var.symbol_type()) == "T@T" for var in term.quantifier_vars())


def is_uninterpreted(term: FNode) -> bool:
    if not term.is_quantifier():
        return False

    if all(
        str(var.symbol_type()) not in {"T@U", "T@T"} for var in term.quantifier_vars()
    ):
        return False

    return True


def function_name(term: FNode) -> str:
    if term.is_function_application():
        return str(term.function_name())

    return ""


def pares_type_check(term: FNode) -> Optional[Tuple[FNode, FNode]]:
    if not term.is_equals():
        return None

    left, right = term.args()

    if not left.is_function_application() and not right.is_function_application():
        return None

    if left.is_function_application() and str(left.function_name()) == "type":
        var = left.arg(0)
        return (var, right)

    if right.is_function_application() and str(right.function_name()) == "type":
        var = right.arg(0)
        return (var, left)

    return None


def to_z3_sort(sort: Any) -> z3.SortRef:
    if str(sort) == "Bool":
        return z3.BoolSort()
    return z3.DeclareSort(str(sort))


def check_ground_and_update(term: FNode, grounds: Set[FNode]) -> bool:
    if term in grounds:
        return True

    if not term.args():
        return False

    for sub_term in term.args():
        if not check_ground_and_update(sub_term, grounds):
            return False

    grounds.add(term)
    return True


def is_finite(formula: FNode) -> bool:
    for var in formula.quantifier_vars():
        symbol_type = str(var.symbol_type())
        if symbol_type not in {"Bool", "T@U"}:
            return False

    return True
