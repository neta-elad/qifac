from typing import Dict, Optional, Set, Tuple

import z3


def get_antecedent(term: z3.ExprRef) -> Optional[z3.ExprRef]:
    if z3.is_implies(term):
        return term.arg(0)

    if z3.is_or(term) and z3.is_not(term.arg(0)):
        return term.arg(0).arg(0)

    return None


def is_type_level(term: z3.ExprRef) -> bool:
    if not z3.is_quantifier(term):
        return False

    quantifier: z3.QuantifierRef = term

    return all(
        str(quantifier.var_sort(i)) == "T@T" for i in range(quantifier.num_vars())
    )


def is_uninterpreted(term: z3.ExprRef) -> bool:
    if not z3.is_quantifier(term):
        return False

    quantifier: z3.QuantifierRef = term

    return not all(
        str(quantifier.var_sort(i)) not in {"T@U", "T@T"}
        for i in range(quantifier.num_vars())
    )


def pares_type_check(term: z3.ExprRef) -> Optional[Tuple[z3.ExprRef, z3.ExprRef]]:
    if not z3.is_eq(term):
        return None

    left, right = term.children()

    if not z3.is_app(left) and not z3.is_app(right):
        return None

    if z3.is_app(left) and str(left.decl().name()) == "type":
        var = left.arg(0)
        return (var, right)

    if z3.is_app(right) and str(right.decl().name()) == "type":
        var = right.arg(0)
        return (var, left)

    return None


def check_ground_and_update(term: z3.ExprRef, grounds: Set[z3.ExprRef]) -> bool:
    if term in grounds:
        return True

    if not term.children():
        return False

    for sub_term in term.children():
        if not check_ground_and_update(sub_term, grounds):
            return False

    grounds.add(term)
    return True


def is_finite(formula: z3.QuantifierRef) -> bool:
    for i in range(formula.num_vars()):
        var = formula.var_sort(i)
        symbol_type = str(var)
        if symbol_type not in {"Bool", "T@U"}:
            return False

    return True


def find_consts(term: z3.ExprRef, consts: Set[z3.ExprRef]) -> None:
    if (
        z3.is_app(term)
        and term.decl().kind() == z3.Z3_OP_UNINTERPRETED
        and not term.children()
    ):
        return consts.add(term)

    for child in term.children():
        find_consts(child, consts)


def find_funs(term: z3.ExprRef, funs: Dict[str, z3.FuncDeclRef]) -> None:
    if (
        z3.is_app(term)
        and term.decl().kind() == z3.Z3_OP_UNINTERPRETED
        and term.children()
    ):
        funs[str(term.decl().name())] = term.decl()

    for child in term.children():
        find_funs(child, funs)
