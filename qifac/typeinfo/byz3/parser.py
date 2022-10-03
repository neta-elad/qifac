from pathlib import Path
from typing import Any, Dict, Optional, Set, Tuple

import z3

from ...tools.helpers import normalize
from .types import T_T, TypeInfo
from .utils import (
    check_ground_and_update,
    find_consts,
    find_funs,
    is_uninterpreted,
    pares_type_check,
)


class TypeSystemFormulaChecker:
    keep: bool

    def __init__(self) -> None:
        self.keep = True

    def walk_any_type(self, term: z3.ExprRef) -> None:
        if (
            z3.is_app(term)
            and term.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and term.decl().range() != z3.BoolSort()
            and term.decl().range() != T_T
        ):
            self.keep = False

        for child in term.children():
            self.walk_any_type(child)

    def check(self, formula: z3.ExprRef) -> bool:
        self.keep = True
        self.walk_any_type(formula)
        return self.keep


class GroundTermsFinder:
    grounds: Set[z3.ExprRef]

    def __init__(self, consts: Set[z3.ExprRef]) -> None:
        self.grounds = consts

    def walk_any_type(self, term: z3.ExprRef) -> Any:
        for child in term.children():
            self.walk_any_type(child)

        if (
            z3.is_app(term)
            and term.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and term.decl().range() != z3.BoolSort()
        ):
            check_ground_and_update(term, self.grounds)

    def find(self, formula: z3.ExprRef) -> Set[z3.ExprRef]:
        self.walk_any_type(formula)
        return self.grounds


def parse_smt_file(smt_file: Path) -> TypeInfo:
    solver = z3.Solver()
    solver.set("timeout", 5000)
    solver.from_file(str(smt_file))

    return TypeInfo(
        parse_grounds(solver),
        parse_z3_funs(solver),
        parse_fun_types(solver),
        solver,
    )


def parse_consts(solver: z3.Solver) -> Set[z3.ExprRef]:
    consts: Set[z3.ExprRef] = set()
    for assertion in solver.assertions():
        find_consts(assertion, consts)

    return consts


def parse_grounds(solver: z3.Solver) -> Set[z3.ExprRef]:
    finder = GroundTermsFinder(parse_consts(solver))

    for assertion in solver.assertions():
        finder.find(assertion)

    return finder.grounds


def parse_z3_funs(solver: z3.Solver) -> Dict[str, z3.FuncDeclRef]:
    funs: Dict[str, z3.FuncDeclRef] = {}

    for assertion in solver.assertions():
        find_funs(assertion, funs)

    return funs


def parse_fun_types(solver: z3.Solver) -> Dict[str, z3.ExprRef]:
    fun_types = {}
    for formula in solver.assertions():
        if not z3.is_quantifier(formula):
            continue

        if not is_uninterpreted(formula):
            continue

        fun_type = parse_fun_type(formula)

        if fun_type is not None:
            fun, return_type = fun_type
            fun_types[fun] = return_type

    return fun_types


def parse_fun_type(quantifier: z3.QuantifierRef) -> Optional[Tuple[Any, Any]]:
    body = quantifier.body()

    type_check = pares_type_check(body)

    if type_check is None:
        return None

    var, kind = type_check

    if not z3.is_app(var):
        return None

    return (normalize(var.decl().name()), kind)
