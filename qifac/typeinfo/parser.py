import io
from dataclasses import dataclass
from typing import Any, Dict, Optional, Set, TextIO, Tuple

import z3
from pysmt.fnode import FNode
from pysmt.operators import ALL_TYPES, FUNCTION
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibScript
from pysmt.walkers import TreeWalker, handles

from ..tools.helpers import normalize

T_T = z3.DeclareSort("T@T")
T_U = z3.DeclareSort("T@U")
TYPE_FUN = z3.Function("type", T_U, T_T)


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


@dataclass
class TypeInfo:
    grounds: Set[FNode]
    z3_funs: Dict[str, z3.FuncDeclRef]
    fun_types: Dict[str, FNode]
    solver: z3.Solver

    def is_ground(self, term: FNode) -> bool:
        return check_ground_and_update(term, self.grounds)

    def to_z3(self, term: FNode) -> z3.ExprRef:
        if term.node_type() == FUNCTION:
            z3_fun = self.z3_funs[normalize(term.function_name())]
            args = [self.to_z3(sub_term) for sub_term in term.args()]
            return z3_fun(*args)

        symbol_name = str(term.symbol_name())
        symbol_type = term.symbol_type()
        return z3.Const(symbol_name, to_z3_sort(str(symbol_type)))

    def get_type(self, term: FNode) -> Optional[z3.ExprRef]:
        if to_z3_sort(term.get_type()) != T_U:
            return None

        const = self.to_z3(term)

        if term.is_function_application():
            fun = normalize(term.function_name())

            if fun in self.fun_types:
                kind = self.to_z3(self.fun_types[fun])

                return kind

        for type_term in self.grounds:
            if to_z3_sort(type_term.get_type()) != T_T:
                continue

            kind = self.to_z3(type_term)
            formula = z3.Not(TYPE_FUN(const) == kind)

            if self.solver.check(formula) == z3.unsat:
                return kind

        return None


class TypeSystemFormulaChecker(TreeWalker):
    keep: bool

    def __init__(self) -> None:
        super().__init__(self)
        self.keep = True

    @handles(ALL_TYPES)
    def walk_any_type(self, formula: FNode) -> Any:
        if formula.node_type() == FUNCTION:
            if str(formula.get_type()) != "T@T":
                self.keep = False

        return self.walk_skip(formula)

    def check(self, formula: FNode) -> bool:
        self.keep = True
        self.walk(formula)
        return self.keep


class GroundTermsFinder(TreeWalker):
    grounds: Set[FNode]

    def __init__(self, consts: Set[FNode]) -> None:
        super().__init__(self)
        self.grounds = consts

    @handles(ALL_TYPES)
    def walk_any_type(self, formula: FNode) -> Any:
        if formula.node_type() == FUNCTION:
            check_ground_and_update(formula, self.grounds)

        return self.walk_skip(formula)

    def find(self, formula: FNode) -> Set[FNode]:
        self.walk(formula)
        return self.grounds


def is_finite(formula: FNode) -> bool:
    for var in formula.quantifier_vars():
        symbol_type = str(var.symbol_type())
        if symbol_type not in {"Bool", "T@U"}:
            return False

    return True


def parse_fun_type(qid: str, body: FNode) -> Optional[Tuple[Any, Any]]:
    if not qid.startswith("funType:"):
        return None

    type_check = pares_type_check(body)

    if type_check is None:
        return None

    var, kind = type_check

    if not var.is_function_application():
        return None

    return (normalize(var.function_name()), kind)


def parse_script(smt_file: TextIO) -> TypeInfo:
    parser = SmtLibParser()
    script = parser.get_script(smt_file)

    return TypeInfo(
        parse_grounds(script),
        parse_z3_funs(script),
        parse_fun_types(script),
        parse_solver(script),
    )


def parse_consts(script: SmtLibScript) -> Set[FNode]:
    consts = set()
    for command in script.filter_by_command_name("declare-fun"):
        symbol: FNode = command.args[0]

        if not symbol.symbol_type().is_function_type():
            consts.add(symbol)

    return consts


def parse_grounds(script: SmtLibScript) -> Set[FNode]:
    finder = GroundTermsFinder(parse_consts(script))

    asserts = script.filter_by_command_name("assert")
    for command in asserts:
        finder.find(command.args[0])

    return finder.grounds


def parse_z3_funs(script: SmtLibScript) -> Dict[str, z3.FuncDeclRef]:
    funs = {}

    for command in script.filter_by_command_name("declare-fun"):
        symbol: FNode = command.args[0]

        symbol_name = str(symbol.symbol_name())

        if symbol.symbol_type().is_function_type():
            signature = [to_z3_sort(sort) for sort in symbol.symbol_type().param_types]
            signature.append(to_z3_sort(symbol.symbol_type().return_type))
            z3_fun = z3.Function(symbol_name, *signature)
            funs[normalize(symbol_name)] = z3_fun

    return funs


def parse_fun_types(script: SmtLibScript) -> Dict[str, FNode]:
    fun_types = {}
    asserts = script.filter_by_command_name("assert")
    for command in asserts:
        formula: FNode = command.args[0]
        if not formula.is_quantifier():
            continue

        if not is_uninterpreted(formula):
            continue

        body = formula.arg(0)

        qid = None
        if script.annotations.has_annotation(body, "qid"):
            qid = list(script.annotations[body]["qid"])[0]

        if qid is None:
            continue

        fun_type = parse_fun_type(qid, body)

        if fun_type is not None:
            fun, return_type = fun_type
            fun_types[fun] = return_type

    return fun_types


def parse_solver(script: SmtLibScript) -> z3.Solver:
    commands = list(script.commands)
    checker = TypeSystemFormulaChecker()
    asserts = script.filter_by_command_name("assert")
    for command in asserts:
        if not checker.check(command.args[0]):
            script.commands.remove(command)

    buffer = io.StringIO()

    script.serialize(buffer, daggify=False)

    solver = z3.Solver()
    solver.from_string(buffer.getvalue())

    script.commands = commands

    return solver
