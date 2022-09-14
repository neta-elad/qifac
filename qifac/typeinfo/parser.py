import io
from typing import Any, Dict, Optional, Set, TextIO, Tuple

import z3
from pysmt.fnode import FNode
from pysmt.operators import ALL_TYPES, FUNCTION
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibScript
from pysmt.walkers import TreeWalker, handles

from ..tools.helpers import normalize
from .types import TypeInfo
from .utils import (
    check_ground_and_update,
    is_uninterpreted,
    pares_type_check,
    to_z3_sort,
)


class TypeSystemFormulaChecker(TreeWalker):
    keep: bool

    def __init__(self) -> None:
        super().__init__()
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
        super().__init__()
        self.grounds = consts

    @handles(ALL_TYPES)
    def walk_any_type(self, formula: FNode) -> Any:
        if formula.node_type() == FUNCTION:
            check_ground_and_update(formula, self.grounds)

        return self.walk_skip(formula)

    def find(self, formula: FNode) -> Set[FNode]:
        self.walk(formula)
        return self.grounds


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
