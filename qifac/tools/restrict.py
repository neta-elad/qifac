import io
from argparse import ArgumentParser, Namespace
from pathlib import Path
from typing import Any, Dict, Optional, Set, Tuple

import z3
from pysmt.fnode import FNode
from pysmt.operators import ALL_TYPES, FUNCTION
from pysmt.smtlib.parser import SmtLibParser
from pysmt.walkers import TreeWalker, handles

import qifac.typeinfo.utils

from .helpers import normalize, stdio_args


def get_antecedent(term: FNode) -> FNode:
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

    if (
        left.is_function_application()
        and str(qifac.typeinfo.utils.function_name()) == "type"
    ):
        var = left.arg(0)
        return (var, right)

    if (
        right.is_function_application()
        and str(qifac.typeinfo.utils.function_name()) == "type"
    ):
        var = right.arg(0)
        return (var, left)

    return None


def is_ground(term: FNode, consts: Set[FNode]) -> bool:
    if term in consts:
        return True

    if not term.args():
        return False

    for sub_term in term.args():
        if not is_ground(sub_term, consts):
            return False

    return True


def to_z3(term: FNode, funs: Dict[str, Any]) -> z3.ExprRef:
    if term.node_type() == FUNCTION:
        z3_fun = funs[normalize(term.function_name())]
        args = [to_z3(sub_term, funs) for sub_term in term.args()]
        return z3_fun(*args)

    symbol_name = str(term.symbol_name())
    symbol_type = term.symbol_type()
    return z3.Const(symbol_name, to_z3_sort(str(symbol_type)))


class Restricter(TreeWalker):
    tracked: Set[FNode]
    throw: bool
    grounds: Set[FNode]

    def __init__(self, grounds: Set[FNode]) -> None:
        super().__init__(self)
        self.throw = False
        self.grounds = grounds

    @handles(ALL_TYPES)
    def walk_any_type(self, formula: FNode) -> Any:
        if formula.node_type() == FUNCTION:
            if is_ground(formula, self.grounds):
                self.grounds.add(formula)

            if str(formula.get_type()) != "T@T":
                self.throw = True
        return self.walk_skip(formula)

    def check(self, formula: FNode) -> bool:
        self.throw = False
        self.walk(formula)
        return not self.throw


def to_z3_sort(sort: Any) -> z3.SortRef:
    if str(sort) == "Bool":
        return z3.BoolSort()
    return z3.DeclareSort(str(sort))


def get_quantifier_instantiations(formula: FNode) -> int:
    instantiations = 1

    for var in formula.quantifier_vars():
        symbol_type = str(var.symbol_type())
        if symbol_type == "Bool":
            instantiations *= 2
        elif symbol_type == "T@U":
            instantiations *= 8
        else:
            return 0

    return instantiations


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


def run(args: Namespace) -> None:
    parser = SmtLibParser()
    script = parser.get_script(args.input)

    t_t = z3.DeclareSort("T@T")
    t_u = z3.DeclareSort("T@U")

    symbols: Dict[str, Set[str]] = {}
    grounds = set()
    funs = {}

    for command in script.filter_by_command_name("declare-fun"):
        symbol: FNode = command.args[0]

        symbol_type = to_z3_sort(symbol.symbol_type())
        symbol_name = str(symbol.symbol_name())

        if symbol.symbol_type().is_function_type():
            signature = [to_z3_sort(sort) for sort in symbol.symbol_type().param_types]
            signature.append(to_z3_sort(symbol.symbol_type().return_type))
            z3_fun = z3.Function(symbol_name, *signature)
            funs[normalize(symbol_name)] = z3_fun
        else:
            grounds.add(symbol)

            symbols.setdefault(symbol_type, set())

            symbols[symbol_type].add(z3.Const(symbol_name, symbol_type))

    restricter = Restricter(grounds)
    asserts = list(script.filter_by_command_name("assert"))

    # Quantifiers:
    # - Fun type
    # - Guarded
    #   - Type info per var
    # - Only over interpreted infinite sorts (Int and Real)
    # -

    total_quanitifiers = 0
    quantifiers = 0
    type_level_quantifiers = 0
    value_level_quantifiers = 0
    finite_quantifiers = 0
    non_fun_type_quantifiers = 0
    has_antecedent = 0
    quantifiers_with_type_info = 0
    has_full_type_info = 0

    qid_to_type_info = {}
    fun_to_type_info = {}

    for command in asserts:
        formula: FNode = command.args[0]
        if not formula.is_quantifier():
            continue
        total_quanitifiers += 1

        if not is_uninterpreted(formula):
            continue

        quantifiers += 1
        body = formula.arg(0)

        if is_type_level(formula):
            type_level_quantifiers += 1
        else:
            value_level_quantifiers += 1

        qid = None
        if script.annotations.has_annotation(body, "qid"):
            qid = list(script.annotations[body]["qid"])[0]

        if qid is None:
            continue

        qid_to_type_info[qid] = {}

        fun_type = parse_fun_type(qid, body)

        if fun_type is not None:
            fun, return_type = fun_type
            fun_to_type_info[fun] = return_type
            continue

        non_fun_type_quantifiers += 1

        is_finite = get_quantifier_instantiations(formula) > 0

        if not is_finite:
            continue

        finite_quantifiers += 1

        antecedent = get_antecedent(body)

        if antecedent is None:
            continue

        has_antecedent += 1
        antecedent = body.arg(0)
        if not antecedent.is_and():
            var_kind = pares_type_check(antecedent)
            if var_kind is not None:
                var, kind = var_kind
                qid_to_type_info[qid][var] = kind
                quantifiers_with_type_info += 1

                if len(formula.quantifier_vars()) == 1:
                    has_full_type_info += 1

            continue

        for check in antecedent.args():
            var_kind = pares_type_check(check)

            if var_kind is None:
                continue

            var, kind = var_kind

            qid_to_type_info[qid][var] = kind

        type_info = qid_to_type_info[qid]
        if len(type_info) > 0:
            quantifiers_with_type_info += 1

            if len(type_info) == len(formula.quantifier_vars()):
                has_full_type_info += 1

        if len(qid_to_type_info[qid]) == 0:
            print(qid)

    print(
        f"{has_full_type_info}/{quantifiers_with_type_info}/{has_antecedent}/{finite_quantifiers}/{non_fun_type_quantifiers}/{value_level_quantifiers}/{quantifiers}/{total_quanitifiers}"
    )
    print(f"{type_level_quantifiers}/{quantifiers}/{total_quanitifiers}")
    print(f"{len(fun_to_type_info)}/{quantifiers}/{total_quanitifiers}")

    for command in asserts:
        if not restricter.check(command.args[0]):
            script.commands.remove(command)
        # restricter.check(command.args[0])

    buffer = io.StringIO()

    script.serialize(buffer, daggify=False)

    solver = z3.Solver()

    Path("test.smt2").write_text(buffer.getvalue())

    solver.from_string(buffer.getvalue())

    assert solver.check() != z3.unsat

    t_t = z3.DeclareSort("T@T")
    t_u = z3.DeclareSort("T@U")

    type_fun = z3.Function("type", t_u, t_t)

    grounds = restricter.grounds

    print(f"{len([g for g in grounds if to_z3_sort(g.get_type()) == t_u])} T@Us")
    print(f"{len([g for g in grounds if to_z3_sort(g.get_type()) == t_t])} T@Ts")

    const_to_sort = {}
    sort_to_consts = {}

    grounds_t_u = 0
    grounds_understood_from_z3 = 0
    grounds_understood_from_fun_type = 0

    for ground_u in grounds:
        if to_z3_sort(ground_u.get_type()) != t_u:
            continue

        grounds_t_u += 1

        const = to_z3(ground_u, funs)

        if ground_u.is_function_application():
            fun = normalize(ground_u.function_name())

            if fun in fun_to_type_info:
                kind = to_z3(fun_to_type_info[fun], funs)

                const_to_sort[const] = kind
                sort_to_consts.setdefault(kind, set())
                sort_to_consts[kind].add(const)
                grounds_understood_from_fun_type += 1

                continue

        understood = False
        for ground_t in restricter.grounds:
            if to_z3_sort(ground_t.get_type()) != t_t:
                continue

            kind = to_z3(ground_t, funs)
            formula = z3.Not(type_fun(const) == kind)

            if solver.check(formula) == z3.unsat:
                const_to_sort[const] = kind
                sort_to_consts.setdefault(kind, set())
                sort_to_consts[kind].add(const)
                grounds_understood_from_z3 += 1
                understood = True
                break

        if not understood:
            print(ground_u)

    # for kind, consts in sort_to_consts.items():
    #     print(f"{kind} has {len(consts)}")

    print(
        f"{grounds_understood_from_fun_type} + {grounds_understood_from_z3}/{grounds_t_u}"
    )

    # interpreting $Is
    # is_fun = z3.Function('$Is', t_u, t_u, z3.BoolSort())
    # ty_type = z3.Const('TyType', t_t)
    # datatype_type_type = z3.Const('DatatypeTypeType', t_t)

    # const_to_ty_type = {}
    # ty_type_to_consts = {}

    # for const in sort_to_consts[datatype_type_type]:
    #     for ty_const in sort_to_consts[ty_type]:
    #         formula = z3.Not(is_fun(const, ty_const))

    #         if solver.check(formula) == z3.unsat:
    #             const_to_ty_type[const] = ty_const
    #             ty_type_to_consts.setdefault(ty_const, set())
    #             ty_type_to_consts[ty_const].add(const)
    #             break

    #     print(f"{const} of {const_to_ty_type.get(const)}")

    exit(-1)

    for const in symbols[t_u]:
        for ground_t in restricter.grounds:
            if to_z3_sort(ground_t.get_type()) != t_u:
                continue

            ground_as_z3 = to_z3(ground_t, funs)

            if (
                ground_as_z3 not in const_to_sort
                or const_to_sort[ground_as_z3] != ty_type
            ):
                continue

            if solver.check(formula) == z3.unsat:
                const_to_sort[const] = kind
                break


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    parser = stdio_args(parser)

    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
