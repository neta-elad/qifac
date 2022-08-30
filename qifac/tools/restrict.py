from ast import parse
import tempfile
from typing import Set, Dict, Any, TextIO, Iterable
from argparse import ArgumentParser, Namespace, FileType
import sys
import io
from pathlib import Path

from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibScript
from pysmt.smtlib.printers import SmtPrinter
from pysmt.walkers import TreeWalker, handles
from pysmt.operators import ALL_TYPES, SYMBOL, FUNCTION, FORALL
from pysmt.fnode import FNode

import z3


from .helpers import stdio_args, normalize

def function_name(term: FNode) -> str:
    if term.is_function_application():
        return str(term.function_name())

    return ''

def is_type_check(term: FNode) -> bool:
    if not term.is_equals():
        return False

    left, right = term.args()

    if not left.is_function_application() and not right.is_function_application():
        return False

    if left.is_function_application() and str(left.function_name()) == 'type':
        return True

    if right.is_function_application() and str(right.function_name()) == 'type':
        return True

    return False

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

            if str(formula.get_type()) != 'T@T':
                self.throw = True
        return self.walk_skip(formula)

    def check(self, formula: FNode) -> bool:
        self.throw = False
        self.walk(formula)
        return not self.throw

def to_z3_sort(sort: Any) -> z3.SortRef:
    if str(sort) == 'Bool':
        return z3.BoolSort()
    return z3.DeclareSort(str(sort))

def run(args: Namespace) -> None:
    parser = SmtLibParser()
    script = parser.get_script(args.input)

    t_t = z3.DeclareSort('T@T')
    t_u = z3.DeclareSort('T@U')

    symbols: Dict[str, Set[str]] = {}
    grounds = set()
    funs = {}

    for command in script.filter_by_command_name('declare-fun'):
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

    total_instantiations = 0
    for command in asserts:
        formula: FNode = command.args[0]
        if formula.is_quantifier():
            instantiations = 1
            for var in formula.quantifier_vars():
                symbol_type = str(var.symbol_type())
                if symbol_type == 'Bool':
                    instantiations *= 2
                elif symbol_type == 'T@U':
                    instantiations *= 8
                else:
                    instantiations *= 0

            
            total_instantiations += instantiations

            if instantiations > 0:
                continue
            body = formula.arg(0)
            if not body.is_implies():
                continue
            antecedent = body.arg(0)
            if not antecedent.is_and():
                continue

            if not all(is_type_check(check) for check in antecedent.args()):
                continue

            print(f'type check {antecedent}')

    print(f"Total is {total_instantiations}")
    exit(-1)

    for command in asserts:
        # if not restricter.check(command.args[0]):
        #     script.commands.remove(command)
        restricter.check(command.args[0])

    exit(-1)

    buffer = io.StringIO()

    script.serialize(buffer, daggify=False)

    solver = z3.Solver()

    solver.from_string(buffer.getvalue())

    assert solver.check() != z3.unsat

    const_to_sort = {}
    sort_to_consts = {}

    t_t = z3.DeclareSort('T@T')
    t_u = z3.DeclareSort('T@U')

    type_fun = z3.Function('type', t_u, t_t)

    grounds = restricter.grounds

    print(f"{len([g for g in grounds if to_z3_sort(g.get_type()) == t_u])} T@Us")
    print(f"{len([g for g in grounds if to_z3_sort(g.get_type()) == t_t])} T@Ts")

    for ground_u in grounds:
        if to_z3_sort(ground_u.get_type()) != t_u:
            continue
        const = to_z3(ground_u, funs)
        for ground_t in restricter.grounds:
            if to_z3_sort(ground_t.get_type()) != t_t:
                continue

            kind = to_z3(ground_t, funs)
            formula = z3.Not(type_fun(const) == kind)

            if solver.check(formula) == z3.unsat:
                const_to_sort[const] = kind
                sort_to_consts.setdefault(kind, set())
                sort_to_consts[kind].add(const)
                break

    for kind, consts in sort_to_consts.items():
        print(f"{kind} has {len(consts)}")

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

            if ground_as_z3 not in const_to_sort or \
                const_to_sort[ground_as_z3] != ty_type:
                continue

            if solver.check(formula) == z3.unsat:
                const_to_sort[const] = kind
                break






def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    parser = stdio_args(parser)

    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())