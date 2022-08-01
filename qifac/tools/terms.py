from typing import Set, TextIO, Dict, Tuple, Optional
from argparse import ArgumentParser, Namespace
import shutil
import tempfile
import itertools
import copy
from pathlib import Path
from dataclasses import dataclass, field

from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import Solver
import z3

from .helpers import stdio_args, RangeType

cache = {}


@dataclass(frozen=True, eq=True)
class Ast:
    fun: z3.FuncDeclRef
    args: Tuple["Ast", ...] = field(default=())

    def apply(self) -> z3.ExprRef:
        if self not in cache:
            cache[self] = self.fun(*(arg.apply() for arg in self.args))

        return cache[self]


def terms(args: Namespace) -> None:
    declarations = get_all_declarations(args.input)

    if args.count:
        count_terms(declarations, args.depth, args.output)
    else:
        show_terms(declarations, args.depth, args.output)


def count_terms(declarations: Set[z3.FuncDeclRef], depth: int, output: TextIO) -> None:
    terms: Dict[z3.SortRef, int] = {}
    for fun in declarations:
        if fun.arity() == 0:
            sort = fun.range()
            if sort not in terms:
                terms[sort] = 0

            terms[sort] += 1

    for _depth in range(1, depth + 1):
        new_terms = {}
        for fun in declarations:
            sort = fun.range()
            if sort not in new_terms:
                new_terms[sort] = 0

            inputs = 1
            for i in range(fun.arity()):
                domain = terms.get(fun.domain(i), 0)
                inputs *= domain

            new_terms[sort] += inputs

        terms = new_terms

    for sort, amount in terms.items():
        output.write(f"{sort}: {amount}\n")


def show_terms(declarations: Set[z3.FuncDeclRef], depth: int, output: TextIO) -> None:
    terms: Dict[z3.SortRef, Set[Ast]] = {}
    for fun in declarations:
        if fun.arity() == 0:
            sort = fun.range()
            sort_terms = terms.setdefault(sort, set())
            sort_terms.add(Ast(fun))

    for _depth in range(1, depth + 1):
        new_terms: Dict[z3.SortRef, Set[Ast]] = {}
        for fun in declarations:
            sort = fun.range()
            sort_terms = new_terms.setdefault(sort, set())
            inputs = []
            for i in range(fun.arity()):
                domain = terms.get(fun.domain(i), set())
                inputs.append(domain)

            for input_tuple in itertools.product(*inputs):
                sort_terms.add(Ast(fun, input_tuple))

        terms = new_terms

    for sort, sort_terms in terms.items():
        for term in sort_terms:
            output.write(f"{term.apply()}: {sort}\n")


def get_all_declarations(source: TextIO) -> Set[z3.FuncDeclRef]:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)

        input_path = str(dir_path / "input.smt2")
        with open(input_path, "w") as file:
            shutil.copyfileobj(source, file)

        solver = z3.Solver()

        solver.from_file(str(input_path))

        declarations = set()

        for assertion in solver.assertions():
            declarations.update(get_declarations(assertion))

        return declarations


def get_declarations(term: z3.ExprRef) -> Set[z3.FuncDeclRef]:
    result = set()

    for child in term.children():
        result.update(get_declarations(child))

    if (
        z3.is_app(term)
        and term.decl().kind() == z3.Z3_OP_UNINTERPRETED
        and term.decl().range() != z3.BoolSort()
    ):
        result.add(term.decl())

    return result


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)

    parser.add_argument(
        "-d",
        "--depth",
        type=int,
        required=True,
        help="Depth of terms",
    )

    parser.add_argument("-c", "--count", action="store_true", help="Count terms")

    return parser


if __name__ == "__main__":
    terms(build_parser().parse_args())
