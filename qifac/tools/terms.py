from typing import Set, TextIO, Dict
from argparse import ArgumentParser, Namespace
import shutil
import tempfile
import itertools
import copy
from pathlib import Path

from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import Solver
import z3

from .helpers import stdio_args, RangeType


def terms(args: Namespace) -> None:
    declarations = get_all_declarations(args.input)

    terms: Dict[z3.SortRef, Set[z3.ExprRef]] = {}

    for fun in declarations:
        if fun.arity() == 0:
            sort = fun.range()
            sort_terms = terms.setdefault(sort, set())
            sort_terms.add(fun())

    for _depth in range(1, args.depth + 1):
        for fun in declarations:
            sort = fun.range()
            sort_terms = terms.setdefault(sort, set())
            inputs = []
            for i in range(fun.arity()):
                domain = terms.get(fun.domain(i), set())
                inputs.append(domain)

            for input_tuple in itertools.product(*inputs):
                sort_terms.add(fun(*input_tuple))

    all_terms = list(itertools.chain(*terms.values()))

    if args.count:
        args.output.write(f"{len(all_terms)}\n")
    else:
        for term in all_terms:
            args.output.write(f"{term}\n")


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
