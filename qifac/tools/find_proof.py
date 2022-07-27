from typing import Optional, TextIO
import argparse
import copy
import io
import sys

from .helpers import stdio
from .add_proof import add_proof
from .booleanize_quantifiers import booleanize_quantifiers
from .unsat_core import find_unsat_core


def find_proof(args: argparse.Namespace) -> None:
    first_input = args.input
    if args.pre_unsat_core:
        pre_unsat_core_namespace = copy.copy(args)
        pre_unsat_core_namespace.programmatic = False
        pre_unsat_core_namespace.output = io.StringIO()
        find_unsat_core(pre_unsat_core_namespace)
        pre_unsat_core_namespace.output.seek(0)
        first_input = pre_unsat_core_namespace.output

        log_output("Pre-unsat core", args.log, pre_unsat_core_namespace.output)

    add_proof_namespace = copy.copy(args)
    add_proof_namespace.input = first_input
    add_proof_namespace.output = io.StringIO()
    add_proof(add_proof_namespace)
    add_proof_namespace.output.seek(0)

    log_output("Add proof", args.log, add_proof_namespace.output)

    booleanize_quantifiers_namespace = copy.copy(args)
    booleanize_quantifiers_namespace.input = add_proof_namespace.output
    booleanize_quantifiers_namespace.output = io.StringIO()
    booleanize_quantifiers(booleanize_quantifiers_namespace)
    booleanize_quantifiers_namespace.output.seek(0)

    log_output(
        "Booleanize quantifiers", args.log, booleanize_quantifiers_namespace.output
    )

    unsat_core_namespace = copy.copy(args)
    unsat_core_namespace.programmatic = False
    unsat_core_namespace.input = booleanize_quantifiers_namespace.output
    find_unsat_core(unsat_core_namespace)


def build_parser(
    parser: argparse.ArgumentParser = argparse.ArgumentParser(),
) -> argparse.ArgumentParser:
    stdio(parser)

    parser.add_argument(
        "-e", "--executable", required=True, help="Z3 executable to use"
    )

    parser.add_argument(
        "-t", "--tracer", required=True, help="Z3Tracer executable to use"
    )

    parser.add_argument(
        "-p",
        "--pre-unsat-core",
        help="Find unsat core of input before finding proof",
        action="store_true",
    )

    parser.add_argument(
        "-l",
        "--log",
        nargs="?",
        type=argparse.FileType("w"),
        default=None,
        const=sys.stderr,
        help="Log for all intremediate states",
    )

    return parser


def log_output(message: str, log: Optional[TextIO], output: io.StringIO) -> None:
    if log is None:
        return

    log.write(message)
    log.write("\n")
    log.write("-" * len(message))
    log.write("\n")
    log.write(output.getvalue())
    log.write("-" * len(message))
    log.write("\n")


if __name__ == "__main__":
    find_proof(build_parser().parse_args())
