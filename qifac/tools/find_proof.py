import argparse
import copy
import io

from .helpers import stdio
from .add_proof import add_proof
from .booleanize_quantifiers import booleanize_quantifiers
from .unsat_core import find_unsat_core

def find_proof(args: argparse.Namespace) -> None:
    add_proof_namespace = copy.copy(args)
    add_proof_namespace.output = io.StringIO()
    add_proof(add_proof_namespace)
    add_proof_namespace.output.seek(0)

    booleanize_quantifiers_namespace = copy.copy(args)
    booleanize_quantifiers_namespace.input = add_proof_namespace.output
    booleanize_quantifiers_namespace.output = io.StringIO()
    booleanize_quantifiers(booleanize_quantifiers_namespace)
    booleanize_quantifiers_namespace.output.seek(0)

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

    return parser


if __name__ == "__main__":
    find_proof(build_parser().parse_args())
