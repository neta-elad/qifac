import argparse

from .helpers import stdio_args, log_args, chain_stdio
from .add_proof import add_proof
from .booleanize_quantifiers import booleanize_quantifiers
from .unsat_core import find_unsat_core


def find_proof(args: argparse.Namespace) -> None:
    args.programmatic = False

    if args.pre_unsat_core:
        chain_stdio(
            args, find_unsat_core, add_proof, booleanize_quantifiers, find_unsat_core
        )
    else:
        chain_stdio(args, add_proof, booleanize_quantifiers, find_unsat_core)


def build_parser(
    parser: argparse.ArgumentParser = argparse.ArgumentParser(),
) -> argparse.ArgumentParser:
    stdio_args(parser)
    log_args(parser)

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

    return parser


if __name__ == "__main__":
    find_proof(build_parser().parse_args())
