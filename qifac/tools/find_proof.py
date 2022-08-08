from typing import List, Mapping, Dict, TextIO
from argparse import Namespace, ArgumentParser, FileType
import io

from .helpers import stdio_args, log_args, chain_stdio
from .add_proof import add_proof
from .booleanize_quantifiers import booleanize_quantifiers
from .unsat_core import find_unsat_core
from .skolemize import skolemize
from .unique_qids import unique_qids
from .remove_unwanted import remove_unwanted


def find_proof(args: Namespace) -> None:
    args.programmatic = False
    args.save = io.StringIO()
    args.full = io.StringIO()

    if args.pre_unsat_core:
        chain_stdio(
            args,
            unique_qids,
            remove_unwanted,
            find_unsat_core,
            skolemize,
            add_proof,
            booleanize_quantifiers,
            find_unsat_core,
        )
    else:
        chain_stdio(
            args,
            unique_qids,
            remove_unwanted,
            skolemize,
            add_proof,
            booleanize_quantifiers,
            find_unsat_core,
        )

    if args.analytics is not None:
        _write_analytics(args.analytics, args.save, args.full)


def _write_analytics(analytics: TextIO, save: io.StringIO, full: io.StringIO) -> None:
    kept_names = {line for line in save.getvalue().splitlines()}

    instantiations = _parse_instantiations(full.getvalue().splitlines())

    kept_instantiations = {
        name: value for name, value in instantiations.items() if name in kept_names
    }

    for name, lines in kept_instantiations.items():
        analytics.write(name)
        analytics.write("\n")
        for line in lines:
            analytics.write(line)
            analytics.write("\n")
        analytics.write("###")
        analytics.write("\n")


def _parse_instantiations(lines: List[str]) -> Mapping[str, List[str]]:
    reading_name = True

    result: Dict[str, List[str]] = {}

    qid = None

    for line in lines:
        if reading_name:
            qid = line
            reading_name = False
            result[qid] = []
            continue

        if line == "###":
            reading_name = True
            continue

        if qid is not None:
            result[qid].append(line)

    return result


def build_parser(
    parser: ArgumentParser = ArgumentParser(),
) -> ArgumentParser:
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

    parser.add_argument("-a", "--analytics", type=FileType("w"), help="Analytics file")

    return parser


if __name__ == "__main__":
    find_proof(build_parser().parse_args())
