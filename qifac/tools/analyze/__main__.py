from argparse import ArgumentParser, Namespace, FileType
import sys

from pysmt.smtlib.parser import SmtLibParser

from ...instantiation_set import InstantiationSet
from .. import analyze


def run(args: Namespace) -> None:
    args.parser = SmtLibParser()
    args.script = args.parser.get_script(args.script)
    args.instantiations = InstantiationSet.parse(args.input, args.parser)
    args.analyzer(args)


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    parser.add_argument(
        "input",
        nargs="?",
        type=FileType("r"),
        default=sys.stdin,
        help="Input analytics file, defaults to stdin",
    )

    parser.add_argument(
        "-s",
        "--script",
        required=True,
        type=FileType("r"),
        help="SMT Lib Script"
    )

    sub_parsers = parser.add_subparsers()

    max_depth = sub_parsers.add_parser("terms")
    analyze.terms.build_parser(max_depth)
    max_depth.set_defaults(analyzer=analyze.terms.run)

    qids = sub_parsers.add_parser("qids")
    analyze.qids.build_parser(qids)
    qids.set_defaults(analyzer=analyze.qids.run)

    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
