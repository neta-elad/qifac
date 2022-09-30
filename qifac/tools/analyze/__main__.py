import shutil
import tempfile
from argparse import ArgumentParser, Namespace
from pathlib import Path

from pysmt.smtlib.parser import SmtLibParser

from qifac.parsing.instantiation_set import InstantiationSet

from .. import analyze
from ..helpers import stdio_args


def run(args: Namespace) -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)
        input_path = str(dir_path / "input.smt2")
        with open(input_path, "w") as input_file:
            shutil.copyfileobj(args.input, input_file)

        args.parser = SmtLibParser()
        args.script = args.parser.get_script_fname(input_path)

        with open(input_path, "r") as input_file:
            args.instantiations = InstantiationSet.parse(input_file, args.parser)

    if len(args.instantiations.instantiations) > 0:
        args.analyzer(args)


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)

    sub_parsers = parser.add_subparsers()

    max_depth = sub_parsers.add_parser("terms")
    analyze.terms.build_parser(max_depth)
    max_depth.set_defaults(analyzer=analyze.terms.run)

    terms_distance = sub_parsers.add_parser("terms-distance")
    analyze.terms_distance.build_parser(terms_distance)
    terms_distance.set_defaults(analyzer=analyze.terms_distance.run)

    qids = sub_parsers.add_parser("qids")
    analyze.qids.build_parser(qids)
    qids.set_defaults(analyzer=analyze.qids.run)

    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
