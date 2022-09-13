import io
from argparse import ArgumentParser, Namespace

from pysmt.smtlib.parser import SmtLibParser

from .helpers import stdio_args


def name(args: Namespace) -> None:
    smt_parser = SmtLibParser()
    script = smt_parser.get_script(args.input)
    annotations = script.annotations

    for i, cmd in enumerate(script.filter_by_command_name("assert")):
        formula = cmd.args[0]
        if formula not in annotations or "named" not in annotations[formula]:
            annotations.add(formula, "named", f"N{i}")

    args.output.write("(set-option :produce-unsat-cores true)\n")
    args.output.write("(set-option :smt.core.minimize true)\n")
    buffer = io.StringIO()
    script.serialize(buffer, daggify=False)
    args.output.write(buffer.getvalue())
    args.output.write("(get-unsat-core)\n")


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)
    return parser


if __name__ == "__main__":
    name(build_parser().parse_args())
