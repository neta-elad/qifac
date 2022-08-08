from argparse import ArgumentParser, Namespace

from pysmt.smtlib.parser import SmtLibParser

from .helpers import stdio_args


def filter_named(args: Namespace) -> None:
    smt_parser = SmtLibParser()
    script = smt_parser.get_script(args.input)
    annotations = script.annotations

    asserts = list(script.filter_by_command_name("assert"))

    (get_unsat_core,) = script.filter_by_command_name("get-unsat-core")

    script.commands.remove(get_unsat_core)

    for command in asserts:
        formula = command.args[0]
        if (
            formula not in annotations
            or "named" not in annotations[formula]
            or len(annotations[formula]["named"]) == 0
        ):
            continue
            # raise RuntimeError(f"Unnamed assert {command}")

        (name,) = annotations[formula]["named"]

        if name not in args.names:
            script.commands.remove(command)

    for command in asserts:
        formula = command.args[0]
        annotations.remove_annotation(formula, "named")

    script.serialize(args.output, daggify=False)


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)

    parser.add_argument(
        "-n",
        "--names",
        nargs="+",
        required=True,
        help="Names to keep",
    )

    return parser


if __name__ == "__main__":
    filter_named(build_parser().parse_args())
