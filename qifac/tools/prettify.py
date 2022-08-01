from typing import Set
from argparse import ArgumentParser, Namespace
import shutil
import tempfile
from pathlib import Path

from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import Solver
import z3

from .helpers import stdio_args


def prettify(args: Namespace) -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)

        input_path = str(dir_path / "input.smt2")
        with open(input_path, "w") as file:
            shutil.copyfileobj(args.input, file)

        smt_parser = SmtLibParser()
        script = smt_parser.get_script_fname(input_path)
        script.commands = list(script.filter_by_command_name("set-info")) + list(
            script.filter_by_command_name("set-option")
        )

        script.serialize(args.output, daggify=False)

        solver = z3.Solver()
        solver.set(unsat_core=True)
        solver.from_file(input_path)
        args.output.write(solver.sexpr())

    args.output.write("(check-sat)\n")


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)
    return parser


if __name__ == "__main__":
    prettify(build_parser().parse_args())
