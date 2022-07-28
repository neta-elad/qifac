from typing import TextIO, List, Optional
import argparse
import tempfile
import subprocess
import io
import shutil
from pathlib import Path

import z3
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibCommand, SmtLibScript
from pysmt.smtlib.printers import SmtPrinter

from .helpers import stdio_args, log_args, log_output
from .name import name
from .filter_named import filter_named


def find_unsat_core(args: argparse.Namespace) -> None:
    if args.programmatic:
        result = find_unsat_core_programmatic(args.input.read())
        args.output.write(result)
    else:
        find_unsat_core_executable(args.input, args.executable, args.output)


def find_unsat_core_programmatic(smt_file: str) -> str:
    solver = z3.Solver()
    solver.from_string(smt_file)

    assert solver.check() == z3.unsat

    checks = solver.assertions()
    solver.reset()
    current = list(checks)
    true = z3.BoolVal(True)
    for i in range(len(checks)):
        solver.reset()
        current[i] = true
        if solver.check(*current) != z3.unsat:
            current[i] = checks[i]

    final = [check for check in current if check is not true]

    solver.assert_exprs(*final)
    return solver.to_smt2()


def find_unsat_core_executable(
    smt_file: TextIO, executable: str, output: TextIO
) -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)

        input_path = dir_path / "input.smt2"
        with open(input_path, "w") as file:
            shutil.copyfileobj(smt_file, file)

        named_path = dir_path / "named.smt2"
        with open(input_path, "r") as input_smt, open(named_path, "w") as output_smt:
            namespace = argparse.Namespace()
            namespace.input = input_smt
            namespace.output = output_smt
            name(namespace)

        result = subprocess.run(
            [executable, named_path], capture_output=True, text=True
        ).stdout

        keep = result.splitlines()[-1][1:-1].split(" ")

        with open(named_path, "r") as input_smt:
            namespace = argparse.Namespace()
            namespace.input = input_smt
            namespace.output = output
            namespace.names = keep
            filter_named(namespace)


def build_parser(
    parser: argparse.ArgumentParser = argparse.ArgumentParser(),
) -> argparse.ArgumentParser:
    stdio_args(parser)
    log_args(parser)

    z3_interface = parser.add_mutually_exclusive_group(required=True)
    z3_interface.add_argument(
        "-p",
        "--programmatic",
        help="find unsat-core using Z3 programmatic API",
        action="store_true",
    )
    z3_interface.add_argument("-e", "--executable", help="Z3 executable to use")

    return parser


if __name__ == "__main__":
    find_unsat_core(build_parser().parse_args())
