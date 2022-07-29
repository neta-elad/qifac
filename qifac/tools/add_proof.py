import argparse
import sys
import subprocess
import tempfile
import shutil
import io
from pathlib import Path

from pysmt.smtlib.parser import SmtLibParser

from .helpers import stdio_args


def add_proof(args: argparse.Namespace) -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)
        input_path = dir_path / "input.smt2"

        with open(input_path, "w") as input_file:
            shutil.copyfileobj(args.input, input_file)

        log_path = dir_path / "z3.log"
        result = subprocess.run(
            [
                args.executable,
                "trace=true",
                "proof=true",
                f"trace_file_name={log_path}",
                str(input_path),
            ],
            capture_output=True,
            text=True,
        ).stdout

        assert "unsat" in result

        result = subprocess.run(
            [args.tracer, "--annotated-proof", str(log_path)],
            capture_output=True,
            text=True,
        ).stdout

        smt_parser = SmtLibParser()
        script = smt_parser.get_script_fname(str(input_path))

        for cmd in smt_parser.get_command_generator(io.StringIO(result)):
            script.commands.insert(-1, cmd)
        script.annotations = smt_parser.cache.annotations

        script.serialize(args.output, daggify=False)


def build_parser(
    parser: argparse.ArgumentParser = argparse.ArgumentParser(),
) -> argparse.ArgumentParser:
    stdio_args(parser)

    parser.add_argument(
        "-e", "--executable", required=True, help="Z3 executable to use"
    )

    parser.add_argument(
        "-t", "--tracer", required=True, help="Z3Tracer executable to use"
    )

    return parser


if __name__ == "__main__":
    add_proof(build_parser().parse_args())
