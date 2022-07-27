import argparse
import sys
import subprocess
import tempfile
import shutil
import io
from pathlib import Path

from pysmt.smtlib.parser import SmtLibParser


def add_proof() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input",
        nargs="?",
        type=argparse.FileType("r"),
        default=sys.stdin,
        help="Input SMTLIB file, defaults to stdin",
    )

    parser.add_argument(
        "output",
        nargs="?",
        type=argparse.FileType("w"),
        default=sys.stdout,
        help="Output SMTLIB file, defaults to stdout",
    )

    parser.add_argument(
        "-e", "--executable", required=True, help="Z3 executable to use"
    )

    parser.add_argument(
        "-t", "--tracer", required=True, help="Z3Tracer executable to use"
    )

    args = parser.parse_args()

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
        )

        assert "unsat" in result.stdout

        result = subprocess.run(
            [args.tracer, "--annotated-proof", str(log_path)],
            capture_output=True,
            text=True,
        )

        smt_parser = SmtLibParser()
        script = smt_parser.get_script_fname(str(input_path))

        for cmd in smt_parser.get_command_generator(io.StringIO(result.stdout)):
            script.commands.insert(-1, cmd)
        script.annotations = smt_parser.cache.annotations

        script.serialize(args.output, daggify=False)


if __name__ == "__main__":
    add_proof()
