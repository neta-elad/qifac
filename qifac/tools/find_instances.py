from argparse import ArgumentParser, Namespace, FileType
import subprocess
import tempfile
import shutil
from pathlib import Path

from .helpers import stdio_args


def run(args: Namespace) -> None:
    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)
        input_path = dir_path / "input.smt2"

        with open(input_path, "w") as input_file:
            shutil.copyfileobj(args.input, input_file)

        log_path = dir_path / "z3.log"
        subprocess.run(
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

        instances_path = dir_path / "instances.txt"

        subprocess.run(
            [
                args.tracer,
                "--skip-z3-version-check",
                "--instantiation-tree",
                str(instances_path),
                str(log_path),
            ],
            capture_output=True,
            text=True,
        )

        with open(instances_path, "r") as instances:
            shutil.copyfileobj(instances, args.output)


def build_parser(
    parser: ArgumentParser = ArgumentParser(),
) -> ArgumentParser:
    stdio_args(parser)

    parser.add_argument(
        "-e", "--executable", required=True, help="Z3 executable to use"
    )

    parser.add_argument(
        "-t", "--tracer", required=True, help="Z3Tracer executable to use"
    )

    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
