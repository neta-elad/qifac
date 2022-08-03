from argparse import ArgumentParser, Namespace
import subprocess
import tempfile
import shutil
from pathlib import Path

from .helpers import stdio_args
from .instantiate import instantiate


def add_proof(args: Namespace) -> None:
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

        shutil.copyfile(log_path, "/tmp/z3.log")
        shutil.copyfile(instances_path, "/tmp/instances.txt")

        with open(input_path) as input_file, open(instances_path, "r") as instances:
            instantiate_namespace = Namespace()
            instantiate_namespace.input = input_file
            instantiate_namespace.instances = instances
            instantiate_namespace.output = args.output
            instantiate(instantiate_namespace)


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
    add_proof(build_parser().parse_args())
