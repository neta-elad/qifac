import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, List, Optional, TextIO

import click
from click import Context, Parameter
from tqdm import tqdm

from qifac.parsing.instantiation_tree import Forest

from .analyze import compare_directories as do_compare_directories
from .analyze import compare_files as do_compare_files
from .analyze import compare_instances, sanity
from .cegar import cegar as do_cegar
from .core import find as do_find
from .core import instances as do_instances
from .instances import count_qids
from .instances import show as do_show
from .instances.compare import compare as do_compare
from .instances.instantiate import instantiate as do_instantiate
from .smt import dedup as do_dedup
from .smt import filter_names as do_filter_names
from .smt import name as do_name
from .smt import pysmt_prettify
from .smt import skolemize as do_skolemize
from .smt import uglify as do_uglify
from .smt import unname as do_unname
from .smt import z3_prettify
from .smt.booleanize import booleanize as do_booleanize
from .smt.cleaner import clean_errors, cleanup
from .typeinfo.parser import parse_script
from .utils import TimeoutException, time_limit
from .z3_utils import run_z3 as do_run_z3


class ForestType(click.ParamType):
    file: click.File

    def __init__(self) -> None:
        self.file = click.File("r")

    def convert(
        self, value: Any, param: Optional[Parameter], ctx: Optional[Context]
    ) -> Forest:
        file = self.file.convert(value, param, ctx)

        return Forest.parse_file(file)


@click.group
def run() -> None:
    pass


@run.command(name="z3")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
def run_z3(smt_file: TextIO) -> None:
    print(do_run_z3(smt_file))


@run.group
def batch() -> None:
    pass


@batch.command(name="partition")
@click.argument(
    "batch_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unsat_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
def batch_partition(batch_dir: Path, unsat_dir: Path, unknown_dir: Path) -> None:
    for file in tqdm(batch_dir.iterdir()):
        if not file.is_file() or file.suffix != ".smt":
            continue

        with open(file, "r") as text_io:
            cleaned = cleanup(text_io)
            if "unknown" in do_run_z3(cleaned):
                cleaned.seek(0)
                with open(
                    unknown_dir / file.with_suffix(".smt2").name, "w"
                ) as unknown_file:
                    shutil.copyfileobj(cleaned, unknown_file)
            else:
                cleaned.seek(0)
                with open(
                    unsat_dir / file.with_suffix(".smt2").name, "w"
                ) as unknown_file:
                    shutil.copyfileobj(cleaned, unknown_file)


@batch.command(name="instances")
@click.argument(
    "batch_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
def batch_instances(batch_dir: Path) -> None:
    for path in batch_dir.iterdir():
        print(f"Trying {path.name}")
        try:
            with time_limit(60 * 5):
                subprocess.run(
                    ["qifac", "core", "instances", str(path), str(path.name)],
                    capture_output=True,
                    text=True,
                )
        except TimeoutException:
            print("Timed out!")
        except Exception as e:
            print(f"Error {e}")


@run.group
def smt() -> None:
    pass


@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def uglify(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_uglify(smt_file), output)


@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def prettify(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(pysmt_prettify(smt_file), output)


@smt.command("z3-prettify")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def do_z3_prettify(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(z3_prettify(smt_file), output)


@smt.command(name="cleanup")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def do_cleanup(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(cleanup(smt_file), output)


@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def dedup(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_dedup(smt_file), output)


@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def unname(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_unname(smt_file), output)


@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def clean(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(clean_errors(smt_file), output)


@smt.command(name="bool")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def booleanize(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_booleanize(smt_file), output)


@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def name(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_name(smt_file), output)


@smt.command(name="filter")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
@click.option("--names", "-n", multiple=True)
def filter_names(smt_file: TextIO, output: TextIO, names: List[str]) -> None:
    shutil.copyfileobj(do_filter_names(smt_file, names), output)


@smt.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def skolemize(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_skolemize(smt_file), output)


@run.group
def core() -> None:
    pass


@core.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def find(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_find(smt_file), output)


@core.command(name="instances")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def core_instances(smt_file: TextIO, output: TextIO) -> None:
    output.write(str(do_instances(smt_file)))


@run.group
def instances() -> None:
    pass


@instances.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
@click.option("--proof/--no-proof", default=True)
def show(smt_file: TextIO, output: TextIO, proof: bool) -> None:
    output.write(str(do_show(smt_file, with_proof=proof)))


@instances.command
@click.argument("instances_file", type=ForestType(), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def qids(instances_file: Forest, output: TextIO) -> None:
    for qid, count in count_qids(instances_file):
        print(f"{qid} {count}", file=output)


@instances.command
@click.argument("unsat_file", type=ForestType())
@click.argument("unknown_file", type=ForestType())
@click.argument("output", type=click.File("w"), default=sys.stdout)
def compare(unsat_file: Forest, unknown_file: Forest, output: TextIO) -> None:
    result = do_compare(unsat_file, unknown_file)
    for node in result:
        print(f"{node}", file=output)


@instances.command
@click.argument("smt_file", type=click.File("r"))
@click.argument("instances_file", type=ForestType())
@click.argument("output", type=click.File("w"), default=sys.stdout)
def instantiate(smt_file: TextIO, instances_file: Forest, output: TextIO) -> None:
    shutil.copyfileobj(do_instantiate(smt_file, instances_file), output)


@instances.command
@click.argument("smt_file", type=click.File("r"))
@click.argument("output", type=click.File("w"), default=sys.stdout)
@click.option("--proof/--no-proof", default=True)
def auto(smt_file: TextIO, output: TextIO, proof: bool) -> None:
    forest = do_show(smt_file, with_proof=proof)
    smt_file.seek(0)
    shutil.copyfileobj(do_instantiate(smt_file, forest), output)


@run.group
def typeinfo() -> None:
    pass


@typeinfo.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def grounds(smt_file: TextIO, output: TextIO) -> None:
    type_info = parse_script(smt_file)

    for ground in type_info.grounds:
        kind = type_info.get_type(ground)

        if kind is not None:
            output.write(f"{ground}: {kind}\n")


@run.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def cegar(smt_file: TextIO, output: TextIO) -> None:
    do_cegar(smt_file)

    # for assertion in asserts:
    #     output.write(f"{assertion.sexpr()}\n")


@run.group
def analyze() -> None:
    pass


@analyze.command(name="compare")
@click.argument("unsat_smt_file", type=click.File("r"))
@click.argument("unknown_smt_file", type=click.File("r"))
@click.argument("output", type=click.File("w"), default=sys.stdout)
def compare_files(
    unsat_smt_file: TextIO, unknown_smt_file: TextIO, output: TextIO
) -> None:
    shutil.copyfileobj(do_compare_files(unsat_smt_file, unknown_smt_file), output)


@analyze.command(name="instances")
@click.argument("unsat_smt_file", type=click.File("r"))
@click.argument("unknown_smt_file", type=click.File("r"))
@click.argument("output", type=click.File("w"), default=sys.stdout)
def do_compare_instances(
    unsat_smt_file: TextIO, unknown_smt_file: TextIO, output: TextIO
) -> None:
    shutil.copyfileobj(compare_instances(unsat_smt_file, unknown_smt_file), output)


@analyze.command(name="sanity")
@click.argument("unsat_smt_file", type=click.File("r"))
def do_sanity(unsat_smt_file: TextIO) -> None:
    sanity(unsat_smt_file)


@analyze.command(name="dirs")
@click.argument(
    "unsat_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "output_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def compare_directories(
    unsat_files: Path, unknown_files: Path, output_dir: Path, output: TextIO
) -> None:
    shutil.copyfileobj(
        do_compare_directories(unsat_files, unknown_files, output_dir), output
    )


if __name__ == "__main__":
    run()
