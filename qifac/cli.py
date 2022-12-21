import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, Optional, TextIO

import click
from click import Context, Parameter
from tqdm import tqdm

from qifac.aggregate import aggregate_all, aggregate_categories, aggregate_qids
from qifac.model import get_model_size
from qifac.parsing.instantiation_tree import Forest
from qifac.smt.cleaner import cleanup
from qifac.typeinfo.byz3.parser import parse_smt_file

from .analyze import compare_directories as do_compare_directories
from .analyze import compare_directory_instances
from .analyze import compare_files as do_compare_files
from .analyze import compare_instances, manual, manual_compare, pair_up_files, sanity
from .cegar import cegar as do_cegar
from .core import find as do_find
from .core import find_core_with_api
from .core import instances as do_instances
from .instances import count_qids, flatten
from .instances import show as do_show
from .instances import simple_instances
from .instances.compare import compare as do_compare
from .instances.instantiate import instantiate as do_instantiate
from .search.cli import search
from .smt.cli import smt
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


run.add_command(search)


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


@batch.command(name="simple-instances")
@click.argument(
    "batch_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "output_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
def batch_simple_instances(batch_dir: Path, output_dir: Path) -> None:
    for path in tqdm(batch_dir.iterdir()):
        if not path.is_file() or not path.suffix == ".smt2":
            continue
        output_path = output_dir / path.with_suffix(".instances.txt").name
        with open(path, "r") as smt_file:
            try:
                output_path.write_text(simple_instances(smt_file))
            except:
                print(path)


run.add_command(smt)


@run.group
def core() -> None:
    pass


@core.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def find(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(do_find(smt_file), output)


@core.command
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def new(smt_file: TextIO, output: TextIO) -> None:
    shutil.copyfileobj(find_core_with_api(smt_file), output)


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


@instances.command("simple")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def do_simple(smt_file: TextIO, output: TextIO) -> None:
    output.write(simple_instances(smt_file))


@instances.command
@click.argument("instances_file", type=ForestType(), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def qids(instances_file: Forest, output: TextIO) -> None:
    for qid, count in count_qids(instances_file):
        print(f"{qid} {count}", file=output)


@instances.command(name="flatten")
@click.argument("instances_file", type=ForestType(), default=sys.stdin)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def do_flatten(instances_file: Forest, output: TextIO) -> None:
    for flat in flatten(instances_file):
        print(f"{flat}", file=output)


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


@typeinfo.command
@click.argument(
    "smt_file", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def byz3(smt_file: Path, output: TextIO) -> None:
    type_info = parse_smt_file(smt_file)

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


@analyze.command(name="manual-compare")
@click.argument(
    "unsat_instances", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_instances", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.Path(file_okay=False, exists=True, path_type=Path))
def do_manual_compare(
    unsat_instances: Path, unknown_instances: Path, output: Path
) -> None:
    manual_compare(unsat_instances, unknown_instances, output)


@analyze.command(name="manual")
@click.argument(
    "unsat_instances", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.Path(file_okay=False, exists=True, path_type=Path))
def do_manual(unsat_instances: Path, output: Path) -> None:
    manual(unsat_instances, output)


@analyze.command(name="instances")
@click.argument(
    "unsat_smt_file", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_smt_file", type=click.Path(dir_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.Path(file_okay=False, path_type=Path))
def do_compare_instances(
    unsat_smt_file: Path, unknown_smt_file: Path, output: Path
) -> None:
    compare_instances(unsat_smt_file, unknown_smt_file).write(output)


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


@analyze.command(name="instance-dirs")
@click.argument(
    "unsat_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "output_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
def do_compare_directory_instances(
    unsat_files: Path, unknown_files: Path, output_dir: Path
) -> None:
    compare_directory_instances(unsat_files, unknown_files, output_dir)


@run.command(name="pair")
@click.argument(
    "unsat_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "unknown_files", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "output_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
def do_pair_up_files(unsat_files: Path, unknown_files: Path, output_dir: Path) -> None:
    pair_up_files(unsat_files, unknown_files, output_dir)


@run.group
def aggregate() -> None:
    pass


@aggregate.command(name="qids")
@click.argument(
    "analysis_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def do_aggregate_qids(analysis_dir: Path, output: TextIO) -> None:
    shutil.copyfileobj(aggregate_qids(analysis_dir), output)


@aggregate.command(name="categories")
@click.argument(
    "analysis_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument("output", type=click.File("w"), default=sys.stdout)
def do_aggregate_categories(analysis_dir: Path, output: TextIO) -> None:
    shutil.copyfileobj(aggregate_categories(analysis_dir), output)


@aggregate.command(name="all")
@click.argument(
    "analysis_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
@click.argument(
    "aggregate_dir", type=click.Path(file_okay=False, exists=True, path_type=Path)
)
def do_aggregate(analysis_dir: Path, aggregate_dir: Path) -> None:
    aggregate_all(analysis_dir, aggregate_dir)


@run.group(name="model")
def do_model() -> None:
    pass


@do_model.command(name="size")
@click.argument("smt_file", type=click.File("r"), default=sys.stdin)
def do_model_size(smt_file: TextIO) -> None:
    low, high = get_model_size(smt_file)
    if low == high:
        print(low)
    else:
        print(f"{low}-{high}")


if __name__ == "__main__":
    run()
