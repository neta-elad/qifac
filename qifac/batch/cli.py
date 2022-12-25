import shutil
import subprocess
from pathlib import Path

import click
from tqdm import tqdm

from ..instances import simple_instances
from ..smt.cleaner import cleanup
from ..utils import TimeoutException, time_limit
from ..z3_utils import run_z3


@click.group
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
            if "unknown" in run_z3(cleaned):
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
