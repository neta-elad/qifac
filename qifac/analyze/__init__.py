import shutil
import subprocess
import tempfile
from io import StringIO
from pathlib import Path
from typing import TextIO

from ..core import instances as core_instances
from ..instances import show as all_instances
from ..instances import simple
from ..instances.compare import compare


def sanity(unsat_file: TextIO) -> None:
    def check_path(path: Path) -> None:
        result = subprocess.run(
            ["qifac", "z3", str(path)], capture_output=True, text=True
        )

        if len(result.stdout) == 0:
            print(f"serious problem with {path.name}: {result.stderr}")
            return

        if "unsat" in result.stdout.splitlines()[0]:
            print(f"{path.name} is unsat")
        else:
            print(f"problem with {path.name}: {result.stdout}")

    with tempfile.TemporaryDirectory() as tmpdir:
        dir_path = Path(tmpdir)
        input_path = dir_path / "input.smt2"
        with open(input_path, "w") as input_file:
            shutil.copyfileobj(unsat_file, input_file)

        check_path(input_path)

        skolemized_path = dir_path / "skolemized.smt2"
        subprocess.run(
            ["qifac", "smt", "skolemize", str(input_path), str(skolemized_path)],
            capture_output=True,
            text=True,
        )
        check_path(skolemized_path)

        pretty_path = dir_path / "pretty.smt2"
        subprocess.run(
            ["qifac", "smt", "prettify", str(skolemized_path), str(pretty_path)],
            capture_output=True,
            text=True,
        )
        check_path(pretty_path)

        dedup_path = dir_path / "dedup.smt2"
        subprocess.run(
            ["qifac", "smt", "dedup", str(pretty_path), str(dedup_path)],
            capture_output=True,
            text=True,
        )
        check_path(dedup_path)

        named_path = dir_path / "named.smt2"
        subprocess.run(
            ["qifac", "smt", "name", str(dedup_path), str(named_path)],
            capture_output=True,
            text=True,
        )
        check_path(named_path)

        core_path = dir_path / "core.smt2"
        subprocess.run(
            ["qifac", "core", "find", str(dedup_path), str(core_path)],
            capture_output=True,
            text=True,
        )
        check_path(core_path)


def compare_files(unsat_file: TextIO, unknown_file: TextIO) -> TextIO:
    buffer = StringIO()

    unsat_forest = core_instances(unsat_file)
    unknown_forest = all_instances(unknown_file, with_proof=False)

    missing = compare(unsat_forest, unknown_forest)

    print(
        f"Missing {int(100*len(missing)/len(unsat_forest.nodes))}% of instantiations",
        file=buffer,
    )
    for node in missing:
        print(f"> {unsat_forest.nodes[node]}", file=buffer)

    buffer.seek(0)

    return buffer


def compare_directories(
    unsat_files: Path, unknown_files: Path, results: Path
) -> TextIO:
    buffer = StringIO()

    for file in unsat_files.iterdir():
        if file.suffix != ".smt2":
            continue

        unknown_path = unknown_files / file.name

        if not unknown_path.is_file():
            print(f"Missing file {file.name} in unknowns directory")
            continue

        output = results / file.with_suffix(".txt").name

        print(f"Analyzing {file.name}...")

        result = subprocess.run(
            ["qifac", "analyze", "compare", str(file), str(unknown_path), str(output)],
            capture_output=True,
            text=True,
        )

        print(f"> {result.stdout}")
        print(f"> {result.stderr}")

    buffer.seek(0)

    return buffer


def compare_instances(unsat_file: TextIO, unknown_file: TextIO) -> TextIO:
    buffer = StringIO()

    unsat = simple(unsat_file)
    unknown = simple(unknown_file)

    missing = unsat - unknown

    print("[summary]", file=buffer)

    print(
        f"Missing {int(100*len(missing)/len(unsat))}% of instantiations",
        file=buffer,
    )

    per_qid = {}
    per_category = {}

    for flat in missing:
        per_qid.setdefault(flat.qid, 0)
        per_qid[flat.qid] += 1
        per_category.setdefault(flat.category, 0)
        per_category[flat.category] += 1

    print("[per-qid]", file=buffer)
    for qid, amount in per_qid.items():
        print(f"{qid}: {amount}", file=buffer)

    print("[per-category]", file=buffer)
    for category, amount in per_category.items():
        print(f"{category}: {amount}", file=buffer)

    print("[missing]", file=buffer)
    for flat in missing:
        print(f"{flat}", file=buffer)

    buffer.seek(0)

    return buffer
