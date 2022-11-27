import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from functools import cached_property
from io import StringIO
from pathlib import Path
from typing import Dict, Set, TextIO

from tqdm import tqdm

from ..core import instances as core_instances
from ..instances import show as all_instances
from ..instances import simple
from ..instances.compare import compare
from ..parsing.flat import Flat, parse_flat
from .categorize import Category
from .utils import sorted_by_value_len, write_dict


@dataclass
class Analysis:
    filename: str
    instances: Set[Flat]

    @cached_property
    def per_qid(self) -> Dict[str, Set[Flat]]:
        unordered: Dict[str, Set[Flat]] = {}
        for flat in self.instances:
            unordered.setdefault(flat.qid, set())
            unordered[flat.qid].add(flat)

        return sorted_by_value_len(unordered)

    @cached_property
    def per_file(self) -> Dict[str, Set[Flat]]:
        unordered: Dict[str, Set[Flat]] = {}

        for flat in self.instances:
            filename = Category.parse_filename(flat.qid)
            unordered.setdefault(filename, set())
            unordered[filename].add(flat)

        return sorted_by_value_len(unordered)

    @cached_property
    def per_category(self) -> Dict[Category, Set[Flat]]:
        unordered: Dict[Category, Set[Flat]] = {}

        for flat in self.instances:
            category = Category.parse(flat.qid, self.filename)
            unordered.setdefault(category, set())
            unordered[category].add(flat)

        return sorted_by_value_len(unordered)

    def write(self, path: Path) -> None:
        path.mkdir(parents=True, exist_ok=True)

        with open(path / "instances.txt", "w") as instances:
            for instance in self.instances:
                instances.write(f"{instance}\n")

        with open(path / "per_qid.csv", "w") as per_qid:
            write_dict(self.per_qid, per_qid)

        with open(path / "per_file.csv", "w") as per_file:
            write_dict(self.per_file, per_file)

        with open(path / "per_category.csv", "w") as per_category:
            write_dict(self.per_category, per_category)


@dataclass
class Comparison:
    unsat_analysis: Analysis
    unknown_analysis: Analysis

    @cached_property
    def diff_analysis(self) -> Analysis:
        return Analysis(
            self.unsat_analysis.filename,
            self.unsat_analysis.instances - self.unknown_analysis.instances,
        )

    @cached_property
    def missing_ratio(self) -> float:
        return len(self.diff_analysis.instances) / len(self.unsat_analysis.instances)

    def write(self, parent: Path) -> None:
        self.unsat_analysis.write(parent / "unsat")
        self.unknown_analysis.write(parent / "unknown")
        self.diff_analysis.write(parent / "diff")
        with open(parent / f"{self.unknown_analysis.filename}-ratio.txt", "w") as ratio:
            ratio.write(f"{self.missing_ratio}\n")


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


def compare_instances(unsat_file: Path, unknown_file: Path) -> Comparison:
    StringIO()

    with open(unsat_file, "r") as unsat_textio:
        unsat = simple(unsat_textio)

    with open(unknown_file, "r") as unknown_textio:
        unknown = simple(unknown_textio)

    return Comparison(
        Analysis(unsat_file.stem, unsat), Analysis(unknown_file.stem, unknown)
    )


def manual_compare(
    unsat_instances: Path, unknown_instances: Path, output: Path
) -> None:
    unsat = parse_flat(unsat_instances.read_text())
    unknown = parse_flat(unknown_instances.read_text())

    Comparison(
        Analysis(unsat_instances.stem, unsat), Analysis(unknown_instances.stem, unknown)
    ).write(output)


def manual(unsat_instances: Path, output: Path) -> None:
    unsat = parse_flat(unsat_instances.read_text())

    Analysis(unsat_instances.stem, unsat).write(output / "manual")


def compare_directory_instances(
    unsat_dir: Path, unknown_dir: Path, analysis_dir: Path
) -> None:
    for file in tqdm(unknown_dir.iterdir()):
        if not file.is_file() or not file.suffix == ".smt2":
            continue

        matching = matching_file(file, unsat_dir)

        if not matching.is_file() or not matching.suffix == ".smt2":
            continue

        analysis_path = analysis_dir / file.stem

        compare_instances(matching, file).write(analysis_path)


def pair_up_files(unsat_dir: Path, unknown_dir: Path, output_dir: Path) -> None:
    for i, file in enumerate(tqdm(unknown_dir.iterdir())):
        if not file.is_file() or not file.suffix == ".smt2":
            continue

        matching = matching_file(file, unsat_dir)

        if not matching.is_file() or not matching.suffix == ".smt2":
            continue

        output_specific_dir = output_dir / f"pair-{i}"
        output_specific_dir.mkdir(parents=True, exist_ok=True)

        shutil.copy2(file, output_specific_dir / file.name)
        shutil.copy2(matching, output_specific_dir / matching.name)


def matching_file(unknown: Path, unsat_directory: Path) -> Path:
    return unsat_directory / re.sub(r"\.?broken(\d+)?", "", unknown.name)
