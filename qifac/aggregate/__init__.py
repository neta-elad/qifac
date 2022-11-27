import csv
import io
from pathlib import Path
from typing import Dict, List, TextIO, Union

from tqdm import tqdm

from ..analyze.utils import read_csv_as_dict


def aggregate_all(analysis_directory: Path, aggregate_directory: Path) -> None:
    dirs = {"diff", "unknown", "unsat"}
    files = {"per_category.csv", "per_file.csv", "per_qid.csv"}

    all_data: Dict[str, Dict[str, List[List[Union[str, int]]]]] = {}

    for directory in analysis_directory.iterdir():
        if not directory.is_dir():
            continue

        for subdir in dirs:
            all_data.setdefault(subdir, {})
            for file in files:
                all_data[subdir].setdefault(file, [])
                path = directory / subdir / file

                if not path.exists():
                    # warn?
                    continue

                with open(path, "r") as path_csv:
                    data = read_csv_as_dict(path_csv)

                    for index, (item, value) in enumerate(data.items()):
                        all_data[subdir][file].append(
                            [directory.name, item, value, index + 1]
                        )

    for subdir in dirs:
        for file in files:
            path = aggregate_directory / subdir / file
            path.parent.mkdir(parents=True, exist_ok=True)

            with open(path, "w") as path_csv:
                writer = csv.writer(path_csv)
                writer.writerow(["source", "item", "amount", "index"])
                writer.writerows(all_data[subdir][file])


def aggregate_qids(analysis_directory: Path) -> TextIO:
    buffer = io.StringIO()
    per_qid: Dict[str, int] = {}
    for file in tqdm(analysis_directory.iterdir()):
        with open(file, "r") as analysis:
            in_section = False
            for line in analysis:
                stripped = line.strip()
                if stripped == "[per-qid]":
                    in_section = True
                    continue

                if not in_section:
                    continue

                if stripped.startswith("["):
                    break

                qid, str_amount = stripped.split(" ")
                qid = qid[:-1]
                amount = int(str_amount)

                per_qid.setdefault(qid, 0)
                per_qid[qid] += amount

    for qid, amount in per_qid.items():
        print(f"{qid}: {amount}", file=buffer)

    buffer.seek(0)

    return buffer


def aggregate_categories(analysis_directory: Path) -> TextIO:
    buffer = io.StringIO()
    per_category: Dict[str, int] = {}
    for file in analysis_directory.iterdir():
        print(f"Aggregating from {file.name}")
        with open(file, "r") as analysis:
            in_section = False
            for line in analysis:
                stripped = line.strip()
                if stripped == "[per-category]":
                    in_section = True
                    continue

                if not in_section:
                    continue

                if stripped.startswith("["):
                    break

                category, str_amount = stripped.split(" ")
                category = category[:-1]
                amount = int(str_amount)

                per_category.setdefault(category, 0)
                per_category[category] += amount

    for category, amount in per_category.items():
        print(f"{category}: {amount}", file=buffer)

    buffer.seek(0)

    return buffer
