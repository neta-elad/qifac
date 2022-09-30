import io
from pathlib import Path
from typing import Dict, TextIO

from tqdm import tqdm


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
    for file in tqdm(analysis_directory.iterdir()):
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
