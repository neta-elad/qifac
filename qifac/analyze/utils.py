import csv
from typing import Dict, Set, TextIO, TypeVar

from qifac.parsing.flat import Flat

T = TypeVar("T")


def sorted_by_value_len(unordered: Dict[T, Set[Flat]]) -> Dict[T, Set[Flat]]:
    return {
        k: v
        for k, v in sorted(
            unordered.items(), key=lambda item: len(item[1]), reverse=True
        )
    }


def write_dict(source: Dict[T, Set[Flat]], target: TextIO) -> None:
    writer = csv.writer(target)
    writer.writerow(["item", "amount"])
    for key, value in source.items():
        writer.writerow([str(key), len(value)])


def read_csv_as_dict(source: TextIO) -> Dict[str, int]:
    reader = csv.reader(source)
    header = True

    result: Dict[str, int] = {}

    for row in reader:
        if header:
            header = False
            continue

        key, value = row
        result[key] = int(value)

    return result
