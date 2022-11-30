from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import List

import toml

from qifac.utils import find_in_parent

METADATA_PATH = Path("metadata.toml")


@dataclass
class Metadata:
    z3: str
    z3tracer: str
    lib_qids: List[str]

    @classmethod
    def from_file(cls, path: Path = METADATA_PATH) -> "Metadata":
        return cls(**toml.loads(find_in_parent(path).read_text()))

    @classmethod
    @cache
    def default(cls) -> "Metadata":
        return cls.from_file()
