from dataclasses import dataclass
from functools import cache
from pathlib import Path

import toml

METADATA_PATH = Path("metadata.toml")


@dataclass
class Metadata:
    z3: str
    z3tracer: str

    @classmethod
    def from_file(cls, path: Path = METADATA_PATH) -> "Metadata":
        return cls(**toml.loads(path.read_text()))

    @classmethod
    @cache
    def default(cls) -> "Metadata":
        return cls.from_file()
