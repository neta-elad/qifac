import re
from dataclasses import dataclass
from enum import Enum, auto
from typing import Set, Tuple


class Category(Enum):
    PRELUDE = auto()
    UNKNOWN = auto()
    FUN_TYPE = auto()
    BUILTIN = auto()
    USER = auto()

    @classmethod
    def parse(cls, qid: str) -> "Category":
        if "Preludebpl" in qid:
            return Category.PRELUDE
        elif "unknown." in qid:
            return Category.UNKNOWN
        elif "funType:" in qid:
            return Category.FUN_TYPE
        elif re.search(r"\.\d+:\d+", qid) is not None:
            return Category.USER
        else:
            return Category.BUILTIN


@dataclass(eq=True, frozen=True)
class Flat:
    qid: str
    body: str
    substitutions: Tuple[str, ...]

    @classmethod
    def parse(cls, text: str) -> "Flat":
        lines = text.splitlines()

        assert len(lines) >= 2

        qid, body, *substitutions = lines

        return cls(qid, body, tuple(substitutions))

    @property
    def category(self) -> Category:
        return Category.parse(self.qid)

    def __str__(self) -> str:
        substitutions = ", ".join(self.substitutions)
        return f"{self.qid} {self.body} [{substitutions}]"


def parse_flat(flat: str) -> Set[Flat]:
    return {Flat.parse(text.strip()) for text in flat.strip().split("[end]") if text}
