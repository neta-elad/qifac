import re
from dataclasses import dataclass
from typing import Set, Tuple


@dataclass(eq=True, frozen=True)
class Flat:
    qid: str
    body: str
    substitutions: Tuple[str, ...]

    @staticmethod
    def clean_qid(qid: str) -> str:
        return re.sub(r"\.?broken(\d+)?", "", qid)

    @classmethod
    def parse(cls, text: str) -> "Flat":
        lines = text.splitlines()

        assert len(lines) >= 2

        qid, body, *substitutions = lines

        qid = cls.clean_qid(qid)

        return cls(qid, body, tuple(substitutions))

    def __str__(self) -> str:
        substitutions = "\n".join(self.substitutions)
        return f"{self.qid}\n{self.body}\n{substitutions}\n[end]"


def parse_flat(flat: str) -> Set[Flat]:
    return {Flat.parse(text.strip()) for text in flat.strip().split("[end]") if text}
