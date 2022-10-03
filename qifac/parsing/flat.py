from dataclasses import dataclass
from typing import Set, Tuple


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

    def __str__(self) -> str:
        substitutions = ", ".join(self.substitutions)
        return f"{self.qid} {self.body} [{substitutions}]"


def parse_flat(flat: str) -> Set[Flat]:
    return {Flat.parse(text.strip()) for text in flat.strip().split("[end]") if text}
