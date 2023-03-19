from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Set, TextIO, Tuple

from pysmt.smtlib.parser import SmtLibParser

from qifac.pysmt_helpers import parse_term

Term = Any


@dataclass(eq=True, frozen=True)
class Instantiation:
    name: str
    qid: str
    assignment: Tuple[Tuple[str, Term], ...]

    @classmethod
    def parse(cls, source: TextIO, parser: SmtLibParser) -> Optional["Instantiation"]:
        name = None
        qid = None
        tuples: List[Tuple[str, Term]] = []
        var = None
        while (line := source.readline()) != "":
            stripped = line.strip()

            if not stripped.startswith(";;! "):
                continue
            else:
                stripped = stripped[4:]

            if stripped == "###":
                break

            if name is None:
                name = stripped
            elif qid is None:
                qid = stripped
            elif var is None:
                var = stripped
            else:
                term = parse_term(parser, stripped)
                tuples.append((var, term))
                var = None
        else:
            return None

        if name is None or qid is None:
            return None

        return cls(name, qid, tuple(tuples))

    def terms(self) -> Iterable[Term]:
        for _var, term in self.assignment:
            yield term

    def as_dict(self) -> Dict[str, Term]:
        return {var: term for var, term in self.assignment}


@dataclass
class InstantiationSet:
    instantiations: Set[Instantiation]

    @classmethod
    def parse(cls, source: TextIO, parser: SmtLibParser) -> "InstantiationSet":
        instantiations = set()
        while (instantiation := Instantiation.parse(source, parser)) is not None:
            instantiations.add(instantiation)

        return cls(instantiations)

    def by_qid(self) -> Dict[str, Set[Instantiation]]:
        result: Dict[str, Set[Instantiation]] = {}
        for instantiation in self.instantiations:
            result.setdefault(instantiation.qid, set()).add(instantiation)

        return result

    def terms(self) -> Iterable[Term]:
        for instantiation in self.instantiations:
            yield from instantiation.terms()
