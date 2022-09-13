import string
from dataclasses import dataclass, field
from typing import Dict, List, Mapping, Optional, Set, TextIO

from pyparsing import Opt, Suppress, Word, delimited_list, printables

IDENT_PARSER = Word(printables)("id")
QID_PARSER = Word(printables)("qid")
VAR_PARSER = Word(printables, exclude_chars="=")("var*")
TERM_PARSER = Word(string.printable, exclude_chars=",[]")("term*")
VALUE_PARSER = VAR_PARSER + Suppress("=") + TERM_PARSER

NODE_PARSER = (
    IDENT_PARSER
    + QID_PARSER
    + Suppress("[")
    + delimited_list(VALUE_PARSER, delim=",")
    + Suppress("]")
    + Opt(IDENT_PARSER("parent"))
)


Ident = str


@dataclass
class Node:
    id: Ident
    qid: str
    substitues: Mapping[str, str]
    parent: Optional[Ident]
    forest: "Forest"

    @classmethod
    def parse(cls, forest: "Forest", source: str) -> "Node":
        result = NODE_PARSER.parse_string(source, parse_all=True).as_dict()

        parent = result.get("parent")
        if parent is not None and parent == result["id"]:
            parent = None

        substitues = dict(zip(result["var"], result["term"]))
        return cls(result["id"], result["qid"], substitues, parent, forest)

    def all_substitutes(self) -> Mapping[str, str]:
        current = dict(self.substitues)

        if self.parent is not None and self.parent in self.forest.nodes:
            current |= self.parent_substitutes()

        return current

    def parent_substitutes(self) -> Mapping[str, str]:
        if self.parent is not None and self.parent in self.forest.nodes:
            return self.forest.nodes[self.parent].all_substitutes()
        else:
            return {}

    def has_cycles(self, seen: Set[Ident]) -> bool:
        if self.id in seen:
            return True

        if self.parent is None:
            return False

        seen.add(self.id)
        return self.forest.nodes[self.parent].has_cycles(seen)

    def __hash__(self) -> int:
        return hash(self.id)

    def __str__(self) -> str:
        parent = ""
        if self.parent is not None:
            parent = f" {self.parent}"

        substitutes = ",".join(f"{var}={term}" for var, term in self.substitues.items())

        return f"{self.id} {self.qid} [{substitutes}]{parent}"


@dataclass
class Forest:
    roots: Set[Ident] = field(default_factory=set)
    nodes: Dict[Ident, Node] = field(default_factory=dict)

    @classmethod
    def parse(cls, lines: List[str]) -> "Forest":
        forest = cls()
        for line in lines:
            node = Node.parse(forest, line)
            if node.parent is None:
                forest.roots.add(node.id)

            forest.nodes[node.id] = node

        return forest

    @classmethod
    def parse_file(cls, file: TextIO) -> "Forest":
        return cls.parse(file.readlines())

    def __str__(self) -> str:
        return "\n".join(str(node) for node in self.nodes.values()) + "\n"
