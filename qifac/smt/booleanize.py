import io
from typing import Any, Dict, Set, TextIO

from pysmt.fnode import FNode
from pysmt.smtlib.annotations import Annotations
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.printers import SmtPrinter
from pysmt.utils import quote

from qifac.pysmt_helpers import AbstractForallWalker


class BooleanizeQuantifiersGetter(AbstractForallWalker):
    booleans: Set[str]
    id: int
    ids: Dict[FNode, str]

    def __init__(self, annotations: Annotations):
        AbstractForallWalker.__init__(self)
        self.annotations = annotations
        self.booleans = set()
        self.id = 0
        self.ids = {}

    def walk_forall(self, formula: FNode) -> None:
        boolean = self.booleanize(formula)
        if boolean is not None:
            self.booleans.add(boolean)

    def booleanize(self, formula: FNode) -> str:
        if formula not in self.ids:
            self.id += 1

            self.ids[formula] = quote(f"b{self.id}[{self.get_qid(formula)}]")

        return self.ids[formula]

    def get_qid(self, formula: FNode) -> str:
        formula_annotations = self.annotations[formula.arg(0)]
        if formula_annotations is not None and "qid" in formula_annotations:
            return "-".join(formula_annotations["qid"])
        else:
            return ""


class BooleanizeQuantifiersPrinter(SmtPrinter):
    getter: BooleanizeQuantifiersGetter
    booleanized: bool

    def __init__(self, stream: TextIO, getter: BooleanizeQuantifiersGetter):
        super().__init__(stream, getter.annotations)
        self.getter = getter
        self.booleanized = False

    def walk_forall(self, formula: Any) -> Any:
        self.write(self.getter.booleanize(formula))
        self.booleanized = True


def booleanize(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()
    smt_parser = SmtLibParser()
    script = smt_parser.get_script(smt_file)

    getter = BooleanizeQuantifiersGetter(script.annotations)

    getter.walk_script(script)

    for boolean in getter.booleans:
        buffer.write(f"(declare-fun {boolean} () Bool)\n")

    printer = BooleanizeQuantifiersPrinter(buffer, getter)
    for cmd in script.commands:
        if id(cmd) not in script.special_commands:
            printer.booleanized = False
            cmd.serialize(printer=printer)
            if printer.booleanized:
                buffer.write(" ;; !QUANTIFIED!")
            elif cmd.name == "assert":
                buffer.write(" ;; !QUANTIFIER-FREE!")
            buffer.write("\n")

    # script.serialize(buffer, daggify=False)

    buffer.seek(0)

    return buffer
