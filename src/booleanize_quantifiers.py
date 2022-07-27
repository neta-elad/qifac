from typing import Optional, TextIO, List, Set, Any, Mapping, cast
import z3
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibCommand
from pysmt.smtlib.printers import SmtPrinter
from pysmt.walkers import TreeWalker, handles
from pysmt.utils import quote
from pysmt.operators import ALL_TYPES, FORALL

all_types_but_forall = list(ALL_TYPES)
all_types_but_forall.remove(FORALL)

import argparse
import io
import sys

Annotations = Mapping[Any, Mapping[str, List[str]]]

booleans = {}
boolean_id = 0
def booleanize_quantifier(formula: Any) -> str:
    if formula not in booleans:
        global boolean_id
        boolean_id += 1
        booleans[formula] = str(f"b{boolean_id}")

    return booleans[formula]
    # formula_annotations = annotations[formula.arg(0)]

    # if formula_annotations is not None and "qid" in formula_annotations:
    #     return cast(str, quote("-".join(formula_annotations["qid"])))
    # else:
    #     return None


class BooleanizeQuantifiersGetter(TreeWalker):
    booleans: Set[str]

    def __init__(self, annotations: Annotations):
        TreeWalker.__init__(self)
        self.annotations = annotations
        self.booleans = set()

    @handles(all_types_but_forall)
    def walk_error(self, formula: Any, **kwargs: Any) -> Any:
        return self.walk_skip(formula)

    def walk_forall(self, formula: Any) -> Any:
        boolean = booleanize_quantifier(formula)
        if boolean is not None:
            self.booleans.add(boolean)


class BooleanizeQuantifiersPrinter(SmtPrinter):
    def __init__(self, stream: TextIO, annotations: Annotations):
        SmtPrinter.__init__(self, stream, annotations)

    def walk_forall(self, formula: Any) -> Any:
        boolean = booleanize_quantifier(formula)
        if boolean is None:
            SmtPrinter.walk_forall(self, formula)
        else:
            self.write(boolean)


def booleanize_quantifiers() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input",
        nargs="?",
        type=argparse.FileType("r"),
        default=sys.stdin,
        help="Input SMTLIB file, defaults to stdin",
    )

    parser.add_argument(
        "output",
        nargs="?",
        type=argparse.FileType("w"),
        default=sys.stdout,
        help="Output SMTLIB file, defaults to stdout",
    )

    args = parser.parse_args()

    smt_file = args.input

    smt_parser = SmtLibParser()
    script = smt_parser.get_script(smt_file)

    printer = BooleanizeQuantifiersPrinter(args.output, annotations=script.annotations)
    getter = BooleanizeQuantifiersGetter(script.annotations)

    for cmd in script.filter_by_command_name("assert"):
        getter.walk(cmd.args[0])

    for boolean in getter.booleans:
        args.output.write(f"(declare-fun {boolean} () Bool)\n")

    for cmd in script.commands:
        cmd.serialize(printer=printer)
        args.output.write("\n")


if __name__ == "__main__":
    booleanize_quantifiers()
