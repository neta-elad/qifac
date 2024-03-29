import argparse
from typing import Any, List, Mapping, Set, TextIO, cast

from pysmt.operators import ALL_TYPES, FORALL
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.printers import SmtPrinter
from pysmt.utils import quote
from pysmt.walkers import TreeWalker, handles

from .helpers import stdio_args

all_types_but_forall = list(ALL_TYPES)
all_types_but_forall.remove(FORALL)


Annotations = Mapping[Any, Mapping[str, List[str]]]

booleans = {}
boolean_id = 0


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
        boolean = _booleanize_quantifier(formula, self.annotations)
        if boolean is not None:
            self.booleans.add(boolean)


class BooleanizeQuantifiersPrinter(SmtPrinter):
    def __init__(self, stream: TextIO, annotations: Annotations):
        SmtPrinter.__init__(self, stream, annotations)

    def walk_forall(self, formula: Any) -> Any:
        boolean = _booleanize_quantifier(formula, self.annotations)
        if boolean is None:
            SmtPrinter.walk_forall(self, formula)
        else:
            self.write(boolean)


def booleanize_quantifiers(args: argparse.Namespace) -> None:
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
        if id(cmd) not in script.special_commands:
            cmd.serialize(printer=printer)
            args.output.write("\n")


def _booleanize_quantifier(formula: Any, annotations: Annotations) -> str:
    if formula not in booleans:
        global boolean_id
        boolean_id += 1

        booleans[formula] = quote(f"b{boolean_id}[{_get_qid(formula, annotations)}]")

    return booleans[formula]


def _get_qid(formula: Any, annotations: Annotations) -> str:
    formula_annotations = annotations[formula.arg(0)]
    if formula_annotations is not None and "qid" in formula_annotations:
        return cast(str, "-".join(formula_annotations["qid"]))
    else:
        return ""


def build_parser(
    parser: argparse.ArgumentParser = argparse.ArgumentParser(),
) -> argparse.ArgumentParser:
    return stdio_args(parser)


if __name__ == "__main__":
    booleanize_quantifiers(build_parser().parse_args())
