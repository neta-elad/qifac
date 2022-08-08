from typing import Dict, Any, Iterable
from argparse import ArgumentParser, Namespace

from pysmt.smtlib.parser import SmtLibParser, Annotations

from ..pysmt_helpers import AbstractForallWalker
from .helpers import stdio_args


class AddQids(AbstractForallWalker):
    annotations: Annotations
    index: int

    def __init__(self, annotations: Annotations):
        AbstractForallWalker.__init__(self)
        self.annotations = annotations
        self.index = 0

    def fresh_qid(self, prefix: str = "k") -> str:
        self.index += 1
        return prefix + "!" + str(self.index)

    def walk_forall(self, formula: Any) -> Iterable[Any]:
        body = formula.arg(0)
        if not self.annotations.has_annotation(body, "qid"):
            self.annotations.add(body, "qid", self.fresh_qid())

        yield body


def unique_qids(args: Namespace) -> None:
    smt_parser = SmtLibParser()
    script = smt_parser.get_script(args.input)

    annotations: Annotations = script.annotations

    used_qids: Dict[str, Any] = {}
    add_qids = AddQids(annotations)

    for formula in annotations.all_annotated_formulae("qid"):
        for qid in annotations[formula]["qid"]:
            if qid in used_qids and used_qids[qid] != formula:
                annotations.remove_value(formula, "qid", qid)
                annotations.add(formula, "qid", add_qids.fresh_qid(qid))

            used_qids[qid] = formula

    add_qids.walk_script(script)

    script.serialize(args.output, daggify=False)


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)
    return parser


if __name__ == "__main__":
    unique_qids(build_parser().parse_args())
