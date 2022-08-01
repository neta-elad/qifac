from typing import Set, Dict, Any, TypeVar, Mapping
from argparse import ArgumentParser, Namespace, FileType
import io

from pysmt.smtlib.parser import SmtLibParser, SmtLibScript
from pysmt.smtlib.annotations import Annotations
from pysmt.shortcuts import get_free_variables, Implies

from pysmt.walkers import TreeWalker, handles
from pysmt.operators import ALL_TYPES, FORALL

from .helpers import stdio_args
from ..instantiation_tree import Forest, Node


all_types_but_forall = list(ALL_TYPES)
all_types_but_forall.remove(FORALL)

Term = Any
Declare = Any


class QuantifierCollector(TreeWalker):
    quantifiers: Dict[str, Any]

    def __init__(self, annotations: Annotations):
        TreeWalker.__init__(self)
        self.annotations = annotations
        self.quantifiers = {}

    @handles(all_types_but_forall)
    def walk_error(self, formula: Any, **kwargs: Any) -> Any:
        return self.walk_skip(formula)

    def walk_forall(self, formula: Any) -> Any:
        body = formula.args()[0]
        if body in self.annotations and "qid" in self.annotations[body]:
            for qid in self.annotations[body]["qid"]:
                self.quantifiers[qid] = formula

        yield body


def instantiate(args: Namespace) -> None:
    smt_parser = SmtLibParser()
    script = smt_parser.get_script(args.input)

    (check_sat,) = script.filter_by_command_name("check-sat")
    script.commands.remove(check_sat)

    collector = QuantifierCollector(script.annotations)

    for cmd in script.filter_by_command_name("assert"):
        collector.walk(cmd.args[0])

    quantifiers = collector.quantifiers

    forest = Forest.parse(args.instances.readlines())

    for node in forest.nodes.values():
        script.add("assert", [_instantiate(smt_parser, quantifiers, script, node)])

    script.add_command(check_sat)

    script.serialize(args.output, daggify=False)


def _instantiate(
    parser: SmtLibParser,
    quantifiers: Mapping[str, Term],
    script: SmtLibScript,
    node: Node,
) -> Term:
    quantifier = quantifiers[_normalize(node.qid)]

    free_variables = _str_dict(get_free_variables(quantifier.args()[0]))

    parent_substitutes = node.parent_substitutes()
    all_substitutes = node.all_substitutes()

    try:
        substitutions = {
            free_variables[_normalize(var)]: _build_term(parser, term)
            for var, term in all_substitutes.items()
        }
    except KeyError as e:
        print(free_variables)
        print(all_substitutes)
        print(e)
        # print(node)
        exit(-1)

    parent_substitutions = {
        free_variables[_normalize(var)]: _build_term(parser, term)
        for var, term in parent_substitutes.items()
    }

    instance = quantifier.args()[0].substitute(substitutions)
    parent = quantifier.substitute(parent_substitutions)

    # if quantifier != parent:
    #     copy_qid(script.annotations, quantifier, parent)

    result = Implies(parent, instance)

    substitutes_string = ",".join(
        f"{var}={term}" for var, term in all_substitutes.items()
    )

    script.annotations.add(result, "named", f"{node.qid}[{substitutes_string}]")

    return result

def _copy_qid(annotations: Annotations, source: Term, target: Term) -> None:
    source_annotations = annotations[source.args()[0]]
    if source_annotations is not None and 'qid' in source_annotations:
        qids = source_annotations['qid']

        for qid in qids:
            annotations.add(target.args()[0], 'qid', qid)


def _build_term(parser: SmtLibParser, term: str) -> Term:
    buffer = io.StringIO(f"(assert (= {term} {term}))")

    for cmd in parser.get_command_generator(buffer):
        return cmd.args[0].args()[0]


def _normalize(symbol: str) -> str:
    if (symbol.startswith('|') and symbol.endswith('|')) or (symbol.startswith("'") and symbol.endswith("'")):
        return symbol[1:-1]
    return symbol


T = TypeVar("T")


def _str_dict(a_set: Set[T]) -> Mapping[str, T]:
    return {_normalize(str(value)): value for value in a_set}


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    stdio_args(parser)

    parser.add_argument(
        "-i",
        "--instances",
        required=True,
        type=FileType("r"),
        help="Instantiations file",
    )

    return parser


if __name__ == "__main__":
    instantiate(build_parser().parse_args())
