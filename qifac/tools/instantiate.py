from typing import Set, Dict, Any
from argparse import ArgumentParser, Namespace, FileType
import shutil
import tempfile
import io
from pathlib import Path

from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.annotations import Annotations
from pysmt.smtlib.printers import SmtPrinter
from pysmt.shortcuts import Solver, get_free_variables, Implies

from pysmt.walkers import TreeWalker, handles
from pysmt.operators import ALL_TYPES, FORALL
import z3

from .helpers import stdio_args
from ..instantiation_tree import Forest, Node


all_types_but_forall = list(ALL_TYPES)
all_types_but_forall.remove(FORALL)



class QuantifierrCollector(TreeWalker):
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
        if body in self.annotations and 'qid' in self.annotations[body]:
            for qid in self.annotations[body]['qid']:
                self.quantifiers[qid] = formula

        yield body

def instantiate(args: Namespace) -> None:
    smt_parser = SmtLibParser()
    script = smt_parser.get_script(args.input)

    check_sat, = script.filter_by_command_name('check-sat')
    script.commands.remove(check_sat)

    collector = QuantifierrCollector(script.annotations)

    for cmd in script.filter_by_command_name('assert'):
        collector.walk(cmd.args[0])

    quantifiers = collector.quantifiers
    declares = _str_dict(script.get_declared_symbols())

    forest = Forest.parse(args.instances.readlines())

    for node in forest.nodes.values():
        script.add('assert', [_instantiate(quantifiers, declares, script, node)])

    script.add_command(check_sat)

    script.serialize(args.output, daggify=False)


def _instantiate(quantifiers, declares, script, node: Node):
    quantifier = quantifiers[node.qid]

    free_variables = _str_dict(get_free_variables(quantifier.args()[0]))

    parent_substitutes = node.parent_substitutes()
    all_substitutes = node.all_substitutes()

    substitutions = {
        free_variables[var]: _build_term(declares, term)
        for var, term in all_substitutes.items()
    }

    parent_substitutions = {
        free_variables[var]: _build_term(declares, term)
        for var, term in parent_substitutes.items()
    }

    instance = quantifier.args()[0].substitute(substitutions)
    parent = quantifier.substitute(parent_substitutions)

    # Copy annotations
    # script.annotations._annotations[instance] = dict(script.annotations[quantifier.args()[0]])

    result = Implies(parent, instance)

    substitutes_string = ','.join(f'{var}={term}' for var, term in all_substitutes.items())

    script.annotations.add(result, 'named', f"{node.qid}:{substitutes_string}")

    return result


from pyparsing import Forward, Group, OneOrMore, Suppress, Word, printables

SYMBOL_PARSER = Word(printables, exclude_chars='()')
LPAR, RPAR = map(Suppress, '()')
TERM_PARSER = Forward()
TERM_PARSER << (SYMBOL_PARSER ^ Group(LPAR + SYMBOL_PARSER + OneOrMore(TERM_PARSER) + RPAR))

def _build_term(declares, term):
    parsed = TERM_PARSER.parse_string(term, parse_all=True).as_list().pop()

    return _build_parsed_term(declares, parsed)

def _build_parsed_term(declares, term):
    if len(term) == 1:
        const = term[0]
        return declares[const]

    fun, *args = term

    return declares[fun](*(_build_parsed_term(declares, arg) for arg in args))



def _str_dict(a_set):
    return {str(value): value for value in a_set}


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
