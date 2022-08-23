from typing import Dict, Any, Set, List, Optional, Tuple
from argparse import ArgumentParser, Namespace, FileType
import statistics
import sys

from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibScript
from pysmt.smtlib.printers import SmtPrinter
from pysmt.walkers import TreeWalker, handles
from pysmt.operators import ALL_TYPES
from pysmt.fnode import FNode

from ...instantiation_set import InstantiationSet, Instantiation, Term


class Tracker(TreeWalker):
    tracked: Set[FNode]

    def __init__(self, script: SmtLibScript) -> None:
        super().__init__(self)
        self.tracked = set()

        for cmd in script.filter_by_command_name("assert"):
            self.walk(cmd.args[0])

    @handles(ALL_TYPES)
    def walk_any_type(self, formula: FNode) -> Any:
        self.tracked.add(formula)
        return self.walk_skip(formula)

    def distance(self, node: FNode) -> Tuple[int, Set[FNode]]:
        if node in self.tracked:
            return 0, {node}

        if not node.args():
            return -1, set()

        max_distance = -1
        sources = set()

        for arg in node.args():
            distance, arg_sources = self.distance(arg)

            if distance == -1:
                break

            if distance > max_distance:
                max_distance = distance

            sources.update(arg_sources)

        return 1 + max_distance, sources


def run(args: Namespace) -> None:
    parser = SmtLibParser()
    script = parser.get_script(args.source)
    tracker = Tracker(script)

    instantiations: InstantiationSet = args.instantiations

    result: Dict[int, List[Tuple[FNode, Set[FNode]]]] = {}

    for instantiation in instantiations.instantiations:
        for term in instantiation.terms():
            distance, sources = tracker.distance(term)
            result.setdefault(distance, [])
            result[distance].append((term, sources))

    printer = SmtPrinter(args.output, script.annotations)

    for distance in sorted(result.keys()):
        args.output.write(f"{len(result[distance])} terms of distance {distance}\n")
        if args.distance is not None and distance >= args.distance:
            for term, sources in result[distance]:
                args.output.write("> ")
                printer.printer(term)
                for source in sources:
                    args.output.write("\n>> ")
                    printer.printer(source)
                args.output.write("\n")


def build_parser(parser: ArgumentParser) -> ArgumentParser:
    parser.add_argument(
        "-s",
        "--source",
        type=FileType("r"),
        required=True,
        help="Original SMT file for this core",
    )

    parser.add_argument(
        "-d",
        "--distance",
        nargs="?",
        type=int,
        default=None,
        const=1,
        help="Show terms of at least distance",
    )

    return parser
