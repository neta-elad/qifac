import sys
from argparse import ArgumentParser, FileType, Namespace
from dataclasses import dataclass, field
from typing import Dict, Optional, Tuple

from qifac.parsing.instantiation_tree import Forest, Ident


@dataclass
class Comparator:
    left: Forest
    right: Forest
    comparisons: Dict[Tuple[Ident, Ident], bool] = field(default_factory=dict)

    def are_equal(
        self, left: Optional[Ident], right: Optional[Ident]
    ) -> Optional[bool]:
        if left is None and right is None:
            return True

        if left is None or right is None:
            return False

        return self.comparisons.get((left, right))

    def compare(self, left: Optional[Ident], right: Optional[Ident]) -> bool:
        comparison = self.are_equal(left, right)
        if comparison is not None:
            return comparison

        assert left is not None
        assert right is not None

        left_node = self.left.nodes[left]
        right_node = self.right.nodes[right]

        if not self.compare(left_node.parent, right_node.parent):
            return self.set_compare(left, right, False)

        if left_node.qid != right_node.qid:
            return self.set_compare(left, right, False)

        if len(left_node.substitues) != len(right_node.substitues):
            # weird?
            return self.set_compare(left, right, False)

        for (key, left_value) in left_node.substitues.items():
            right_value = right_node.substitues.get(key)
            if left_value != right_value:
                return self.set_compare(left, right, False)

        # if left_node.qid == '|funType:bool_2_U|' and right_node.qid == '|funType:bool_2_U|':
        #     if left_node.substitues.get('arg0@@4', '') == 'true':
        #         print('!')
        #         print(right_node.substitues)
        #         print('!')

        return self.set_compare(left, right, True)

    def set_compare(self, left: Ident, right: Ident, comparison: bool) -> bool:
        self.comparisons[(left, right)] = comparison
        self.comparisons[(right, left)] = comparison

        return comparison


def run(args: Namespace) -> None:
    left_forest = Forest.parse(args.left.readlines())
    right_forest = Forest.parse(args.right.readlines())

    compare = Comparator(left_forest, right_forest)

    for left in left_forest.nodes:
        found = False
        for right in right_forest.nodes:
            if compare.compare(left, right):
                found = True
                break

        if not found:
            print(f"{left}")


def build_parser(parser: ArgumentParser = ArgumentParser()) -> ArgumentParser:
    parser.add_argument(
        "left",
        type=FileType("r"),
        help="Input left to compare",
    )

    parser.add_argument(
        "right",
        nargs="?",
        type=FileType("r"),
        default=sys.stdin,
        help="Input right to compare",
    )

    return parser


if __name__ == "__main__":
    run(build_parser().parse_args())
