from dataclasses import dataclass, field
from typing import Dict, Optional, Set, Tuple

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

        for key, left_value in left_node.substitues.items():
            right_value = right_node.substitues.get(key)
            if left_value != right_value:
                return self.set_compare(left, right, False)

        return self.set_compare(left, right, True)

    def set_compare(self, left: Ident, right: Ident, comparison: bool) -> bool:
        self.comparisons[(left, right)] = comparison
        self.comparisons[(right, left)] = comparison

        return comparison


def compare(unsat_forest: Forest, unknown_file: Forest) -> Set[str]:
    result = set()

    comparator = Comparator(unsat_forest, unknown_file)

    for unsat_node in unsat_forest.nodes:
        found = False
        for unknown_node in unknown_file.nodes:
            if comparator.compare(unsat_node, unknown_node):
                found = True
                break

        if not found:
            result.add(unsat_node)

    return result
