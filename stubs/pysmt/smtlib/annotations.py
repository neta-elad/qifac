from typing import Any, Dict

from ..fnode import FNode


class Annotations:
    def add(self, formula: FNode, annotation: str, value: Any = None) -> None:
        ...

    def remove_annotation(self, formula: FNode, annotation: str) -> None:
        ...

    def has_annotation(
        self, formula: FNode, annotation: str, value: Any = None
    ) -> bool:
        ...

    def __getitem__(self, item: FNode) -> Dict[str, Any]:
        ...

    def __contains__(self, formula: FNode) -> bool:
        ...
