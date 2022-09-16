from dataclasses import dataclass, field
from typing import List, Set

import z3


@dataclass
class Hitter:
    elements: Set[z3.BoolRef]
    sets: List[Set[z3.BoolRef]] = field(default_factory=list)
    optimizer: z3.Optimize = field(default_factory=z3.Optimize)

    def __post_init__(self) -> None:
        for element in self.elements:
            self.optimizer.add_soft(z3.Not(element))

    def add(self, the_set: Set[z3.BoolRef]) -> None:
        self.sets.append(the_set)
        self.optimizer.add(z3.Or(*(element for element in the_set)))

    def minimum(self) -> Set[z3.BoolRef]:
        assert self.optimizer.check() == z3.sat
        model = self.optimizer.model()

        minimum = set()

        for element in self.elements:
            if z3.is_true(model.eval(element)):
                minimum.add(element)

        return minimum
