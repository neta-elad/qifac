from dataclasses import dataclass, field, replace
from functools import cached_property, reduce
from typing import Generic, Self, Tuple, Union

from _operator import and_
from dd.autoref import Function as BDDFunction

from qifac.search.bdd.bdd import BDD
from qifac.search.bdd.universe import Element, Value


@dataclass(eq=True, frozen=True)
class Vector(Generic[Value]):
    elements: Tuple[Element[Value], ...]
    bdd: BDD = field(default=BDD.default(), kw_only=True)

    @cached_property
    def indices(self) -> Tuple[int, ...]:
        return tuple(element.index for element in self.elements)

    @cached_property
    def cube(self) -> BDDFunction:
        return reduce(
            and_,
            (self.bdd.to_expression(element.binary.cube) for element in self.elements),
        )

    @cached_property
    def argument_cube(self) -> BDDFunction:
        return reduce(
            and_,
            (
                self.bdd.to_expression(element.with_prefix(i).binary.cube)
                for i, element in enumerate(self.elements)
            ),
        )

    def with_prefix(self, prefix: Union[str, int], *, add: bool = True) -> Self:
        return replace(
            self,
            elements=tuple(
                element.with_prefix(prefix, add=add) for element in self.elements
            ),
        )
