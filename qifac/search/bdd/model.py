from dataclasses import dataclass
from typing import Iterable, Optional, Tuple, cast

import z3

from qifac.search.bdd.universe import Element, Universe, from_iterable


@dataclass(eq=True, frozen=True)
class Model:
    ref: z3.ModelRef
    universe: Universe[z3.Const]

    def eval(
        self, expression: z3.ExprRef, *, model_completion: bool = True
    ) -> Element[z3.Const]:
        evaluation = self.ref.eval(expression, model_completion=model_completion)
        return self.universe[cast(z3.Const, evaluation)]


def from_ref(model: z3.ModelRef, *, name: Optional[int] = None) -> Model:
    return Model(model, from_iterable(model.get_universe(model.get_sort(0)), name=name))


def from_refs(models: Iterable[z3.ModelRef]) -> Tuple[Model, ...]:
    return tuple(from_ref(model, name=i) for i, model in enumerate(models))
