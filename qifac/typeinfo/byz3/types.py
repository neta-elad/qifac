from dataclasses import dataclass
from typing import Dict, Optional, Set

import z3

from qifac.tools.helpers import normalize

from .utils import check_ground_and_update

T_T = z3.DeclareSort("T@T")
T_U = z3.DeclareSort("T@U")
TYPE_FUN = z3.Function("type", T_U, T_T)


@dataclass
class TypeInfo:
    grounds: Set[z3.ExprRef]
    z3_funs: Dict[str, z3.FuncDeclRef]
    fun_types: Dict[str, z3.ExprRef]
    solver: z3.Solver

    def is_ground(self, term: z3.ExprRef) -> bool:
        return check_ground_and_update(term, self.grounds)

    def to_z3(self, term: z3.ExprRef) -> z3.ExprRef:
        return term

    def get_type(self, term: z3.ExprRef) -> Optional[z3.ExprRef]:
        if term.sort() != T_U:
            return None

        const = term

        if z3.is_app(term):
            fun = normalize(term.decl().name())

            if fun in self.fun_types:
                kind = self.to_z3(self.fun_types[fun])

                return kind

        for type_term in self.grounds:
            if type_term.sort() != T_T:
                continue

            kind = self.to_z3(type_term)
            formula = z3.Not(TYPE_FUN(const) == kind)

            if self.solver.check(formula) == z3.unsat:
                return kind

        return None
