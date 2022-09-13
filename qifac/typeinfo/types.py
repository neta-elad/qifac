from dataclasses import dataclass
from typing import Dict, Optional, Set

import z3
from pysmt.fnode import FNode
from pysmt.operators import FUNCTION

from qifac.tools.helpers import normalize
from qifac.typeinfo.utils import check_ground_and_update, to_z3_sort

T_T = z3.DeclareSort("T@T")
T_U = z3.DeclareSort("T@U")
TYPE_FUN = z3.Function("type", T_U, T_T)


@dataclass
class TypeInfo:
    grounds: Set[FNode]
    z3_funs: Dict[str, z3.FuncDeclRef]
    fun_types: Dict[str, FNode]
    solver: z3.Solver

    def is_ground(self, term: FNode) -> bool:
        return check_ground_and_update(term, self.grounds)

    def to_z3(self, term: FNode) -> z3.ExprRef:
        if term.node_type() == FUNCTION:
            z3_fun = self.z3_funs[normalize(term.function_name())]
            args = [self.to_z3(sub_term) for sub_term in term.args()]
            return z3_fun(*args)

        symbol_name = str(term.symbol_name())
        symbol_type = term.symbol_type()
        return z3.Const(symbol_name, to_z3_sort(str(symbol_type)))

    def get_type(self, term: FNode) -> Optional[z3.ExprRef]:
        if to_z3_sort(term.get_type()) != T_U:
            return None

        const = self.to_z3(term)

        if term.is_function_application():
            fun = normalize(term.function_name())

            if fun in self.fun_types:
                kind = self.to_z3(self.fun_types[fun])

                return kind

        for type_term in self.grounds:
            if to_z3_sort(type_term.get_type()) != T_T:
                continue

            kind = self.to_z3(type_term)
            formula = z3.Not(TYPE_FUN(const) == kind)

            if self.solver.check(formula) == z3.unsat:
                return kind

        return None
