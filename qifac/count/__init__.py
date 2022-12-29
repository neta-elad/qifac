import io
from typing import Any, TextIO

import z3


def count_quantifiers(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()
    solver = z3.Solver()
    solver.from_string(smt_file.read())

    def count(formula: z3.ExprRef, negations: int) -> Any:
        if z3.is_eq(formula):
            return []
        elif z3.is_distinct(formula):
            return []
        elif z3.is_app(formula) and formula.decl().range() != z3.BoolSort():
            return []
        elif z3.is_and(formula) or z3.is_or(formula):
            results = [count(child, negations) for child in formula.children()]
            return results
        elif z3.is_not(formula):
            return count(formula.children()[0], negations + 1)
        elif z3.is_implies(formula):
            antecedent, consequent = formula.children()
            return [count(antecedent, negations + 1), count(consequent, negations)]
        elif z3.is_quantifier(formula):
            head = None
            if formula.is_forall() and negations % 2 == 0:
                head = formula.num_vars()
            elif formula.is_exists() and negations % 2 == 1:
                head = formula.num_vars()

            if head is None:
                return count(formula.children()[0], negations)
            else:
                return head, count(formula.children()[0], negations)
        else:
            return []

    for assertion in solver.assertions():
        result = count(assertion, 0)
        buffer.write(result)
        buffer.write("\n")

    buffer.seek(0)
    return buffer
