import io
from typing import Any, Dict, Set, TextIO, Tuple

import z3


def count_symbols(smt_file: TextIO, show: bool = False) -> None:
    symbols: Dict[Tuple[int, z3.SortRef], Set[z3.FuncDeclRef]] = {}

    def walk_tree(formula: z3.ExprRef) -> None:
        if z3.is_app(formula) and formula.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            decl = formula.decl()
            key = decl.arity(), decl.range()
            symbols.setdefault(key, set())
            symbols[key].add(decl)

        for child in formula.children():
            walk_tree(child)

    solver = z3.Solver()
    solver.from_string(smt_file.read())

    for assertion in solver.assertions():
        walk_tree(assertion)

    keys = list(symbols.keys())

    sorted_keys = sorted(keys, key=lambda key: key[0])

    for key in sorted_keys:
        value = symbols[key]
        if show:
            print(f"{key} => {value}")
        else:
            print(f"{key} => {len(value)}")


def count_terms(smt_file: TextIO, show: bool = False) -> None:
    terms: Dict[z3.SortRef, Set[z3.ExprRef]] = {}

    def is_ground(formula: z3.ExprRef) -> bool:
        if z3.is_var(formula):
            return False
        elif z3.is_const(formula):
            return True
        else:
            return all(is_ground(child) for child in formula.children())

    def walk_tree(formula: z3.ExprRef) -> None:
        if z3.is_app(formula) and formula.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            decl = formula.decl()
            key = decl.range()
            if key != z3.BoolSort() and is_ground(formula):
                terms.setdefault(key, set())
                terms[key].add(formula)

        for child in formula.children():
            walk_tree(child)

    solver = z3.Solver()
    solver.from_string(smt_file.read())

    for assertion in solver.assertions():
        walk_tree(assertion)


    for sort, sort_terms in terms.items():
        if show:
            print(f"{sort} => {sort_terms}")
        else:
            print(f"{sort} => {len(sort_terms)}")


def count_quantifiers(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()
    solver = z3.Solver()
    solver.from_string(smt_file.read())

    def walk_tree(formula: z3.ExprRef, negations: int) -> Any:
        if z3.is_eq(formula):
            return []
        elif z3.is_distinct(formula):
            return []
        elif z3.is_app(formula) and formula.decl().range() != z3.BoolSort():
            return []
        elif z3.is_and(formula) or z3.is_or(formula):
            results = [walk_tree(child, negations) for child in formula.children()]
            return results
        elif z3.is_not(formula):
            return walk_tree(formula.children()[0], negations + 1)
        elif z3.is_implies(formula):
            antecedent, consequent = formula.children()
            return [
                walk_tree(antecedent, negations + 1),
                walk_tree(consequent, negations),
            ]
        elif z3.is_quantifier(formula):
            head = None
            if formula.is_forall() and negations % 2 == 0:
                head = formula.num_vars()
            elif formula.is_exists() and negations % 2 == 1:
                head = formula.num_vars()

            if head is None:
                return walk_tree(formula.children()[0], negations)
            else:
                return head, walk_tree(formula.children()[0], negations)
        else:
            return []

    for assertion in solver.assertions():

        result = walk_tree(assertion, 0)
        buffer.write(str(result))
        buffer.write("\n")

    buffer.seek(0)
    return buffer
