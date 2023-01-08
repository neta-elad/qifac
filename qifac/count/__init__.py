import io
from functools import cache
from typing import Any, Dict, Set, TextIO, Tuple, TypeVar, Iterable, Callable

import z3


def count_symbols(smt_file: TextIO, show: bool = False) -> None:
    symbols: Dict[Tuple[int, z3.SortRef], Set[z3.FuncDeclRef]] = {}

    @cache
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


@cache
def is_ground(formula: z3.ExprRef) -> bool:
    if z3.is_var(formula):
        return False
    elif z3.is_const(formula):
        return True
    else:
        return all(is_ground(child) for child in formula.children())


@cache
def find_terms(formula: z3.ExprRef) -> Set[z3.ExprRef]:
    terms= set()
    if is_ground(formula) and z3.is_app(formula) and formula.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        decl = formula.decl()
        key = decl.range()
        if key != z3.BoolSort():
            terms.add(formula)

    for child in formula.children():
        terms |= find_terms(child)

    return terms

def find_all_terms(smt_file: TextIO) -> Set[z3.ExprRef]:
    all_terms = set()
    solver = z3.Solver()
    solver.from_string(smt_file.read())

    for assertion in solver.assertions():
        all_terms |= find_terms(assertion)

    return all_terms

def count_terms(smt_file: TextIO, show: bool = False) -> None:
    terms: Dict[z3.SortRef, Set[z3.ExprRef]] = {}

    all_terms = find_all_terms(smt_file)
    for term in all_terms:
        key = term.decl().range()
        terms.setdefault(key, set())
        terms[key].add(term)

    for sort, sort_terms in terms.items():
        if show:
            print(f"{sort} => {sort_terms}")
        else:
            print(f"{sort} => {len(sort_terms)}")



def count_quantifiers(smt_file: TextIO) -> TextIO:
    buffer = io.StringIO()
    solver = z3.Solver()
    solver.from_string(smt_file.read())

    @cache
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

T = TypeVar('T')
U = TypeVar('U')
V = TypeVar('V')

def extend_pair(pair: Tuple[T, U], value: V) -> Tuple[T, Tuple[U, V]]:
    return pair[0], (pair[1], value)

def max_pair(iterable: Iterable[Tuple[int, T]]) -> Tuple[int, T]:
    return max(iterable, key=lambda pair: pair[0])

def group_by(iterable: Iterable[T], key: Callable[[T], U]) -> Dict[U, Set[T]]:
    grouped: Dict[U, Set[T]] = {}

    for value in iterable:
        current_key = key(value)
        grouped.setdefault(current_key, set())
        grouped[current_key].add(value)

    return grouped


def count_depth_diff(smt_file: TextIO, instantiated_file: TextIO) -> None:
    original_terms = find_all_terms(smt_file)
    inst_terms = find_all_terms(instantiated_file)

    per_sort = group_by(inst_terms, lambda term: term.decl().range())

    @cache
    def depth_diff(formula: z3.ExprRef) -> Tuple[int, z3.ExprRef]:
        if formula in original_terms:
            return 0, formula

        term_depth, original_term = max_pair(depth_diff(child) for child in formula.children())
        return term_depth + 1, original_term

    for sort, terms in per_sort.items():
        max_depth, (org_term, inst_term) = max_pair(extend_pair(depth_diff(term), term) for term in terms)
        print(f"{sort}: {inst_term} is {max_depth} from {org_term}")

