from typing import (
    Any,
    Iterable,
    List,
    Optional,
    Sequence,
    Tuple,
    TypeGuard,
    TypeVar,
    Union,
)

import z3

class Context: ...
class Z3PPObject: ...

class AstRef(Z3PPObject):
    def eq(self, other: Any) -> bool: ...

class SortRef(AstRef):
    def name(self) -> str: ...
    def kind(self) -> int: ...

class BoolSortRef(SortRef): ...
class ArithSortRef(SortRef): ...
class DatatypeRef(SortRef): ...

class Datatype:
    def __init__(self, name: str, ctx: z3.Context = ...) -> None: ...
    def create(self) -> DatatypeRef: ...
    def declare(
        self, name: str, *args: Tuple[str, Union[Datatype, SortRef]]
    ) -> None: ...

class FuncDeclRef(AstRef):
    def __call__(self, *args: ExprRef) -> ExprRef: ...
    def arity(self) -> int: ...
    def domain(self, i: int) -> SortRef: ...
    def range(self) -> SortRef: ...
    def name(self) -> str: ...
    def kind(self) -> int: ...

class RecFuncDeclRef(FuncDeclRef): ...

class ExprRef(AstRef):
    def children(self) -> List[ExprRef]: ...
    def __eq__(self, other) -> "BoolRef": ...  # type: ignore
    def __ne__(self, other) -> "BoolRef": ...  # type: ignore
    def decl(self) -> FuncDeclRef: ...
    def sort(self) -> SortRef: ...
    def sexpr(self) -> str: ...
    def num_args(self) -> int: ...
    def arg(self, i: int) -> "ExprRef": ...

class BoolRef(ExprRef): ...

class ArithRef(ExprRef):
    def __ge__(self, other: int) -> BoolRef: ...
    def __gt__(self, other: Any) -> BoolRef: ...
    def __le__(self, other: Any) -> BoolRef: ...
    def __lt__(self, other: Any) -> BoolRef: ...
    def __add__(self, other: int | ArithRef) -> ArithRef: ...
    def __sub__(self, other: int) -> ArithRef: ...

class Const(ExprRef):
    def __init__(self, name: str, sort: SortRef): ...
    def decl(self) -> FuncDeclRef: ...

class IntNumRef(Const, ArithRef):
    def as_long(self) -> int: ...

class QuantifierRef(BoolRef):
    def num_vars(self) -> int: ...
    def var_sort(self, idx: int) -> SortRef: ...
    def var_name(self, idx: int) -> str: ...
    def is_forall(self) -> bool: ...
    def is_exists(self) -> bool: ...
    def body(self) -> BoolRef: ...
    def get_id(self) -> int: ...

class CheckSatResult: ...

class ModelRef(Z3PPObject):
    def sorts(self) -> List[SortRef]: ...
    def get_universe(self, sort: SortRef) -> List[Const]: ...
    def decls(self) -> List[FuncDeclRef]: ...
    def eval(self, t: AnyExprRef, model_completion: bool = False) -> AnyExprRef: ...
    def sexpr(self) -> str: ...
    def __getitem__(self, t: AnyExprRef) -> AnyExprRef: ...

class Solver:
    def __init__(self, *, ctx: Context = ...) -> None: ...
    def check(
        self, *assumptions: Union[Iterable[ExprRef], ExprRef]
    ) -> CheckSatResult: ...
    def model(self) -> ModelRef: ...
    def reason_unknown(self) -> str: ...
    def set(self, *args: Any, **kwargs: Any) -> None: ...
    def from_file(self, filename: str) -> None: ...
    def from_string(self, string: str) -> None: ...
    def assertions(self) -> Sequence[BoolRef]: ...
    def unsat_core(self) -> Sequence[BoolRef]: ...
    def reset(self) -> None: ...
    def assert_exprs(self, *args: BoolRef) -> None: ...
    def add(self, arg: BoolRef) -> None: ...
    def to_smt2(self) -> str: ...
    def sexpr(self) -> str: ...
    def push(self) -> None: ...
    def pop(self) -> None: ...

class Optimize(Solver):
    def add_soft(self, arg: BoolRef) -> None: ...

class ApplyResult(Z3PPObject):
    def as_expr(self) -> ExprRef: ...

class Tactic:
    def __init__(self, name: str, ctx: Context = ...): ...
    def __call__(
        self, goal: ExprRef, *arguments: Any, **keywords: Any
    ) -> ApplyResult: ...
    def solver(self) -> Solver: ...

AnyExprRef = TypeVar("AnyExprRef", bound=ExprRef)

def DeclareSort(name: str, ctx: Context = ...) -> SortRef: ...
def EnumSort(
    name: str, values: List[str], ctx: Context = ...
) -> Tuple[SortRef, List[z3.Const]]: ...
def FreshConst(sort: SortRef, prefix: str = "") -> Const: ...
def Consts(names: str, sort: SortRef) -> Tuple[Const, ...]: ...
def Function(name: str, *sig: SortRef) -> FuncDeclRef: ...
def RecFunction(name: str, *sig: SortRef) -> RecFuncDeclRef: ...
def RecAddDefinition(
    f: RecFuncDeclRef, args: Union[Const, List[Const]], body: ExprRef
) -> None: ...
def FreshFunction(*sig: SortRef) -> FuncDeclRef: ...
def BoolSort(ctx: Context = ...) -> BoolSortRef: ...
def IntSort(ctx: Context = ...) -> ArithSortRef: ...
def Int(name: str, ctx: Context = ...) -> IntNumRef: ...
def IntVal(val: int, ctx: Context = ...) -> IntNumRef: ...
def Bool(name: str, ctx: Context = ...) -> BoolRef: ...
def BoolVal(val: bool, ctx: Context = ...) -> BoolRef: ...
def If(a: BoolRef, b: AnyExprRef, c: AnyExprRef, ctx: Context = ...) -> AnyExprRef: ...
def Sum(*args: IntNumRef) -> IntNumRef: ...
def And(*args: BoolRef) -> BoolRef: ...
def Or(*args: BoolRef) -> BoolRef: ...
def Not(a: BoolRef) -> BoolRef: ...
def Implies(a: BoolRef, b: BoolRef, ctx: Context = ...) -> BoolRef: ...
def Distinct(*args: ExprRef) -> BoolRef: ...
def ForAll(vs: Union[Const, List[Const]], body: ExprRef) -> QuantifierRef: ...
def Exists(vs: Union[Const, List[Const]], body: ExprRef) -> QuantifierRef: ...
def Var(idx: int, s: SortRef) -> ExprRef: ...
def is_ast(a: Any) -> TypeGuard[AstRef]: ...
def is_quantifier(a: Any) -> TypeGuard[QuantifierRef]: ...
def is_int(a: Any) -> bool: ...
def is_app(a: Any) -> bool: ...
def is_eq(a: Any) -> TypeGuard[BoolRef]: ...
def is_distinct(a: Any) -> TypeGuard[BoolRef]: ...
def is_const(a: Any) -> TypeGuard[Const]: ...
def is_arith(a: Any) -> TypeGuard[ArithRef]: ...
def is_int_value(a: Any) -> TypeGuard[IntNumRef]: ...
def is_var(a: Any) -> bool: ...
def is_or(a: Any) -> bool: ...
def is_and(a: Any) -> bool: ...
def is_not(a: Any) -> bool: ...
def is_implies(a: Any) -> bool: ...
def is_lt(a: Any) -> bool: ...
def is_le(a: Any) -> bool: ...
def is_ge(a: Any) -> bool: ...
def is_gt(a: Any) -> bool: ...
def is_add(a: Any) -> bool: ...
def is_sub(a: Any) -> bool: ...
def is_bool(a: Any) -> TypeGuard[BoolRef]: ...
def is_true(a: Any) -> TypeGuard[BoolRef]: ...
def is_false(a: Any) -> TypeGuard[BoolRef]: ...
def substitute_vars(t: AnyExprRef, *m: ExprRef) -> AnyExprRef: ...
def substitute(t: AnyExprRef, *m: Tuple[ExprRef, ExprRef]) -> AnyExprRef: ...
def RoundTowardZero() -> z3.ExprRef: ...
def set_param(*args: Any, **kwargs: Any) -> None: ...
def simplify(a: z3.ExprRef, *arguments: Any, **keywords: Any) -> z3.ExprRef: ...

sat: CheckSatResult = ...
unsat: CheckSatResult = ...
unknown: CheckSatResult = ...

Z3_OP_UNINTERPRETED: int = ...
Z3_UNINTERPRETED_SORT: int = ...
