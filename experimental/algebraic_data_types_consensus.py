from itertools import product, chain

import z3

if False:
    node = z3.DeclareSort('node')
    quorum = z3.DeclareSort('quorum')
    value = z3.DeclareSort('value')
else:
    S = z3.DeclareSort('S')
    node = S
    quorum = S
    value = S

member = z3.Function('member', node, quorum, z3.BoolSort())
intersection = z3.Function('intersection', quorum, quorum, node)
vote = z3.Function('vote', node, value, z3.BoolSort())
decided = z3.Function('decided', value, z3.BoolSort())
quorum_of_decided = z3.Function('quorum_of_decided', value, quorum)

n = z3.Const('n', node)
n1 = z3.Const('n1', node)
n2 = z3.Const('n2', node)
v = z3.Const('v', value)
v1 = z3.Const('v1', value)
v2 = z3.Const('v2', value)
q = z3.Const('q', quorum)
q1 = z3.Const('q1', quorum)
q2 = z3.Const('q2', quorum)

qf_assertions = [
    decided(v1),
    v1 != v2,
]

forall_assertions = [
    z3.ForAll([q1, q2], member(intersection(q1, q2), q1)),
    z3.ForAll([q1, q2], member(intersection(q1, q2), q2)),
    z3.ForAll([n, v1, v2], z3.Implies(z3.And(vote(n,v1),vote(n,v2)), v1 == v2)),
    z3.ForAll([v, n], z3.Implies(decided(v), z3.Implies(member(n, quorum_of_decided(v)), vote(n,v)))),
    z3.ForAll([n], z3.Implies(member(n,q2), vote(n,v2))),
]

def minimize_model(s, n=1):
    def limit(k):
        xs = [z3.Const(f'x{i}', S) for i in range(k)]
        y = z3.Const('y', S)
        s.add(z3.Exists(xs, z3.ForAll([y], z3.Or(*(y == x for x in xs)))))
    assert s.check() == z3.sat
    while True:
        s.push()
        limit(n)
        if (res := s.check()) == z3.sat:
            m = s.model()
            s.pop()
            return n, m
        else:
            assert res == z3.unsat
            s.pop()
            n += 1


print('Fully quantified query:')
s = z3.Solver()
s.add(*chain(qf_assertions, forall_assertions))
print(s)
print(s.check())
print()

print('Only ground query:')
s = z3.Solver()
s.add(*qf_assertions)
print(s)
print(s.check())
print()

all_live_terms = [v1, v2, quorum_of_decided(v1), q2, intersection(quorum_of_decided(v1),q2)]
models = []
for i in range(len(all_live_terms) + 1):
    print(f'Checking with {i} live terms:')
    live_terms = all_live_terms[:i]
    def live(xs):
        return z3.And([z3.Or([x == t for t in live_terms])for x in xs])
    def forall(xs, body):
        return z3.ForAll(xs, z3.Implies(live(xs), body))
    s = z3.Solver()
    s.add(*qf_assertions)
    for f in forall_assertions:
        vs = [z3.Const(f.var_name(i), f.var_sort(i)) for i in range(f.num_vars())]
        s.add(forall(vs, f.body()))
    print(s)
    res = s.check()
    print(res)
    if res == z3.sat:
        n_m, m = minimize_model(s)
        print(n_m, m)
        models.append(m)
    print()

def to_bool(x):
    if x is True or x is False:
        return x
    else:
        assert z3.is_true(x) or z3.is_false(x), x
        return z3.is_true(x)

print(f'Using ADTs over {len(models)} models:')
ctx = z3.Context()
s = z3.Solver(ctx=ctx)

GroundTerm = z3.Datatype('GroundTerm', ctx=ctx)
GroundTerm.declare('GT_v1')
GroundTerm.declare('GT_v2')
GroundTerm.declare('GT_q2')
GroundTerm.declare('GT_intersection', ('GT_intersection_0', GroundTerm), ('GT_intersection_1', GroundTerm))
GroundTerm.declare('GT_quorum_of_decided', ('GT_quorum_of_decided_0', GroundTerm))
GroundTerm = GroundTerm.create()

def adt_to_term(t):
    def _(f):
        res = z3.simplify(f(t))
        if z3.is_true(res):
            return True
        elif z3.is_false(res):
            return False
        else:
            return adt_to_term(res)
    if _(GroundTerm.is_GT_v1):
        return v1
    elif _(GroundTerm.is_GT_v2):
        return v2
    elif _(GroundTerm.is_GT_q2):
        return q2
    elif _(GroundTerm.is_GT_intersection):
        return intersection(_(GroundTerm.GT_intersection_0), _(GroundTerm.GT_intersection_1))
    elif _(GroundTerm.is_GT_quorum_of_decided):
        return quorum_of_decided(_(GroundTerm.GT_quorum_of_decided_0))
    else:
        assert False, t

t = z3.Const('t', GroundTerm)
#n_terms_for_instantiation = 1
n_terms_for_instantiation = 2
terms_for_instantiation = [z3.Const(f't_{i}', GroundTerm) for i in range(n_terms_for_instantiation)]

def add_model(I, M):
    # U = sorted(M.get_universe(S), key=str)
    U = sorted(M.get_universe(S), key=lambda x: int(str(x).split('!')[-1]))
    E, ES = z3.EnumSort(f'E_{I}', [f'E_{I}_{i}' for i in range(len(U))], ctx=ctx)

    # Ground term ADT that interprets to E:
    functions = [intersection, quorum_of_decided]
    function_interps = [
        { xs: U.index(M.eval(f(*(U[x] for x in xs)), model_completion=True))
          for xs in product(range(len(U)), repeat=f.arity())
        }
        for f in functions
    ]
    constants = [v1, v2, q2]
    constant_interps = [U.index(M.eval(c, model_completion=True)) for c in constants]
    interpret = z3.RecFunction(f'interpret_{I}', GroundTerm, E)
    entries = []
    for c, ci in zip(constants, constant_interps):
        entries.append((
            getattr(GroundTerm, f'is_GT_{c}')(t),
            ES[ci]
        ))
    for f, fi in zip(functions, function_interps):
        for xs in product(range(len(U)), repeat=f.arity()):
            entries.append((
                z3.And(getattr(GroundTerm, f'is_GT_{f}')(t), *(
                    interpret(getattr(GroundTerm, f'GT_{f}_{i}')(t)) == ES[xs[i]]
                    for i in range(f.arity())
                )),
                ES[fi[xs]]
            ))
    # def ite_from_entries(es):
    #     if len(es) == 0:
    #         return ES[0]
    #     else:
    #         return z3.If(es[0][0], es[0][1], ite_from_entries(es[1:]))
    def ite_from_entries(es):
        ite = ES[0]
        for e in reversed(es):
            ite = z3.If(e[0], e[1], ite)
        return ite
    ite = ite_from_entries(entries)
    z3.RecAddDefinition(interpret, t, ite)

    # Bodies of quantified assertions, indicator variables, and witnesses
    bodies = [
        z3.Function(f'body_{I}_{i}', *([E] * f.num_vars() + [z3.BoolSort(ctx=ctx)]))
        for i, f in enumerate(forall_assertions)
    ]
    indicators = [z3.Bool(f'violate_{I}_{i}', ctx=ctx) for i in range(len(forall_assertions))]
    witnesses = [
        [z3.Const(f'witness_{I}_{i}_{j}', E) for j in range(f.num_vars())]
        for i, f in enumerate(forall_assertions)
    ]
    s.add(z3.Or(*indicators))
    for f, b in zip(forall_assertions, bodies):
        n = f.num_vars()
        for xs, es in zip(product(U, repeat=n), product(ES, repeat=n)):
            res = to_bool(M.eval(z3.substitute_vars(f.body(), *xs), model_completion=True))
            lit = b(*es)
            if not res:
                lit = z3.Not(lit)
            # print(lit)
            s.add(lit)
    for i in range(len(forall_assertions)):
        s.add(z3.Implies(indicators[i], z3.Not(bodies[i](*witnesses[i]))))
        for w in witnesses[i]:
            s.add(z3.Implies(indicators[i], z3.Or(*(w == interpret(t) for t in terms_for_instantiation))))
    return (M, U, (E, ES), interpret, bodies, indicators, witnesses)

MUEIBVWs = []
for I, M in enumerate(models):
    MUEIBVWs.append(add_model(I, M))

# open('test.smt2', 'w').write(s.to_smt2())  # the definition of interpret seems to be missing
res = s.check()
print(s.check())
ground_instantiations = []
if res == z3.sat:
    m = s.model()
    for (I, (M, U, (E, ES), interpret, bodies, indicators, witnesses)) in enumerate(MUEIBVWs):
        print(f'model {I}:')
        violated = [m[v] is not None and to_bool(m[v]) for v in indicators]
        assert any(violated)
        assert violated.count(True) == 1
        for i, v in enumerate(violated):
            if v:
                print(f'    violates assertion {i}: {forall_assertions[i]}')
                ws = [m[w] for w in witnesses[i]]
                print(f'    witnesses are: {ws}')
                adts = []
                for w in ws:
                    eqs = [to_bool(z3.simplify(w == m.eval(interpret(m[t])))) for t in terms_for_instantiation]
                    assert any(eqs)
                    j = eqs.index(True)
                    adts.append(m[terms_for_instantiation[j]])
                print(f'    ground term ADTs are: {adts}')
                ts = [adt_to_term(t) for t in adts]
                print(f'    ground terms are: {ts}')
                elems = [M.eval(t) for t in ts]
                print(f'    ground terms evaluate to: {elems}')
                assert [U.index(e) for e in elems] == [ES.index(m[w]) for w in witnesses[i]]
                g = z3.substitute_vars(forall_assertions[i].body(), *ts)
                print(f'    ground instance is: {g}')
                print(f'    it evaluates to: {M.eval(g)}')
                assert z3.is_false(M.eval(g)), (I, ws, adts, ts, elems, g, M.eval(g))
                if len(ground_instantiations) == I:  # append only the first violated in each model
                    ground_instantiations.append(g)
print('\nSummary:')
print(f'\nFound the following ADTs:', [m[t] for t in terms_for_instantiation])
print(f'\nThey correspond to terms:', [adt_to_term(m[t]) for t in terms_for_instantiation])
print(f'\nAll models are hit using the following {len(ground_instantiations)} ground instantiations:')
for g in ground_instantiations:
    print(f'\n{g}')


print(f'\nTrying to do MBQI:\n')
s_smt = z3.Solver()
s_smt.add(*qf_assertions)
while (res := s_smt.check()) != z3.unsat:
    assert res == z3.sat
    n_M, M = minimize_model(s_smt)
    print(f'\nFound {len(MUEIBVWs) + 1}-th model with {n_M} elements: \n{M}')
    MUEIBVWs.append(add_model(len(MUEIBVWs), M))

    res = s.check()
    print(f'finding new instantiations: {res}')
    ground_instantiations = []
    if res == z3.sat:
        m = s.model()
        for (I, (M, U, (E, ES), interpret, bodies, indicators, witnesses)) in enumerate(MUEIBVWs):
            print(f'model {I}:')
            violated = [m[v] is not None and to_bool(m[v]) for v in indicators]
            assert any(violated)
            assert violated.count(True) == 1
            for i, v in enumerate(violated):
                if v:
                    print(f'    violates assertion {i}: {forall_assertions[i]}')
                    ws = [m[w] for w in witnesses[i]]
                    print(f'    witnesses are: {ws}')
                    adts = []
                    for w in ws:
                        eqs = [to_bool(z3.simplify(w == m.eval(interpret(m[t])))) for t in terms_for_instantiation]
                        assert any(eqs)
                        j = eqs.index(True)
                        adts.append(m[terms_for_instantiation[j]])
                    print(f'    ground term ADTs are: {adts}')
                    ts = [adt_to_term(t) for t in adts]
                    print(f'    ground terms are: {ts}')
                    elems = [M.eval(t) for t in ts]
                    print(f'    ground terms evaluate to: {elems}')
                    assert [U.index(e) for e in elems] == [ES.index(m[w]) for w in witnesses[i]]
                    g = z3.substitute_vars(forall_assertions[i].body(), *ts)
                    print(f'    ground instance is: {g}')
                    print(f'    it evaluates to: {M.eval(g)}')
                    assert z3.is_false(M.eval(g)), (I, ws, adts, ts, elems, g, M.eval(g))
                    if len(ground_instantiations) == I:  # append only the first violated in each model
                        ground_instantiations.append(g)
    elif res == z3.unsat:
        print(f'Cannot hit all models with {n_terms_for_instantiation} ground terms')
        break
    else:
        assert False

    print(f'\nSummary for the {I}-th iteration:')
    print(f'\nFound the following ADTs:', [m[t] for t in terms_for_instantiation])
    print(f'\nThey correspond to terms:', [adt_to_term(m[t]) for t in terms_for_instantiation])
    print(f'\nAll models are hit using the following {len(ground_instantiations)} ground instantiations:')
    for g in ground_instantiations:
        print(f'\n{g}')
        s_smt.add(g)
print(f'ADT-based MBQI done! (s_smt is {s_smt.check()})')
