from glob import glob

import z3

files = glob('*.smt2')
files = [fn for fn in files if 'qifac_unsat_core' not in fn]
files = sorted(files, key=lambda x: len(open(x).read()))

for fn in files:
    print()
    print(fn)
    s = z3.Solver()
    s.from_file(fn)
    res = s.check()
    print(f'original file: {res}')
    if res == z3.unsat:
        assertions = s.assertions()
        s = z3.Solver()
        bools = [z3.Bool(f'__qifac___flag_{i}') for i in range(len(assertions))]
        s.add(*(z3.Implies(b, a) for a, b in zip(assertions, bools)))
        res = s.check(*bools)
        print(f'with indicator variabes: {res}')
        if res == z3.unknown:
            print('    {s.reason_unknown()}')
        elif res == z3.unsat:
            unsat_core = list(s.unsat_core())
            ii = [int(str(b).split('_')[-1]) for b in unsat_core]
            unsat_core_assertions = [assertions[i] for i in ii]
            print(f'found unsat core with {len(unsat_core_assertions)} assertions')
            s = z3.Solver()
            s.add(*unsat_core_assertions)
            res = s.check()
            print(res)
            if res == z3.unknown:
                print(s.reason_unknown())
            open(fn + '.qifac_unsat_core.smt2', 'w').write(s.to_smt2())
            open(fn + '.qifac_unsat_core.dat', 'w').write(repr(ii))
