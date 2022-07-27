# qifac: Quantifier Instantiations Finder and Cleaner

## Find Unsat-core
```bash
python -m 'src.unsat_core'
```

## Booleanize Quantifiers
```bash
python -m 'src.booleanize_quantifiers'
```

## Find Minimal Proof
```bash
python -m 'src.add_proof' <input> -t <z3tracer> -e <z3> \
    | python -m 'src.booleanize_quantifiers' \
    | python -m 'src.unsat_core' -e <z3>
```