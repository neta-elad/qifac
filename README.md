# QIFaC: Quantifier Instantiations Finder and Cleaner

## Installation
1. Clone the project:
    ```shell
    git clone git@github.com:neta-elad/qifac.git && cd qifac
    ```
2. Create a virtual environment (optional but highly recommended):
    ```shell
   make env && source .env/bin/activate
    ```
3. Install qifac:
    ```shell
   make install
    ```

## Tools
### Help
```shell
qifac --help
```
### Find unsat-core
```shell
qifac core find <input smt file> <output smt file>
```

### Extract Dafny's type information
```shell
qifac typeinfo grounds <input smt file>
```

### Collect all instantiations
```shell
qifac instances show <input smt file> <output instances file>
```

### Compare instantiations
```shell
qifac instances compare <unsat instances file> <unknown instances file>
```

## Ideas
- CEGAR
  - Choose asserts with or without MBQI
  - Are triggers fast enough 
  (or is there room to optimize which asserts to choose, 
  even if we only use triggers)
  - Choose asserts + instantiations
- Use type info for instantiations
  - Enumerative instantiations
- Instantiation data analysis
- Verus
  - Instantiation data analysis
  - type info (should be simpler and more informative)