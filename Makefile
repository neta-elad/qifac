.PHONY: all
all: format lint type test

.PHONY: lint
lint:
	isort . -q
	autoflake . --recursive \
				--exclude .venv,submodules \
				--remove-unused-variables \
				--remove-all-unused-imports \
				--expand-star-imports \
				--in-place

.PHONY: format
format:
	black .

.PHONY: type
type:
	mypy --strict qifac


.PHONY: test
test:
	pytest


.PHONY: env
env:
	! [ -d .venv ] && python3 -m venv .venv || true

.PHONY: install
install:
	yes | pip uninstall qifac
	pip install -e .[test]

.PHONY: clean
clean:
	rm -r .venv
