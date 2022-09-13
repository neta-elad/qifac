.PHONY: all
all: format lint type test

.PHONY: lint
lint:
	isort . -q
	autoflake . --recursive \
				--exclude .env \
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
	pytest -q


.PHONY: env
env:
	! [ -d .env ] && python3 -m venv .env || true

.PHONY: install
install:
	yes | pip uninstall qifac
	pip install -e .[test]

.PHONY: clean
clean:
	rm -r .env