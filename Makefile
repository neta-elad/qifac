.PHONMY: lint
lint: format type


.PHONY: format
format: check-env
	black .


.PHONY: type
type: check-env
	mypy --strict .

.PHONY: install
install: check-env
	pip install -r requirements.txt

.PHONY: check-env
check-env:
ifndef VIRTUAL_ENV
	$(error Please activate virtual environment: source .env/bin/activate)
endif
