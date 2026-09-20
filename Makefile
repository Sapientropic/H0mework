LEAN_DIR := Lean
VENV := .local/venv
VIEW_BASE := .local/check-views
LE := scripts/physics/low-energy
EV := evidence/physics/low-energy

.PHONY: bootstrap build check clean

bootstrap:
	cd $(LEAN_DIR) && lake exe cache get

build:
	cd $(LEAN_DIR) && lake build

$(VENV)/bin/python:
	python3 -m venv $(VENV)
	$(VENV)/bin/pip install --quiet sympy mpmath

check: $(VENV)/bin/python
	rm -rf $(VIEW_BASE)
	$(VENV)/bin/python tools/source_view.py \
	  --output $(VIEW_BASE)/readout \
	  --receipt $(EV)/results/exact-readout.json
	$(VENV)/bin/python $(LE)/check_readout.py \
	  --root $(VIEW_BASE)/readout --receipt $(EV)/results/exact-readout.json
	$(VENV)/bin/python $(LE)/stabilizer_check.py \
	  --receipt $(EV)/results/exact-readout.json --out $(VIEW_BASE)/stabilizer-check.json
	cmp $(VIEW_BASE)/stabilizer-check.json $(EV)/results/stabilizer-check.json
	$(VENV)/bin/python tools/source_view.py \
	  --output $(VIEW_BASE)/spatial \
	  --receipt $(EV)/occupied-response/receipt.json \
	  --path Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean \
	  --path Verification/physics/low-energy-phenomenology/occupied-response/spatial/finite-coupling/derivative/audit/independent-receipt.json \
	  --path Verification/physics/low-energy-phenomenology/occupied-response/spatial/global/audit/independent-receipt.json
	$(VENV)/bin/python $(LE)/occupied-response/spatial/global/independent_check.py \
	  --root $(VIEW_BASE)/spatial
	$(VENV)/bin/python $(LE)/occupied-response/spatial/finite-coupling-derivative/independent_check.py \
	  --root $(VIEW_BASE)/spatial
	@echo "all frozen evidence checks passed"

clean:
	rm -rf $(VIEW_BASE)
