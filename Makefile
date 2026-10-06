LEAN_DIR := Lean
ROOT := $(CURDIR)
VENV := .local/venv
VIEW_BASE := .local/check-views
LE := scripts/physics/low-energy
EV := evidence/physics/low-energy
CQ := evidence/physics/constrained-quantum
LE_SRC := Verification/physics/low-energy-phenomenology
ECD := $(LE_SRC)/external-composite-decay
VIEW_DEPS := --path-prefix $(LE_SRC)/ \
  --receipt-prefix $(CQ)/ --receipt-prefix $(EV)/ \
  --path Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean \
  --path Lean/SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair/ColorDoublet.lean

.PHONY: bootstrap build check check-map check-5a check-5a-k check-case2 check-obs check-physics check-all clean

bootstrap:
	cd $(LEAN_DIR) && lake exe cache get

build:
	cd $(LEAN_DIR) && lake build

$(VENV)/bin/python:
	python3 -m venv $(VENV)
	$(VENV)/bin/python -m pip install --quiet sympy mpmath numpy

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

# Export identities: pinned module bytes, original artifacts and public receipt payloads.
check-map: $(VENV)/bin/python
	$(VENV)/bin/python tools/source_view.py --verify-all

# Case 5A (constrained-local-quantum): reconstruct the ECD source tree at each
# pinned revision and rerun the frozen independent consumers (~40 min total).
check-5a: $(VENV)/bin/python
	rm -rf $(VIEW_BASE)/5a-t $(VIEW_BASE)/5a-v $(VIEW_BASE)/5a-x
	$(VENV)/bin/python tools/source_view.py --output $(VIEW_BASE)/5a-t --at T $(VIEW_DEPS)
	cd $(VIEW_BASE)/5a-t/$(ECD) && \
	  $(ROOT)/$(VENV)/bin/python independent_source_first_order_cauchy.py
	$(VENV)/bin/python tools/compare_evidence.py \
	  $(VIEW_BASE)/5a-t/$(ECD)/independent_source_first_order_cauchy.json \
	  $(CQ)/independent_source_first_order_cauchy.json
	$(VENV)/bin/python tools/source_view.py --output $(VIEW_BASE)/5a-v --at V $(VIEW_DEPS)
	cd $(VIEW_BASE)/5a-v/$(ECD) && \
	  $(ROOT)/$(VENV)/bin/python independent_source_quantum_gauss_section.py
	$(VENV)/bin/python tools/compare_evidence.py \
	  $(VIEW_BASE)/5a-v/$(ECD)/independent_source_quantum_gauss_section.json \
	  $(CQ)/independent_source_quantum_gauss_section.json
	$(VENV)/bin/python tools/source_view.py --output $(VIEW_BASE)/5a-x --at X $(VIEW_DEPS)
	cd $(VIEW_BASE)/5a-x/$(ECD) && \
	  $(ROOT)/$(VENV)/bin/python independent_source_joint_ccr_car_ports.py
	$(VENV)/bin/python tools/compare_evidence.py \
	  $(VIEW_BASE)/5a-x/$(ECD)/independent_source_joint_ccr_car_ports.json \
	  $(CQ)/independent_source_joint_ccr_car_ports.json
	@echo "case 5A era views and independent consumers passed"

# Case 5A K15-K17: each increment is pinned at its own commit (none is an
# ancestor of X). Rebuild the view, delete the frozen receipt inside it, rerun
# the original program and compare the fresh receipt field by field.
K_RUNS := K15:source_diagonal_core_history K16:source_diagonal_grade \
  K17:source_unitary_core_history
check-5a-k: $(VENV)/bin/python
	for run in $(K_RUNS); do \
	  tag=$${run%%:*}; prog=$${run#*:}; view=$(VIEW_BASE)/5a-$$tag; \
	  rm -rf $$view; \
	  $(VENV)/bin/python tools/source_view.py --output $$view --at $$tag $(VIEW_DEPS) >/dev/null || exit 1; \
	  rm -f $$view/$(ECD)/$$prog.json; \
	  (cd $$view/$(ECD) && $(ROOT)/$(VENV)/bin/python $$prog.py) || exit 1; \
	  $(VENV)/bin/python tools/compare_evidence.py $$view/$(ECD)/$$prog.json $(CQ)/$$prog.json || exit 1; \
	done
	@echo "case 5A K15-K17 programs reproduced their frozen receipts"

# CourtyCourt Case 2 (low-energy-loop-response): T-revision view plus the
# package audit consumers inside it. The audit/verify_*.py harnesses also need
# a built source package and source-repository lint tools; this target runs
# the listed Python checks. The default Lean build checks exported modules.
CASE2_AUDITS := \
  packet-gauge-spatial-propagation-curvature/audit/independent_bounds.py \
  packet-gauge-spatial-propagation-curvature/audit/independent_angular.py \
  packet-gauge-spatial-propagation-curvature/audit/independent_series.py \
  packet-gauge-spatial-reader-curvature/audit/independent.py \
  packet-window-second-order/audit/check.py \
  packet-curvature-coefficients/audit/bounds.py \
  packet-curvature-coefficients/audit/jets.py \
  packet-curvature-coefficients/audit/replay.py \
  boson-effective/audit/independent_check.py \
  light-kernel/audit/independent_check.py \
  prepared-loops/audit/independent_check.py
check-case2: $(VENV)/bin/python
	$(VENV)/bin/python tools/source_view.py --output $(VIEW_BASE)/case2-t --at T $(VIEW_DEPS)
	cd $(VIEW_BASE)/case2-t/$(LE_SRC)/full-quantum && \
	  for s in $(CASE2_AUDITS); do $(ROOT)/$(VENV)/bin/python "$$s" || exit 1; done
	cd $(VIEW_BASE)/case2-t/$(LE_SRC)/full-quantum/closed-loops/audit && \
	  $(ROOT)/$(VENV)/bin/python independent_check.py --root $(ROOT)/$(VIEW_BASE)/case2-t
	@echo "case 2 full-quantum independent consumers passed"

# observation-dynamics: reconstruct the counted-observation tree at both
# pinned revisions and confirm the Gate.lean byte versions differ. Default
# Lean targets compile E/I paper entries; Gate audits remain frozen artifacts.
check-obs: $(VENV)/bin/python
	rm -rf $(VIEW_BASE)/obs-e $(VIEW_BASE)/obs-i
	$(VENV)/bin/python tools/source_view.py --output $(VIEW_BASE)/obs-e --at E \
	  --path-prefix Verification/no-island/
	$(VENV)/bin/python tools/source_view.py --output $(VIEW_BASE)/obs-i --at I \
	  --path-prefix Verification/no-island/
	cmp -s $(VIEW_BASE)/obs-e/Verification/no-island/counted-observation/Gate.lean \
	       $(VIEW_BASE)/obs-i/Verification/no-island/counted-observation/Gate.lean \
	  && { echo "Gate.lean unexpectedly identical across E and I"; exit 1; } \
	  || echo "Gate.lean E/I byte versions differ as pinned"
	@echo "observation-dynamics era views passed"

# physics-common-source appendix D.5: finite matrix/arithmetic checks of the
# displayed formulas (numpy only; no Homework source needed). The rerun must
# cover the same families and evaluations and stay within the recorded
# tolerance; residuals may differ in the last digits across numpy builds.
PC_EV := evidence/physics/common-source
check-physics: $(VENV)/bin/python
	rm -rf $(VIEW_BASE)/physics-core && mkdir -p $(VIEW_BASE)/physics-core
	cp scripts/physics/common-source/check_core_identities.py $(VIEW_BASE)/physics-core/
	cd $(VIEW_BASE)/physics-core && $(ROOT)/$(VENV)/bin/python check_core_identities.py
	$(VENV)/bin/python -c "import json,sys; f=json.load(open('$(VIEW_BASE)/physics-core/core-identity-checks.json')); r=json.load(open('$(PC_EV)/core-identity-checks.json')); ok=f['status']=='passed' and f['families']==r['families'] and f['evaluations']==r['evaluations'] and f['max_residual']<=r['absolute_tolerance']; print('physics core identities', 'passed' if ok else 'FAILED', f['families'], f['evaluations'], f['max_residual']); sys.exit(0 if ok else 1)"

check-all: check check-map check-5a check-5a-k check-case2 check-obs check-physics
	@echo "all tiers passed"

clean:
	rm -rf $(VIEW_BASE)

# Each first-release execution keeps its own view and result directory.
FR_RUN := .local/first-release-runs/$(shell python3 -c 'import uuid; print(uuid.uuid4().hex)')
FR_RUNTIME := checks/first-release-runtime.json
FR_QUANTUM := checks/first-release-quantum.json
FR_ARCHIVES ?= evidence/first-release/bell-inputs
.PHONY: build-first-release trust-first-release check-first-release-map check-first-release-entry check-first-release-bell check-first-release-quantum check-first-release-full

build-first-release:
	python3 tools/first_release.py build --output $(FR_RUN)/build

trust-first-release:
	python3 tools/first_release.py trust --output $(FR_RUN)/trust

check-first-release-map: check-map
	python3 tools/first_release.py verify-map

check-first-release-entry: check-first-release-map $(VENV)/bin/python
	$(VENV)/bin/python tools/first_release_replay.py entry --config $(FR_RUNTIME) --output $(FR_RUN)/entry --python $(ROOT)/$(VENV)/bin/python

check-first-release-bell: $(VENV)/bin/python
	$(VENV)/bin/python tools/first_release_replay.py bell --config $(FR_RUNTIME) --output $(FR_RUN)/bell --archive-dir $(FR_ARCHIVES) --python $(ROOT)/$(VENV)/bin/python

check-first-release-quantum: $(VENV)/bin/python
	$(VENV)/bin/python tools/first_release_quantum.py --config $(FR_QUANTUM) --output $(FR_RUN)/quantum --python $(ROOT)/$(VENV)/bin/python

check-first-release-full: $(VENV)/bin/python
	$(MAKE) build-first-release
	$(MAKE) trust-first-release
	$(MAKE) check-first-release-map
	$(VENV)/bin/python tools/first_release_replay.py full --config $(FR_RUNTIME) --output $(FR_RUN)/full --archive-dir $(FR_ARCHIVES) --python $(ROOT)/$(VENV)/bin/python
