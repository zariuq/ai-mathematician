CETTA ?= cetta
.DEFAULT_GOAL := test-cetta
VAMPIRE ?= .cetta/tools/vampire-5.1.0-linux-x64/vampire
PYTHON ?= python3
CORPUS ?=
LEAN ?= lean
DUPER ?= 0
HTTP_CETTA ?=
RUN_CONFIG ?= cetta-run.json
RESEARCH_CONFIG ?= cetta-research.example.json
ZIPPER ?= tools/duper-env/.lake/packages/auto/.lake/build/zipperposition.exe
ITP_RUNTIME ?= native
LEANC ?= $(shell "$(LEAN)" --print-prefix)/bin/leanc
ITP_NATIVE := .cetta/lean-native
ITP_COMPILER := .cetta/lean-compiler.txt
ITP_MODULES := MegLib Bridge CettaProofTactics CettaITP CettaProposalView CettaITPGuard
.SECONDARY: $(addprefix $(ITP_NATIVE)/ir/,$(addsuffix .c,$(ITP_MODULES) itp_driver itp_guard)) $(addprefix $(ITP_NATIVE)/ir/,$(addsuffix .o,$(ITP_MODULES) itp_driver itp_guard))

.PHONY: test-cetta test-cetta-library test-cetta-search test-cetta-atp test-cetta-itp test-cetta-prover

.PHONY: prepare-cetta-itp prepare-cetta-duper test-cetta-induction test-cetta-reconstruction
.PHONY: test-cetta-vampire-output test-cetta-lean-export test-cetta-experiment test-cetta-llm
.PHONY: run-cetta test-cetta-workers
.PHONY: test-cetta-ranked-bridge
.PHONY: test-cetta-upstream test-cetta-isolation test-cetta-proof-advice
.PHONY: test-cetta-smt
test-cetta-smt:
	$(PYTHON) tests/check_ai_mathematician_smt.py --cetta "$(CETTA)" \
		--vampire "$(VAMPIRE)" $(if $(strip $(CORPUS)),--corpus "$(CORPUS)")
test-cetta-proof-advice:
	$(PYTHON) tests/check_ai_mathematician_proof_advice.py --cetta "$(CETTA)" \
		$(if $(strip $(CORPUS)),--corpus "$(CORPUS)" --vampire "$(VAMPIRE)")
test-cetta-upstream:
	$(PYTHON) tests/check_ai_mathematician_upstream.py --cetta "$(CETTA)"
test-cetta-isolation: prepare-cetta-itp-native
	CETTA_ITP_RUNTIME=native $(PYTHON) tests/check_ai_mathematician_isolation.py --cetta "$(CETTA)" \
		--corpus "$(CORPUS)" --lean "$(LEAN)"
test-cetta-ranked-bridge:
	$(PYTHON) tests/check_ai_mathematician_ranked_bridge.py --cetta "$(CETTA)" --corpus "$(CORPUS)"
run-cetta: prepare-cetta-itp-native
	LEAN_BIN="$(if $(findstring /,$(LEAN)),$(abspath $(LEAN)),$(LEAN))" \
	VAMPIRE_BIN="$(if $(findstring /,$(VAMPIRE)),$(abspath $(VAMPIRE)),$(VAMPIRE))" \
	CETTA_ITP_RUNTIME="$(ITP_RUNTIME)" \
	"$(CETTA)" --no-results --lang petta@1.0.6 phase1/workers_main.metta "$(RUN_CONFIG)"

test-cetta-workers: prepare-cetta-itp
	$(PYTHON) tests/check_ai_mathematician_workers.py --cetta "$(CETTA)" --lean "$(LEAN)" \
		--vampire "$(VAMPIRE)" $(if $(strip $(CORPUS)),--corpus "$(CORPUS)" --real)
prepare-cetta-itp: lib/CettaITPGuard.olean

# These programs execute tactics dynamically, but need no source frontend at
# startup. Generated proof libraries do not need editor/IDE metadata.
.PHONY: prepare-cetta-itp-native
prepare-cetta-itp-native: prepare-cetta-itp $(ITP_NATIVE)/itp-guard $(ITP_NATIVE)/itp-worker $(ITP_NATIVE)/sysroot.txt

.PHONY: test-cetta-itp-native
test-cetta-itp-native: prepare-cetta-itp-native
	CETTA_ITP_RUNTIME=native $(PYTHON) tests/check_ai_mathematician_itp.py --cetta "$(CETTA)" --lean "$(LEAN)" \
		$(if $(strip $(CORPUS)),--corpus "$(CORPUS)")

$(ITP_NATIVE)/sysroot.txt: $(ITP_COMPILER) Makefile
	mkdir -p "$(ITP_NATIVE)"
	"$(LEAN)" --print-prefix > $@.new
	mv -f $@.new $@

$(ITP_NATIVE)/lib/%.olean $(ITP_NATIVE)/ir/%.c &: lib/%.lean $(ITP_COMPILER) Makefile
	mkdir -p "$(ITP_NATIVE)/lib" "$(ITP_NATIVE)/ir"
	LEAN_PATH="$(ITP_NATIVE)/lib" "$(LEAN)" -Dlinter.unusedVariables=false -R lib \
		-o "$(ITP_NATIVE)/lib/$*.olean" -c "$(ITP_NATIVE)/ir/$*.c" "$<"

$(ITP_NATIVE)/lib/Bridge.olean $(ITP_NATIVE)/ir/Bridge.c: $(ITP_NATIVE)/lib/MegLib.olean
$(ITP_NATIVE)/lib/CettaProofTactics.olean $(ITP_NATIVE)/ir/CettaProofTactics.c: $(ITP_NATIVE)/lib/Bridge.olean
$(ITP_NATIVE)/lib/CettaITP.olean $(ITP_NATIVE)/ir/CettaITP.c: $(ITP_NATIVE)/lib/CettaProofTactics.olean
$(ITP_NATIVE)/lib/CettaITPGuard.olean $(ITP_NATIVE)/ir/CettaITPGuard.c: $(ITP_NATIVE)/lib/CettaITP.olean
$(ITP_NATIVE)/lib/CettaITPGuard.olean $(ITP_NATIVE)/ir/CettaITPGuard.c: $(ITP_NATIVE)/lib/CettaProposalView.olean

$(ITP_NATIVE)/ir/itp_driver.c: phase1/itp_driver.lean $(ITP_NATIVE)/lib/CettaITP.olean Makefile
	LEAN_PATH="$(ITP_NATIVE)/lib" "$(LEAN)" -R phase1 -c "$@" "$<"

$(ITP_NATIVE)/ir/itp_guard.c: phase1/itp_guard.lean $(ITP_NATIVE)/lib/CettaITPGuard.olean Makefile
	LEAN_PATH="$(ITP_NATIVE)/lib" "$(LEAN)" -R phase1 -c "$@" "$<"

$(ITP_NATIVE)/ir/%.o: $(ITP_NATIVE)/ir/%.c
	"$(LEANC)" -O3 -DNDEBUG -DLEAN_EXPORTING -c "$<" -o "$@"

$(ITP_NATIVE)/itp-guard: $(ITP_NATIVE)/ir/itp_guard.o $(addprefix $(ITP_NATIVE)/ir/,$(addsuffix .o,$(ITP_MODULES)))
	"$(LEANC)" -O3 -rdynamic $^ -o "$@.new"
	mv -f "$@.new" "$@"

$(ITP_NATIVE)/itp-worker: $(ITP_NATIVE)/ir/itp_driver.o $(addprefix $(ITP_NATIVE)/ir/,$(addsuffix .o,$(filter-out CettaITPGuard CettaProposalView,$(ITP_MODULES))))
	"$(LEANC)" -O3 -rdynamic $^ -o "$@.new"
	mv -f "$@.new" "$@"

.PHONY: itp-compiler-check
itp-compiler-check:
$(ITP_COMPILER): itp-compiler-check
	mkdir -p .cetta
	"$(LEAN)" --print-prefix > "$@.new"
	"$(LEAN)" --version >> "$@.new"
	@if ! cmp -s "$@.new" "$@"; then mv -f "$@.new" "$@"; fi

prepare-cetta-duper:
	lake -d tools/duper-env build Duper

test-cetta-induction: prepare-cetta-itp
	$(PYTHON) tests/check_ai_mathematician_induction.py --cetta "$(CETTA)" \
		--corpus "$(CORPUS)" --all

test-cetta-reconstruction: prepare-cetta-itp
	$(PYTHON) tests/check_ai_mathematician_reconstruction.py --cetta "$(CETTA)" --lean "$(LEAN)" \
		--vampire "$(VAMPIRE)" $(if $(strip $(CORPUS)),--corpus "$(CORPUS)") \
		$(if $(filter 1,$(DUPER)),--duper)

lib/MegLib.olean: lib/MegLib.lean lean-toolchain $(ITP_COMPILER)
	$(LEAN) -Dlinter.unusedVariables=false -o $@ $<

lib/Bridge.olean: lib/Bridge.lean lib/MegLib.olean
	LEAN_PATH=lib $(LEAN) -o $@ $<

lib/CettaProofTactics.olean: lib/CettaProofTactics.lean lib/Bridge.olean
	LEAN_PATH=lib $(LEAN) -o $@ $<

lib/CettaITP.olean: lib/CettaITP.lean lib/CettaProofTactics.olean
	LEAN_PATH=lib $(LEAN) -o $@ $<

lib/CettaProposalView.olean: lib/CettaProposalView.lean $(ITP_COMPILER)
	$(LEAN) -o $@ $<

lib/CettaITPGuard.olean: lib/CettaITPGuard.lean lib/CettaITP.olean lib/CettaProposalView.olean
	LEAN_PATH=lib $(LEAN) -o $@ $<

test-cetta: test-cetta-library test-cetta-search test-cetta-atp test-cetta-itp test-cetta-prover test-cetta-reconstruction test-cetta-vampire-output test-cetta-lean-export test-cetta-llm test-cetta-workers $(if $(strip $(CORPUS)),test-cetta-induction test-cetta-experiment)
test-cetta: test-cetta-upstream test-cetta-proof-advice test-cetta-smt $(if $(strip $(CORPUS)),test-cetta-ranked-bridge test-cetta-isolation)

test-cetta-vampire-output:
	$(PYTHON) tests/check_ai_mathematician_vampire_output.py --cetta "$(CETTA)"

test-cetta-lean-export:
	$(PYTHON) tests/check_ai_mathematician_lean_export.py --cetta "$(CETTA)" --lean "$(LEAN)" \
		$(if $(strip $(CORPUS)),--corpus "$(CORPUS)")

test-cetta-experiment: prepare-cetta-itp
	$(PYTHON) tests/check_ai_mathematician_experiment.py --cetta "$(CETTA)" --lean "$(LEAN)" \
		--vampire "$(VAMPIRE)" --corpus "$(CORPUS)" $(if $(filter 1,$(DUPER)),--duper)

test-cetta-llm: prepare-cetta-itp
	$(PYTHON) tests/check_ai_mathematician_llm.py --cetta "$(CETTA)" --lean "$(LEAN)" \
		$(if $(strip $(HTTP_CETTA)),--http-cetta "$(HTTP_CETTA)") \
		$(if $(strip $(CORPUS)),--corpus "$(CORPUS)" --vampire "$(VAMPIRE)")

test-cetta-prover: prepare-cetta-itp
	$(PYTHON) tests/check_ai_mathematician_prover.py --cetta "$(CETTA)" --lean "$(LEAN)" \
		--vampire "$(VAMPIRE)" $(if $(strip $(CORPUS)),--corpus "$(CORPUS)")

test-cetta-itp: prepare-cetta-itp
	$(PYTHON) tests/check_ai_mathematician_itp.py --cetta "$(CETTA)" --lean "$(LEAN)" \
		$(if $(strip $(CORPUS)),--corpus "$(CORPUS)")

test-cetta-library:
	$(PYTHON) tests/check_ai_mathematician_library.py --cetta "$(CETTA)" \
		--generated 256 $(if $(strip $(CORPUS)),--corpus "$(CORPUS)")

test-cetta-search:
	$(PYTHON) tests/check_ai_mathematician_search.py --cetta "$(CETTA)" \
		$(if $(strip $(CORPUS)),--corpus "$(CORPUS)" --check-recall)

test-cetta-atp:
	$(PYTHON) tests/check_ai_mathematician_atp.py --cetta "$(CETTA)" \
		--vampire "$(VAMPIRE)" --generated 256 \
		$(if $(strip $(CORPUS)),--corpus "$(CORPUS)")

# Optional runtime integration; normal application tests need neither Cesta nor C sources.
CETTA_SOURCE ?=
QUALIFICATION_OUTPUT ?= .cetta/qualification
QUALIFICATION_RESUME ?= 0
.PHONY: qualify-cetta
qualify-cetta: prepare-cetta-itp-native prepare-cetta-duper
	$(PYTHON) tests/qualify_ai_mathematician.py --cetta "$(CETTA)" \
		--engine-source "$(CETTA_SOURCE)" \
		--corpus "$(CORPUS)" --vampire "$(VAMPIRE)" --lean "$(LEAN)" \
		--zipper "$(ZIPPER)" --output "$(QUALIFICATION_OUTPUT)" $(if $(filter 1,$(QUALIFICATION_RESUME)),--resume)
.PHONY: test-cetta-layout-runtime
QUALIFICATION_BASELINE ?= .cetta/qualification
FUNCTIONAL_QUALIFICATION_OUTPUT ?= .cetta/functional-qualification
.PHONY: qualify-cetta-functionality
qualify-cetta-functionality:
	$(PYTHON) tests/check_ai_mathematician_functionality.py
	$(PYTHON) tests/qualify_ai_mathematician_functionality.py \
		--baseline "$(QUALIFICATION_BASELINE)" --output "$(FUNCTIONAL_QUALIFICATION_OUTPUT)" --zipper "$(ZIPPER)"

.PHONY: run-cetta-research test-cetta-research
run-cetta-research: prepare-cetta-itp-native
	CETTA_ITP_RUNTIME="$(ITP_RUNTIME)" "$(CETTA)" --no-results --lang petta@1.0.6 \
		phase1/research_main.metta "$(RESEARCH_CONFIG)"

test-cetta-research:
	CETTA_ITP_RUNTIME=native $(PYTHON) tests/check_ai_mathematician_research.py --cetta "$(CETTA)" \
		--corpus "$(CORPUS)" --lean "$(LEAN)" --zipper "$(ZIPPER)" --vampire "$(VAMPIRE)" --require-integrations

test-cetta-layout-runtime:
	$(PYTHON) tests/check_cetta_layout_runtime.py --cetta "$(CETTA)" --cetta-source "$(CETTA_SOURCE)"
