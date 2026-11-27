# Rocq 9 / FreerDPS is the default complete verification profile.
PROFILE ?= freer
FREERDPS_THEORIES ?= $(abspath ../../.local/registry-proof-deps/FreerDPS/theories)
BUILD_DIR ?= $(abspath ../../.local/registry-build/$(PROFILE))
COQC ?= coqc
COQDEP ?= coqdep
COQCHK ?= coqchk
ROOT := $(CURDIR)
ALL_SOURCES := $(shell sed -n '/\.v$$/p' _CoqProject)
ifeq ($(PROFILE),freer)
SOURCES := $(ALL_SOURCES)
EXTERNAL := -Q "$(FREERDPS_THEORIES)" FreerDPS
AUDITS := Audit FreerAudit OwnedDataContract
else
SOURCES := $(foreach f,$(ALL_SOURCES),$(if $(filter Freer% OwnedData%,$(notdir $(f))),,$(f))) theories/interface/OwnedDataContract.v
AUDITS := Audit OwnedDataContract
endif
DIRS := $(sort $(patsubst %/,%,$(dir $(SOURCES))))
FLAGS := $(foreach d,$(DIRS),-Q $(d) OxideSE.Registry) $(EXTERNAL)
TARGETS := $(patsubst %.v,%.vo,$(filter $(foreach a,$(AUDITS),%/$(a).v),$(SOURCES)))

.PHONY: all check check-freer check-interface
all: $(BUILD_DIR)/dependencies.mk
	$(MAKE) -C "$(BUILD_DIR)" -f "$(ROOT)/compile.mk" FLAGS='$(FLAGS)' COQC="$(COQC)" $(TARGETS)

check: all
	cd "$(BUILD_DIR)" && $(COQCHK) $(FLAGS) $(addprefix OxideSE.Registry.,$(AUDITS))

check-freer:
	$(MAKE) PROFILE=freer check

# Compile the public statement in isolation from all project .v/.vo files.
check-interface:
	@set -eu; work=$$(mktemp -d); trap 'rm -rf "$$work"' EXIT; \
	cp theories/interface/OwnedDataContract.v "$$work/"; cd "$$work"; \
	$(COQC) -Q . OxideSE.Registry OwnedDataContract.v; \
	$(COQCHK) -Q . OxideSE.Registry OxideSE.Registry.OwnedDataContract

$(BUILD_DIR)/%.v: %.v
	@mkdir -p "$(dir $@)"
	@cp "$<" "$@"

$(BUILD_DIR)/dependencies.mk: $(addprefix $(BUILD_DIR)/,$(SOURCES)) _CoqProject Makefile
	cd "$(BUILD_DIR)" && $(COQDEP) $(FLAGS) $(SOURCES) > dependencies.tmp && mv dependencies.tmp dependencies.mk

# Remove only the generated products of this profile.
.PHONY: clean
clean:
	$(RM) $(foreach ext,vo vos vok glob,$(addprefix $(BUILD_DIR)/,$(SOURCES:.v=.$(ext)))) \
	  $(foreach f,$(SOURCES),$(BUILD_DIR)/$(dir $(f)).$(notdir $(f:.v=.aux))) \
	  "$(BUILD_DIR)/dependencies.mk" "$(BUILD_DIR)/.lia.cache" "$(BUILD_DIR)/.nia.cache"
