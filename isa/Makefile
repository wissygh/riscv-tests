#=======================================================================
# Makefile for riscv-tests/isa
#-----------------------------------------------------------------------

XLEN ?= 64

ENV = xs

src_dir := .
build_dir := build

$(shell mkdir -p build)

ifeq ($(XLEN),64)
include $(src_dir)/rv64ui/Makefrag
include $(src_dir)/rv64uc/Makefrag
include $(src_dir)/rv64um/Makefrag
include $(src_dir)/rv64ua/Makefrag
include $(src_dir)/rv64uf/Makefrag
include $(src_dir)/rv64ud/Makefrag
include $(src_dir)/rv64uzfh/Makefrag
include $(src_dir)/rv64uzba/Makefrag
include $(src_dir)/rv64uzbb/Makefrag
include $(src_dir)/rv64uzbc/Makefrag
include $(src_dir)/rv64uzbs/Makefrag
include $(src_dir)/rv64si/Makefrag
include $(src_dir)/rv64ssvnapot/Makefrag
include $(src_dir)/rv64mi/Makefrag
include $(src_dir)/rv64mzicbo/Makefrag
endif
include $(src_dir)/rv32ui/Makefrag
include $(src_dir)/rv32uc/Makefrag
include $(src_dir)/rv32um/Makefrag
include $(src_dir)/rv32ua/Makefrag
include $(src_dir)/rv32uf/Makefrag
include $(src_dir)/rv32ud/Makefrag
include $(src_dir)/rv32uzfh/Makefrag
include $(src_dir)/rv32uzba/Makefrag
include $(src_dir)/rv32uzbb/Makefrag
include $(src_dir)/rv32uzbc/Makefrag
include $(src_dir)/rv32uzbs/Makefrag
include $(src_dir)/rv32si/Makefrag
include $(src_dir)/rv32mi/Makefrag

default: all

#--------------------------------------------------------------------
# Build rules
#--------------------------------------------------------------------

RISCV_PREFIX ?= riscv$(XLEN)-linux-gnu-
RISCV_GCC ?= $(RISCV_PREFIX)gcc
RISCV_GCC_OPTS ?= -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -Wl,--build-id=none
RISCV_OBJDUMP ?= $(RISCV_PREFIX)objdump --disassemble-all --disassemble-zeroes
RISCV_OBJCOPY ?= $(RISCV_PREFIX)objcopy
RISCV_SIM ?= spike

vpath %.S $(src_dir)

#------------------------------------------------------------
# Build assembly tests

%.dump: %
	$(RISCV_OBJDUMP) $(build_dir)/$< > $(build_dir)/$@

%.bin: %
	$(RISCV_OBJCOPY) -O binary $(build_dir)/$< $(build_dir)/$@

%.out: %
	$(RISCV_SIM) --isa=rv64gc_zfh_zicboz_svnapot_zicntr_zba_zbb_zbc_zbs --misaligned $< 2> $@

%.out32: %
	$(RISCV_SIM) --isa=rv32gc_zfh_zicboz_svnapot_zicntr_zba_zbb_zbc_zbs --misaligned $< 2> $@

%.nemu-log: %.bin
	make -C $(NEMU_HOME) ISA=riscv64 run ARGS="--batch --log=$(abspath $(build_dir)/$@) $(abspath $(build_dir)/$<)"

%.noop-log: %.bin
	make -C $(NOOP_HOME) emu IMAGE="$(abspath $(build_dir)/$<)" 2>&1 | tee > $(abspath $(build_dir)/$@)
	cat $(build_dir)/$@ | grep "HIT GOOD TRAP"
	

define compile_template

$$($(1)_p_tests): $(1)-p-%: $(1)/%.S
	$$(RISCV_GCC) $(2) $$(RISCV_GCC_OPTS) -I$(src_dir)/../env/$(ENV) -I$(src_dir)/macros/scalar -T$(src_dir)/../env/$(ENV)/link.ld $$< -o $$(build_dir)/$$@
$(1)_tests += $$($(1)_p_tests)

# $$($(1)_v_tests): $(1)-v-%: $(1)/%.S
# 	$$(RISCV_GCC) $(2) $$(RISCV_GCC_OPTS) -DENTROPY=0x$$(shell echo \$$@ | md5sum | cut -c 1-7) -std=gnu99 -O2 -I$(src_dir)/../env/v -I$(src_dir)/macros/scalar -T$(src_dir)/../env/v/link.ld $(src_dir)/../env/v/entry.S $(src_dir)/../env/v/*.c $$< -o $$@
# $(1)_tests += $$($(1)_v_tests)

$(1)_tests_dump = $$(addsuffix .dump, $$($(1)_tests))
$(1)_tests_bin = $$(addsuffix .bin, $$($(1)_tests))

$(1): $$($(1)_tests_dump) $$($(1)_tests_bin)

.PHONY: $(1)

COMPILER_SUPPORTS_$(1) := $$(shell $$(RISCV_GCC) $(2) -c -x c /dev/null -o /dev/null 2> /dev/null; echo $$$$?)

ifeq ($$(COMPILER_SUPPORTS_$(1)),0)
tests += $$($(1)_tests)
endif

endef

$(eval $(call compile_template,rv32ui,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32uc,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32um,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32ua,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32uf,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32ud,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32uzfh,-march=rv32g_zfh -mabi=ilp32))
$(eval $(call compile_template,rv32uzba,-march=rv32g_zba -mabi=ilp32))
$(eval $(call compile_template,rv32uzbb,-march=rv32g_zbb -mabi=ilp32))
$(eval $(call compile_template,rv32uzbc,-march=rv32g_zbc -mabi=ilp32))
$(eval $(call compile_template,rv32uzbs,-march=rv32g_zbs -mabi=ilp32))
$(eval $(call compile_template,rv32si,-march=rv32g -mabi=ilp32))
$(eval $(call compile_template,rv32mi,-march=rv32g -mabi=ilp32))
ifeq ($(XLEN),64)
$(eval $(call compile_template,rv64ui,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64uc,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64um,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64ua,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64uf,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64ud,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64uzfh,-march=rv64g_zfh -mabi=lp64))
$(eval $(call compile_template,rv64uzba,-march=rv64g_zba -mabi=lp64))
$(eval $(call compile_template,rv64uzbb,-march=rv64g_zbb -mabi=lp64))
$(eval $(call compile_template,rv64uzbc,-march=rv64g_zbc -mabi=lp64))
$(eval $(call compile_template,rv64uzbs,-march=rv64g_zbs -mabi=lp64))
$(eval $(call compile_template,rv64mzicbo,-march=rv64g_zicboz -mabi=lp64))
$(eval $(call compile_template,rv64si,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64ssvnapot,-march=rv64g -mabi=lp64))
$(eval $(call compile_template,rv64mi,-march=rv64g -mabi=lp64))
endif

SUITES = rv64ui

$(foreach s, $(SUITES), $(eval $(call compile_template,$(s),-march=rv64g -mabi=lp64)) )

tests_dump = $(addsuffix .dump, $(tests))
tests_bin = $(addsuffix .bin, $(tests))
tests_hex = $(addsuffix .hex, $(tests))
tests_out = $(addsuffix .out, $(filter rv64%,$(tests)))
tests32_out = $(addsuffix .out32, $(filter rv32%,$(tests)))

nemu_out = $(addsuffix .nemu-log, $(tests))
noop_out = $(addsuffix .noop-log, $(tests))

run: $(tests_out) $(tests32_out)

nemu_run: $(tests_dump) $(tests_bin) $(nemu_out)

noop_run: $(tests_dump) $(tests_bin) $(noop_out)

junk = $(build_dir)

#------------------------------------------------------------
# Default

all: $(tests_dump) $(tests_bin)

#------------------------------------------------------------
# Clean up

clean:
	rm -rf $(junk)
