# See LICENSE for license details.

#*****************************************************************************
# ma_addr.S
#-----------------------------------------------------------------------------
#
# Test misaligned ld/st trap.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

.align 2
.option norvc

la a0, s_mode_exec
csrrw a1, mepc, a0

la a0, ss_mode_exec
csrrw a1, sepc, a0

# set mstatus.mprv
li a0, MSTATUS_MPRV
csrrc a1, mstatus, a0
csrrs a1, mstatus, a0

# set mpp
li a0, MSTATUS_MPP
csrrc a1, mstatus, a0
li a0, MSTATUS_MPP & (MSTATUS_MPP >> 1)
csrrs a1, mstatus, a0

# mret to s mode
mret

s_mode_exec:

# set sstatus.spp
li a0, MSTATUS_SPP
csrrs a1, sstatus, a0

# sret to s-mode
la a0, ss_mode_exec
csrrw a1, sepc, a0
sret

ss_mode_exec:

csrr a1, sstatus

RVTEST_PASS

# mtvec handler
mtvec_handler:
  RVTEST_FAIL

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END