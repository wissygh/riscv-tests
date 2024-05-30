
# See LICENSE for license details.

#*****************************************************************************
# loadTrigger.S
#-----------------------------------------------------------------------------
#
# Test loadTrigger, if they are implemented.
#

#include "riscv_test.h"
#include "test_macros.h"
RVTEST_RV64M
RVTEST_CODE_BEGIN

  li TESTNUM, 2 #末尾会判断gp和0的关系

  csrw tcontrol, 8
  # triggr adder
  la t2, data1

  # store trigger
  csrw tselect, 0
  csrw tdata2, t2
  li t1, (2 << (__riscv_xlen - 4)) | MCONTROL_M | MCONTROL_STORE
  csrw tdata1, t1

  li a1, 0xffffffff
  SW a1, 0(t2)

  # load trigger
  csrw tselect, 1
  csrw tdata2, t2
  li t1, (2 << (__riscv_xlen - 4)) | MCONTROL_M | MCONTROL_LOAD 
  csrw tdata1, t1

  LWU a2, 0(t2)

  bne a1, a2, fail
  TEST_PASSFAIL

  .align 2
  .global mtvec_handler

mtvec_handler:
  # Only even-numbered tests should trap.
  li t0, CAUSE_BREAKPOINT
  csrr t1, mcause
  bne t0, t1, fail

  # mret
  csrw tdata1, x0
  mret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
 .align 4
 TEST_DATA

data1: .word 0

RVTEST_DATA_END
