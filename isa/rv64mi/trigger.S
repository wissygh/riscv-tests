
# See LICENSE for license details.

#*****************************************************************************
# trigger.S
#-----------------------------------------------------------------------------
#
# Test trigger, if they are implemented.
#

#include "riscv_test.h"
#include "test_macros.h"
RVTEST_RV64M
RVTEST_CODE_BEGIN

  li TESTNUM, 2 #末尾会判断gp和0的关系

  csrw tcontrol, 8
  # store chain
  csrw tselect, 0
  la t2, data1
  csrw tdata2, t2
  li t1, (2 << (__riscv_xlen - 4)) | MCONTROL_M | MCONTROL_STORE | (2 << 7) | MCONTROL_CHAIN
  csrw tdata1, t1

  csrw tselect, 1
  la t2, data3
  csrw tdata2, t2
  li t1, (2 << (__riscv_xlen - 4)) | MCONTROL_M | MCONTROL_STORE | (3 << 7)
  csrw tdata1, t1

  la t2, data2
  li a0, 0xffffffff
  SW a0, 0(t2)


  # load chain
  csrw tselect, 0
  la t2, data1
  csrw tdata2, t2
  li t1, (2 << (__riscv_xlen - 4)) | MCONTROL_M | MCONTROL_LOAD | (2 << 7) | MCONTROL_CHAIN
  csrw tdata1, t1

  csrw tselect, 1
  la t2, data3
  csrw tdata2, t2
  li t1, (2 << (__riscv_xlen - 4)) | MCONTROL_M | MCONTROL_LOAD | (3 << 7)
  csrw tdata1, t1

  la t2, data2
  LWU a1, 0(t2)

  bne a1, a0, fail

  TEST_PASSFAIL

  .align 4
  .global mtvec_handler

mtvec_handler:
  # Only even-numbered tests should trap.
  li t0, CAUSE_BREAKPOINT
  csrr t1, mcause
  bne t0, t1, fail

  # mret
  csrw tdata1, x0
  csrw tselect, 0
  csrw tdata1, x0
  mret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
 .align 4
 TEST_DATA

data1: .word 0
data2: .word 0
data3: .word 0

RVTEST_DATA_END
