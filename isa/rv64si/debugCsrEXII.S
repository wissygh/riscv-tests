# See LICENSE for license details.

#*****************************************************************************
# debugCsrEXII.S
#-----------------------------------------------------------------------------
#
# Test syscall trap.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64S
RVTEST_CODE_BEGIN

#ifdef __MACHINE_MODE
  #define sscratch mscratch
  #define sstatus mstatus
  #define scause mcause
  #define sepc mepc
  #define sret mret
  #define stvec_handler mtvec_handler
#endif

  li TESTNUM, 2

test_csr:
  csrw dcsr, 0
  csrw dpc, 0
  csrw dscratch0, 0
  csrw dscratch1, 0
  
  csrr t0, dcsr
  csrr t0, dpc
  csrr t0, dscratch0

test_last:
  csrr t0, dscratch1
  
  la t0, test_last
  bne t0, t2, fail //说明我测试跑到了最后一条

  TEST_PASSFAIL

  .align 4
  .global stvec_handler
stvec_handler:
  li t1, CAUSE_ILLEGAL_INSTRUCTION
  csrr t0, scause
  bne t0, t1, fail

  csrr t0, sepc
  csrr t2, sepc
  addi t0, t0, 4
  csrw sepc, t0
  sret



# write_tselect:
#   csrw tselect, 0
#   j fail

#   TEST_PASSFAIL

#   .align 4
#   .global stvec_handler
# stvec_handler:
#   li t1, CAUSE_ILLEGAL_INSTRUCTION
#   csrr t0, scause
#   bne t0, t1, fail
#   la t1, write_tselect
#   csrr t0, sepc
#   bne t0, t1, fail
#   j pass

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
