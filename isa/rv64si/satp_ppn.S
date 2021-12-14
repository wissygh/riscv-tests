# See LICENSE for license details.

#*****************************************************************************
# satp_ppn.S
#-----------------------------------------------------------------------------
#
# Test write satp.ppn that large than PADDRBITS
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64S
RVTEST_CODE_BEGIN

#ifdef __MACHINE_MODE
  #define sscratch mscratch
  #define sstatus mstatus
  #define scause mcause
  #define sbadaddr mbadaddr
  #define sepc mepc
  #define sret mret
  #define stvec_handler mtvec_handler
#endif

  .align 2
  .option norvc

#define PADDRBITS 36

test_code_begin:

li a0, 0x00000FFFFFFFFFFFUL
li a1, 0x0000000000FFFFFFUL
csrrw a2, satp, a0
csrr a2, satp

// satp's ppn should be masked by PADDTBITS
beq a2, a1, ohyeah

RVTEST_FAIL

ohyeah:

RVTEST_PASS

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
