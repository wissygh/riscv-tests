# See LICENSE for license details.

#*****************************************************************************
# asid.S
#-----------------------------------------------------------------------------
#
# Test asid(now someting is wrong in this test case)
#

#include "riscv_test.h"
#include "test_macros.h"


RVTEST_RV64M
RVTEST_CODE_BEGIN

  # Construct the page table

#define SCRATCH RISCV_PGSIZE
#define SET_MPRV \
  li a0, MSTATUS_MPRV; \
  csrs mstatus, a0;

#define CLEAR_MPRV \
  li a0, MSTATUS_MPRV; \
  csrc mstatus, a0;

  # page table 1 : map 0x1000 - 0x1fff to data_page_1
  la a0,page_table_1_0
  la a1,page_table_1_1
  srl a1, a1, 12
  sll a1, a1, PTE_PPN_SHIFT
  ori a1, a1, PTE_V
  sd a1, 0(a0)

  la a0,page_table_1_1
  la a1,page_table_1_2
  srl a1, a1, 12
  sll a1, a1, PTE_PPN_SHIFT
  ori a1, a1, PTE_V
  sd a1, 0(a0)

  la a0,page_table_1_2
  la a1,data_page_1
  srl a1, a1, 12
  sll a1, a1, PTE_PPN_SHIFT
  ori a1, a1, (PTE_V | PTE_R | PTE_W | PTE_A | PTE_D)
  sd a1, 8(a0)

  # page table 2 : map 0x1000 - 0x1fff to data_page_2
  la a0,page_table_2_0
  la a1,page_table_2_1
  srl a1, a1, 12
  sll a1, a1, PTE_PPN_SHIFT
  ori a1, a1, PTE_V
  sd a1, 0(a0)

  la a0,page_table_2_1
  la a1,page_table_2_2
  srl a1, a1, 12
  sll a1, a1, PTE_PPN_SHIFT
  ori a1, a1, PTE_V
  sd a1, 0(a0)

  la a0,page_table_2_2
  la a1,data_page_2
  srl a1, a1, 12
  sll a1, a1, PTE_PPN_SHIFT
  ori a1, a1, (PTE_V | PTE_R | PTE_W | PTE_A | PTE_D)
  sd a1, 8(a0)

  # set MPP
  li a0, MSTATUS_MPP
  csrc mstatus, a0  
  li a0, MSTATUS_MPP & (MSTATUS_MPP >> 1);
  csrs mstatus, a0 

  la a0, page_table_1_0
  srl a0, a0, 12
  li a1, -1
  srli a1, a1, (64-44)
  and a0, a0, a1
  li a1, ((8 << 16) + 1)
  sll a1, a1, 44
  or t1, a0, a1 // the asid 1 satp

  la a0, page_table_2_0
  srl a0, a0, 12
  li a1, -1
  srli a1, a1, (64-44)
  and a0, a0, a1
  li a1, ((8 << 16) + 2)
  sll a1, a1, 44
  or t2, a0, a1 // the asid 2 satp

  # change to asid 1
  csrw satp, t1

  SET_MPRV
  # sw 58 to 0x1108
  li a0, 0x1100
  li a1, 58
  sw a1, 8(a0)

  # change to asid 2
  csrw satp, t2
  # lw 0x1108, should not equal
  li a0, 0x1100
  li a1, 58
  lw a0, 8(a0)
  beq a0, a1, fail
  # sw 42 to 0x1108
  li a0, 0x1100
  li a1, 42
  sw a1, 8(a0)

  # change to asid 1
  csrw satp, t1
  # lw 0x1108, should equal to 58, not 42
  li a0, 0x1100
  lw a0, 8(a0)
  li a1, 58
  li a1, 42
  beq a0, a1, fail
  li a1, 58
  beq a0, a1, success
  
fail:
  RVTEST_FAIL

success:
  RVTEST_PASS

  .align 2
  .global mtvec_handler
mtvec_handler:
die:
  RVTEST_FAIL

RVTEST_CODE_END

  .data

.align 12
page_table_1_0: .dword 0

.align 12
page_table_1_1: .dword 0

.align 12
page_table_1_2: .dword 0

.align 12
data_page_1: .dword 0

.align 12
page_table_2_0: .dword 0

.align 12
page_table_2_1: .dword 0

.align 12
page_table_2_2: .dword 0

.align 12
data_page_2: .dword 0

RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END