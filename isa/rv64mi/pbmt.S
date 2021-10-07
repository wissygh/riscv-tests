# See LICENSE for license details.

#*****************************************************************************
# pbmt.S
#-----------------------------------------------------------------------------
#
# Test pbmt and asid bits 
#

#include "riscv_test.h"
#include "test_macros.h"


RVTEST_RV64M
RVTEST_CODE_BEGIN

# Construct the page table

#define MY_VA 0x40201010
  # VPN 2 == VPN 1 == VPN 0 == 0x1
  # Page offset == 0x10

  # Level 0 PTE contents

  # PPN
  la a0, my_data
  srl a0, a0, 12

  # attributes
  sll a0, a0, PTE_PPN_SHIFT
  li a1, PTE_V | PTE_R | PTE_W | PTE_X | PTE_A | PTE_D | PTE_N | PTE_PBMT_TWO
  or a0, a0, a1

  # Level 0 PTE address
  la a1, page_table
  addi a1, a1, ((MY_VA >> 12) & 0x1FF) * 8

  # Level 0 PTE store
  sd a0, (a1)


  # Level 1 PTE contents
  la a0, page_table
  srl a0, a0, 12
  sll a0, a0, PTE_PPN_SHIFT
  li a1, PTE_V
  or a0, a0, a1

  # Level 1 PTE address
  la a1, page_table
  addi a1, a1, ((MY_VA >> 21) & 0x1FF) * 8
  li a2, 1 << 12
  add a1, a1, a2

  # Level 1 PTE store
  sd a0, (a1)

  ####

  # Level 2 PTE contents
  la a0, page_table
  li a1, 1 << 12
  add a0, a0, a1
  srl a0, a0, 12
  sll a0, a0, PTE_PPN_SHIFT
  li a1, PTE_V
  or a0, a0, a1

  # Level 2 PTE address
  la a1, page_table
  addi a1, a1, ((MY_VA >> 30) & 0x1FF) * 8
  li a2, 2 << 12
  add a1, a1, a2

  # Level 2 PTE store
  sd a0, (a1)

  ####

  ####
  li TESTNUM, 1

  ## Turn on VM
  la a1, page_table
  li a2, 2 << 12
  add a1, a1, a2
  srl a1, a1, 12
  li a0, (SATP_MODE & ~(SATP_MODE<<1)) * SATP_MODE_SV39
  or a0, a0, a1
  csrw satp, a0
  sfence.vma

  # Set up MPRV with MPP=S and SUM=1, so loads and stores use S-mode and S can access U pages
  # li a1, ((MSTATUS_MPP & ~(MSTATUS_MPP<<1)) * PRV_S) | MSTATUS_MPRV 
  li a1, MSTATUS_MPRV 
  csrs mstatus, a1
  li a1, MSTATUS_MPP
  csrc mstatus, a1
  li a1, 0x00000800
  csrs mstatus, a1

  # Do a store to MY_VA
  li a0, MY_VA
  li a1, 42
  sw a1, (a0)

  #do test of asid for fun: change asid bits
  la a1, page_table
  li a2, 2 << 12
  add a1, a1, a2
  srl a1, a1, 12
  li t1, 2 << 44 # set asid as 2
  or a1 , a1 , t1
  li a0, (SATP_MODE & ~(SATP_MODE<<1)) * SATP_MODE_SV39
  or a0, a0, a1
  csrw satp, a0
  sfence.vma 

  li a0, MY_VA
  lw a2, (a0)

  # sfence flush tlb who's asid is 2
  li x6, 0
  li x7, 2
  sfence.vma x6, x7

  # Clear MPRV
  li a1, MSTATUS_MPRV
  csrc mstatus, a1

  # Do a load of my_data
  # la a0, my_data
  # srl a0, a0, 12
  # sll a0, a0, 12
  # li t1, MY_VA & 0xFFF
  # or a0, a0, t1
  # lw a2, (a0)

  li t1, 42
  bne a2, t1, die


  # check wave to see pbmt works or not mannually

  RVTEST_PASS

  .align 2
  .global mtvec_handler
mtvec_handler:
die:
  RVTEST_FAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

.align 20
page_table: .dword 0

.align 20
my_data: .dword 0

RVTEST_DATA_END