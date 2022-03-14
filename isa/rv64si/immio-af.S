
# See LICENSE for license details.

#*****************************************************************************
# immio-af.S
#-----------------------------------------------------------------------------
#
# test mmio instruction, low part is mmio(flash), high part is not mmio(ddr)
# see if the core blocked or not
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

# Brother test of the immio
# what the test do:
# xs starts from flash(0x1000_0000), which is mmio, then jumps to 0x8000_0000(this test)
# this test will establish a page table, one page to flash, one page to ddr
# then jump to the tail of flash, the mmio instruction will be divided into mmio and ddr part.
# But we remove flash's execute right, then jump to then same addr, trap_handler will take control.
# In the trap_handler, good trap


#define FLASH_ADDR 0x10000000
#define FLASH_TAIL (FLASH_ADDR + RISCV_PGSIZE - 2) # flash makes sure this will a part of instruction(not C)
#define DDR_ADDR data_page

#define MAKE_PDE \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, PTE_V;

#define MAKE_PTE \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, (PTE_V | PTE_R | PTE_W | PTE_A | PTE_D | PTE_X);



test_begin:
  la a0, mtvec_handler
  csrw mtvec, a0
  # vaddr start from 0

  la a0, page_table_1
  la a1, page_table_2
  MAKE_PDE
  sd a1, 0(a0)

  la a0, page_table_2
  la a1, page_table_3
  MAKE_PDE
  sd a1, 0(a0)

  la a0, page_table_3
  li a1, FLASH_ADDR
  MAKE_PTE
  sd a1, 0(a0)

  la a0, page_table_3
  la a1, DDR_ADDR
  MAKE_PTE
  sd a1, 8(a0)

  # make map for current addr which should in 0x8000_0000
  la a0, page_table_1
  li a1, 0x80000000
  MAKE_PTE
  sd a1, 16(a0)

  # jump to dest addr
  sfence.vma

  la a0, page_table_1
  srl a0, a0, 12
  li a1, -1
  srli a1, a1, (64-44)
  and a0, a0, a1
  li a1, ((8 << 16) + 0)
  sll a1, a1, 44
  or t1, a0, a1
  csrw satp, t1 // set satp, now m mode, so not virtual

  la a0, virtual_begin
  csrw mepc, a0
  li a0, MSTATUS_MPP
  csrc mstatus, a0
  li a0, MSTATUS_MPP & (MSTATUS_MPP >> 1)
  csrs mstatus, a0

  # remove flash's x right
  li a0, ((0x10000000 + (0x100/2 -1)) >> 2)
  csrw pmpaddr1, a0
  csrr a0, pmpcfg0
  ori a0, a0, (31-4)
  csrw pmpcfg0, a0

  sfence.vma
  li a0, 42 # good trap magic number

  mret

virtual_begin:
  # li a0, FLASH_TAIL
  li a1, (0x1000-2)
  jr a1

mtvec_handler:
  li a1, 42
  bne a0, a1, die
  csrr a0, mcause
  li a1, 1 # iaf
  beq a0, a1, success


die:
  RVTEST_FAIL

success:

RVTEST_CODE_END

    .data

RVTEST_DATA_BEGIN

  TEST_DATA

.align 12
page_table_1: .dword 0
.align 12
page_table_2: .dword 0
.align 12
page_table_3: .dword 0
.align 12
data_page: .dword 0