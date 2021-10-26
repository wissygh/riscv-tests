# See LICENSE for license details.

#*****************************************************************************
# svinval.S
#-----------------------------------------------------------------------------
#
# Test sfence instructions
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

#define SCRATCH RISCV_PGSIZE
#define OFF 0x100
#define LOW_ACCESS_VADDR (RISCV_PGSIZE + 0x100)
#define HIGH_ACCESS_VADDR (RISCV_PGSIZE * 5 + 0x100)

#define SET_MPRV \
  li a0, MSTATUS_MPRV; \
  csrs mstatus, a0;

#define CLEAR_MPRV \
  li a0, MSTATUS_MPRV; \
  csrc mstatus, a0;

#define MAKE_PTE \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, (PTE_V | PTE_R | PTE_W | PTE_A | PTE_D);

test_begin:

  la a0, mtvec_handler
  csrw mtvec, a0

  la a0, page_table_1
  la a1, page_table_2
  srl a1, a1, 12
  sll a1, a1, PTE_PPN_SHIFT
  ori a1, a1, PTE_V
  sd a1, 0(a0)

  la a0,page_table_2
  la a1,page_table_3
  srl a1, a1, 12
  sll a1, a1, PTE_PPN_SHIFT
  ori a1, a1, PTE_V
  sd a1, 0(a0)

  sfence.vma // flush the level 1GB and level 2MB into dcache
  # set MPP
  li a0, MSTATUS_MPP
  csrc mstatus, a0
  li a0, MSTATUS_MPP & (MSTATUS_MPP >> 1);
  csrs mstatus, a0

  // first, 0x1000-0x1fff mapped to data_page 5
  //        0x5000-0x5fff mapped to data_page 1
  la a0,page_table_3
  la a1,data_page_5
  srl a1, a1, 12
  sll a1, a1, PTE_PPN_SHIFT
  ori a1, a1, (PTE_V | PTE_R | PTE_W | PTE_A | PTE_D)
  sd a1, 8(a0)

  la a1, data_page_1
  srl a1, a1, 12
  sll a1, a1, PTE_PPN_SHIFT
  ori a1, a1, (PTE_V | PTE_R | PTE_W | PTE_A | PTE_D)
  sd a1, 40(a0)

  fence

  la a0, page_table_1
  srl a0, a0, 12
  li a1, -1
  srli a1, a1, (64-44)
  and a0, a0, a1
  li a1, ((8 << 16) + 0)
  sll a1, a1, 44
  or t1, a0, a1
  csrw satp, t1 // satp

  SET_MPRV // ld/st use vaddr now

  li a0, 58
  li a1, LOW_ACCESS_VADDR
  sd a0, 0(a1)

  li a0, 42
  li a1, HIGH_ACCESS_VADDR
  sd a0, 0(a1)

  // store 58 to va 0x1100, pa 0x5100
  CLEAR_MPRV
  li gp, 1
  la a0, data_page_1
  ld a1, OFF(a0)
  li a0, 42
  bne a0, a1, die

  li gp, 2
  la a0, data_page_5
  ld a1, OFF(a0)
  li a0, 58
  bne a0, a1, die


  la a0, page_table_3
  la a1, data_page_1
  MAKE_PTE
  sd a1, 8(a0)

  la a1, data_page_2
  MAKE_PTE
  sd a1, 16(a0)

  la a1, data_page_3
  MAKE_PTE
  sd a1, 24(a0)

  la a1, data_page_4
  MAKE_PTE
  sd a1, 32(a0)

  la a1, data_page_5
  MAKE_PTE
  sd a1, 40(a0)

  la a1, data_page_6
  MAKE_PTE
  sd a1, 48(a0)

  la a1, data_page_7
  MAKE_PTE
  sd a1, 56(a0)

  la a1, data_page_8
  MAKE_PTE
  sd a1, 64(a0)

  SET_MPRV

  li x1, LOW_ACCESS_VADDR
  li x2, (LOW_ACCESS_VADDR + RISCV_PGSIZE * 1)
  li x3, (LOW_ACCESS_VADDR + RISCV_PGSIZE * 2)
  li x4, (LOW_ACCESS_VADDR + RISCV_PGSIZE * 3)
  li x5, (LOW_ACCESS_VADDR + RISCV_PGSIZE * 4)
  li x6, (LOW_ACCESS_VADDR + RISCV_PGSIZE * 5)
  li x7, (LOW_ACCESS_VADDR + RISCV_PGSIZE * 6)
  li x8, (LOW_ACCESS_VADDR + RISCV_PGSIZE * 7)
  li x9, (LOW_ACCESS_VADDR + RISCV_PGSIZE * 8)

  .word 0b00011000000000000000000001110011 # SFENCE_W_INVAL
  .word 0b00010110000000001000000001110011 # SINVAL_VMA x1
  .word 0b00010110000000010000000001110011 # SINVAL_VMA x2
  .word 0b00010110000000011000000001110011 # SINVAL_VMA x3
  .word 0b00010110000000100000000001110011 # SINVAL_VMA x4
  .word 0b00010110000000110000000001110011 # SINVAL_VMA x6
  .word 0b00010110000000111000000001110011 # SINVAL_VMA x7
  .word 0b00010110000001000000000001110011 # SINVAL_VMA x8
  .word 0b00010110000001001000000001110011 # SINVAL_VMA x9
  .word 0b00010110000001001000000001110011 # SINVAL_VMA x9
  .word 0b00010110000000110000000001110011 # SINVAL_VMA x6
  .word 0b00010110000000111000000001110011 # SINVAL_VMA x7
  .word 0b00010110000001000000000001110011 # SINVAL_VMA x8
  .word 0b00010110000001001000000001110011 # SINVAL_VMA x9
  .word 0b00010110000001001000000001110011 # SINVAL_VMA x9
  .word 0b00010110000000110000000001110011 # SINVAL_VMA x6
  .word 0b00010110000000111000000001110011 # SINVAL_VMA x7
  .word 0b00010110000001001000000001110011 # SINVAL_VMA x9
  .word 0b00010110000001001000000001110011 # SINVAL_VMA x9
  .word 0b00010110000000110000000001110011 # SINVAL_VMA x6
  .word 0b00010110000000111000000001110011 # SINVAL_VMA x7
  .word 0b00010110000001000000000001110011 # SINVAL_VMA x8
  .word 0b00010110000001001000000001110011 # SINVAL_VMA x9
  .word 0b00010110000001001000000001110011 # SINVAL_VMA x9
  .word 0b00010110000000110000000001110011 # SINVAL_VMA x6
  .word 0b00010110000000111000000001110011 # SINVAL_VMA x7
  .word 0b00010110000001000000000001110011 # SINVAL_VMA x8
  .word 0b00010110000001000000000001110011 # SINVAL_VMA x8
  .word 0b00010110000001001000000001110011 # SINVAL_VMA x9
  .word 0b00010110000001001000000001110011 # SINVAL_VMA x9
  .word 0b00010110000000101000000001110011 # SINVAL_VMA x5
  .word 0b00011000000100000000000001110011 # SFENCE_INVAL_IR

  li gp, 3
  li a0, 58
  li a1, HIGH_ACCESS_VADDR
  ld a1, (a1)
  bne a0, a1, die

  li gp, 4
  li a0, 42
  li a1, LOW_ACCESS_VADDR
  ld a1, (a1)
  bne a0, a1, die

  csrw 0x5c4, x0 // clear svinval csr
  fence // flush pipe

  li gp, 5
  li tp, 1
  .word 0b00011000000000000000000001110011 # SFENCE_W_INVAL
  bne tp, zero, die

  li gp, 6
  li tp, 1
  .word 0b00010110000000001000000001110011 # SINVAL_VMA x1
  bne tp, zero, die

  li gp, 7
  li tp, 1
  .word 0b00011000000100000000000001110011 # SFENCE_INVAL_IR
  bne tp, zero, die
  j success

fail:
  RVTEST_FAIL

success:
  RVTEST_PASS

  .align 2
  .global mtvec_handler
mtvec_handler:
  beq tp, zero, die
  mv tp, zero
  li a1, 2
  csrr a0, mcause
  bne a0, a1, die
  csrr a1, mepc
  addi a1, a1, 4
  jr a1

die:
  RVTEST_FAIL

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
data_page_1: .dword 0
.align 12
data_page_2: .dword 0
.align 12
data_page_3: .dword 0
.align 12
data_page_4: .dword 0
.align 12
data_page_5: .dword 0
.align 12
data_page_6: .dword 0
.align 12
data_page_7: .dword 0
.align 12
data_page_8: .dword 0
.align 12
data_page_9: .dword 0
.align 12
data_page_10: .dword 0
.align 12
data_page_11: .dword 0
.align 12
data_page_12: .dword 0
.align 12
data_page_13: .dword 0
.align 12
data_page_14: .dword 0
.align 12
data_page_15: .dword 0
.align 12
data_page_16: .dword 0
.align 12
data_page_17: .dword 0
.align 12
data_page_18: .dword 0
.align 12
data_page_19: .dword 0

RVTEST_DATA_END
