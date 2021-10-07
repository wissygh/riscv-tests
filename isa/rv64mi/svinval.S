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

  li t1 , 1
  li t2 , 2
  li t1 , 1
  li t2 , 2
  li t1 , 1
  li t2 , 2
  li t1 , 1
  li t2 , 2
  sfence.vma
  sfence.vma
  sfence.vma

  li t1 , 1
  li t2 , 2
  li t1 , 1
  li t2 , 2
  li t1 , 1
  li t2 , 2
  li t1 , 1
  li t2 , 2
  
  .word 0b00011000000000000000000001110011 # SFENCE_W_INVAL
  .word 0b00010110000000000000000001110011 # SINVAL_VMA
  .word 0b00010110000000000000000001110011 # SINVAL_VMA
  .word 0b00010110000000000000000001110011 # SINVAL_VMA
  .word 0b00010110000000000000000001110011 # SINVAL_VMA
  .word 0b00010110000000000000000001110011 # SINVAL_VMA
  .word 0b00010110000000000000000001110011 # SINVAL_VMA
  .word 0b00010110000000000000000001110011 # SINVAL_VMA
  .word 0b00010110000000000000000001110011 # SINVAL_VMA
  .word 0b00010110000000000000000001110011 # SINVAL_VMA
  .word 0b00010110000000000000000001110011 # SINVAL_VMA
  .word 0b00011000000100000000000001110011 # SFENCE_INVAL_IR

  RVTEST_PASS

  .align 2
  .global mtvec_handler
mtvec_handler:
  RVTEST_FAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
