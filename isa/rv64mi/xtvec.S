
#*****************************************************************************
# illegal.S
#-----------------------------------------------------------------------------
#
# Test vectorized handler
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  .align 2
  .option norvc

  j test_begin

mtvec_handler:
  j synchronous_exception
  j m_ssip_handler
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail

stvec_handler:
  j synchronous_exception
  j s_ssip_handler
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail
  j fail

m_ssip_handler:
  csrr t0, mcause
  li   t2, (1 << 63)
  and  t3, t2, t0       # get msb
  beqz t3, fail         # is not interrupt?
  xor  t0, t2, t0       # clear msb
  li   t1, IRQ_S_SOFT   # machine software interrupt
  bne  t0, t1, fail     # is not msi?

  csrci mip, MIP_SSIP   # clear SSIP

  csrr t0, mepc
  addi t0, t0, 4        # skip j fail
  csrw mepc, t0
  mret                  # end if m_ssip_handler

s_ssip_handler:
  csrr t0, scause
  li   t2, (1 << 63)
  and  t3, t2, t0       # get msb
  beqz t3, fail         # is not interrupt?
  xor  t0, t2, t0       # clear msb
  li   t1, IRQ_S_SOFT   # machine software interrupt
  bne  t0, t1, fail     # is not msi?

  csrci sip, SIP_SSIP   # clear SSIP

  csrr t0, sepc
  addi t0, t0, 4        # skip j fail
  csrw sepc, t0
  sret                  # end if m_ssip_handler

synchronous_exception:
  li t1, CAUSE_ILLEGAL_INSTRUCTION
  csrr t0, mcause
  bne t0, t1, fail
  csrr t0, mepc

  # Make sure mtval contains either 0 or the instruction word.
  csrr t2, mbadaddr
  beqz t2, 1f
  lhu t1, 0(t0)
  xor t2, t2, t1
  lhu t1, 2(t0)
  slli t1, t1, 16
  xor t2, t2, t1
  bnez t2, fail
1:
  addi t0, t0, 8
  csrw mepc, t0
  mret

test_begin:
  # Test vectored interrupts if they are supported.
test_1:                             # vectored_interrupts test
  csrwi mip, MIP_SSIP
  csrwi mie, MIP_SSIP
  la t0, mtvec_handler + 1
  csrrw s0, mtvec, t0               # set vectored interrupt handler
  csrr t0, mtvec
  andi t0, t0, 1
  beqz t0, test_1_done              # if not support vectored interrupt handler
  csrsi mstatus, MSTATUS_MIE        # enable m mode interrupt

1:
  j 1b
test_1_done:
  csrw mtvec, s0                    # resume old mtvec
  
test_2:                             # illegal instruction test
  la t0, mtvec_handler + 1
  csrrw s0, mtvec, t0               # set vectored interrupt handler
  csrr t0, mtvec
  andi t0, t0, 1
  beqz t0, test_2_done              # if not support vectored interrupt handler
  .word 0
  j fail

test_2_done:
  csrw mtvec, s0                    # resume old mtvec

  csrsi mstatus, MSTATUS_MIE        # enable interrupt
  csrwi mideleg, MIP_SSIP           # SSIP interrupt can be handled in S mode
  la t0, test_3
  csrw mepc, t0
  li t0, MSTATUS_MPP
  csrc mstatus, t0
  li t1, (MSTATUS_MPP & -MSTATUS_MPP) * PRV_S
  csrs mstatus, t1
  mret                              # entry S mode

test_3:
  # now hart in S mode

  la t0, stvec_handler + 1
  csrrw s0, stvec, t0               # set vectored interrupt handler
  csrr t0, stvec
  andi t0, t0, 1
  beqz t0, test_1_done              # if not support vectored interrupt handler
  csrwi sie, SIP_SSIP
  csrwi sip, SIP_SSIP               # raise S mode software interrupt
  csrsi sstatus, SSTATUS_SIE        # enable m mode interrupt
1:
  j 1b

test_3_done:
  csrw stvec, s0                    # resume old mtvec

  j pass

TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
