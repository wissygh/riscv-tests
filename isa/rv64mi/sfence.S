# See LICENSE for license details.

#*****************************************************************************
# sfence.S
#-----------------------------------------------------------------------------
#
# Test asid and sfence
# L1 TLB and L2 TLB have different methods to deal with sfence
# So you should use macro definition to control tests
#

//#define ASID_L2TLB 1

#ifndef ASID_L2TLB
  #define ASID_L1TLB 1
#endif

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

#define SET_MPP \
  li a0, MSTATUS_MPP; \
  csrc mstatus, a0; \
  li a0, MSTATUS_MPP & (MSTATUS_MPP >> 1); \
  csrs mstatus, a0;

#define MAKE_PGD \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, (PTE_V);

#define MAKE_PGD_UNVALID \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, 0;

#define MAKE_PGD_GLOBAL \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, (PTE_V | PTE_G);

#define MAKE_PMD \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, (PTE_V);

#define MAKE_PMD_UNVALID \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, 0;

#define MAKE_PMD_GLOBAL \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, (PTE_V | PTE_G);

#define MAKE_PTE \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, (PTE_V | PTE_R | PTE_W | PTE_A | PTE_D);

#define MAKE_PTE_UNVALID \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, (PTE_R | PTE_W | PTE_A | PTE_D);

#define MAKE_PTE_GLOBAL \
  srl a1, a1, 12; \
  sll a1, a1, PTE_PPN_SHIFT; \
  ori a1, a1, (PTE_V | PTE_R | PTE_W | PTE_G | PTE_A | PTE_D);

#define MAKE_ASID(asid) \
  srl a0, a0, 12; \
  li a1, -1; \
  srli a1, a1, (64-44); \
  and a0, a0, a1; \
  li a1, ((8 << 16) + asid); \
  sll a1, a1, 44;

asid_test_begin:

  # page table 1 : map 0x201000 - 0x201fff to data_page_1
  la a0,page_table_1_0
  la a1,page_table_1_1
  MAKE_PGD
  sd a1, 0(a0)

  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD
  sd a1, 8(a0)

  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE
  sd a1, 8(a0)

  # page table 2 : map 0x201000 - 0x201fff to data_page_2
  la a0,page_table_2_0
  la a1,page_table_2_1
  MAKE_PGD
  sd a1, 0(a0)

  la a0,page_table_2_1
  la a1,page_table_2_2
  MAKE_PMD
  sd a1, 8(a0)

  la a0,page_table_2_2
  la a1,data_page_2
  MAKE_PTE
  sd a1, 8(a0)

  # page table 3 : map 0x200000 - 0x3fffff to data_page_3
  la a0,page_table_3_0
  la a1,page_table_3_1
  MAKE_PGD
  sd a1, 0(a0)

  la a0,page_table_3_1
  la a1,data_page_3
  MAKE_PTE
  sd a1, 8(a0)

  # page table 4 : map 0x200000 - 0x3fffff to data_page_4
  la a0,page_table_4_0
  la a1,page_table_4_1
  MAKE_PGD
  sd a1, 0(a0)

  la a0,page_table_4_1
  la a1,data_page_4
  MAKE_PTE
  sd a1, 8(a0)

  # page table 5 : map 0x0 - 0x3fffffff to data_page_5
  la a0,page_table_5_0
  la a1,data_page_5
  MAKE_PTE
  sd a1, 0(a0)

  fence

  SET_MPP

  la a0, page_table_1_0
  MAKE_ASID(1)
  or t1, a0, a1 // the asid 1 satp

  la a0, page_table_2_0
  MAKE_ASID(2)
  or t2, a0, a1 // the asid 2 satp

  la a0, page_table_3_0
  MAKE_ASID(3)
  or t3, a0, a1 // the asid 3 satp

  la a0, page_table_4_0
  MAKE_ASID(4)
  or t4, a0, a1 // the asid 4 satp

  la a0, page_table_5_0
  MAKE_ASID(5)
  or t5, a0, a1 // the asid 4 satp

  SET_MPRV

asid_should_not_equal:

  # change to asid 1
  csrw satp, t1
  # sw 1111 to 0x201108
  li a0, 0x201100
  li a1, 1111
  sw a1, 8(a0)

  # change to asid 2
  csrw satp, t2
  # lw 0x201108, should equal to 0
  li a0, 0x201100
  li a1, 0
  lw a0, 8(a0)
  bne a0, a1, fail
  # sw 2222 to 0x201108
  li a0, 0x201100
  li a1, 2222
  sw a1, 8(a0)

  # change to asid 3
  csrw satp, t3
  # lw 0x201108, should equal to 0
  li a0, 0x201100
  li a1, 0
  lw a0, 8(a0)
  bne a0, a1, fail
  # sw 3333 to 0x201108
  li a0, 0x201100
  li a1, 3333
  sw a1, 8(a0)

  # change to asid 4
  csrw satp, t4
  # lw 0x201108, should equal to 0
  li a0, 0x201100
  li a1, 0
  lw a0, 8(a0)
  bne a0, a1, fail
  # sw 4444 to 0x201108
  li a0, 0x201100
  li a1, 4444
  sw a1, 8(a0)

  # change to asid 5
  csrw satp, t5
  # lw 0x201108, should equal to 0
  li a0, 0x201100
  li a1, 0
  lw a0, 8(a0)
  bne a0, a1, fail
  # sw 5555 to 0x201108
  li a0, 0x201100
  li a1, 5555
  sw a1, 8(a0)

asid_should_equal:

  # change to asid 1
  csrw satp, t1
  # lw 0x201108, should equal to 1111
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # change to asid 2
  csrw satp, t2
  # lw 0x201108, should equal to 2222
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  # change to asid 3
  csrw satp, t3
  # lw 0x201108, should equal to 3333
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  # change to asid 4
  csrw satp, t4
  # lw 0x201108, should equal to 4444
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 4444
  bne a0, a1, fail

  # change to asid 5
  csrw satp, t5
  # lw 0x201108, should equal to 5555
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 5555
  bne a0, a1, fail

asid_test_end:

  fence
  j sfence_test_begin

sfence_test_begin:

  j before_sfence_1GB

before_sfence_1GB:

  # change to asid 1
  csrw satp, t1

  # lw 0x201108, in order to refill 0x201108 to Page Cache
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  j sfence_1GB_1

sfence_1GB_1:

  CLEAR_MPRV
  # remap 0x40201000 - 0x40201fff to data_page_1
  la a0,page_table_1_0
  la a1,page_table_1_1
  MAKE_PGD
  sd a1, 8(a0)
  # remap 0x201000 - 0x201fff to data_page_2
  la a0,page_table_1_0
  la a1,page_table_2_1
  MAKE_PGD
  sd a1, 0(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x201108, should equal to 1111
  # 0x201108 is in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: sfence other asid
  # only sfence asid 0, not current asid
  li x1, 0
  sfence.vma x0, x1

  # lw 0x40201108, should equal to 1111
  # 0x40201108 is not in Page Cache, need a request to mem
  li a0, 0x40201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 is still in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 3: sfence other asid
  # only sfence asid 2, not current asid
  li x1, 2
  sfence.vma x0, x1

  # lw 0x40201108, should equal to 1111
  # 0x40201108 is in Page Cache now
  li a0, 0x40201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 is still in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 4: sfence current asid
  # only sfence asid 1, is current asid
  li x1, 1
  sfence.vma x0, x1

  # lw 0x40201108, should equal to 1111
  # 0x40201108 has been flushed, need a request to mem
  li a0, 0x40201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  j sfence_1GB_2

sfence_1GB_2:

  CLEAR_MPRV
  # remap 0x201000 - 0x201fff to data_page_1
  la a0,page_table_1_0
  la a1,page_table_1_1
  MAKE_PGD
  sd a1, 0(a0)
  # remap 0x40201000 - 0x40201fff to data_page_2
  la a0,page_table_1_0
  la a1,page_table_2_1
  MAKE_PGD
  sd a1, 8(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x40201108, should equal to 1111
  # 0x40201108 is in Page Cache now
  li a0, 0x40201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: sfence all asid
  sfence.vma x0, x0

  # lw 0x40201108, should equal to 2222
  # 0x40201108 has been flushed, need a request to mem
  li a0, 0x40201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  j sfence_1GB_3

sfence_1GB_3:

  CLEAR_MPRV
  # remap 0x40201000 - 0x40201fff to data_page_1 with global
  la a0,page_table_1_0
  la a1,page_table_1_1
  MAKE_PGD_GLOBAL
  sd a1, 8(a0)
  # remap 0x201000 - 0x201fff to data_page_2
  la a0,page_table_1_0
  la a1,page_table_2_1
  MAKE_PGD
  sd a1, 0(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x201108, should equal to 1111
  # 0x201108 is in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: refill global entry to Page Cache
  # sfence all asid
  sfence.vma x0, x0

  # lw 0x40201108, should equal to 1111
  # 0x40201108 has been flushed, need a request to mem
  # refill 0x40201108 to Page Cache with global
  li a0, 0x40201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  # refill 0x201108 to Page Cache
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  CLEAR_MPRV
  # remap 0x201000 - 0x201fff to data_page_1
  la a0,page_table_1_0
  la a1,page_table_1_1
  MAKE_PGD
  sd a1, 0(a0)
  # remap 0x40201000 - 0x40201fff to data_page_2
  la a0,page_table_1_0
  la a1,page_table_2_1
  MAKE_PGD
  sd a1, 8(a0)
  SET_MPRV

  # 3: before sfence
  # lw 0x40201108, should equal to 1111
  # 0x40201108 is still in Page Cache now
  li a0, 0x40201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 4: sfence current asid, but without global
  # only sfence asid 1, is current asid
  li x1, 1
  sfence.vma x0, x1

  # lw 0x40201108, should equal to 1111
  # 0x40201108 is global, should not be flushed
  li a0, 0x40201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # 5: sfence all asid
  sfence.vma x0, x0

  # lw 0x40201108, should equal to 2222
  # 0x40201108 has been flushed, need a request to mem
  li a0, 0x40201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  j before_sfence_2MB

before_sfence_2MB:

  CLEAR_MPRV

  # map 0x201000 - 0x201fff to data_page_1
  la a0,page_table_1_0
  la a1,page_table_1_1
  MAKE_PGD
  sd a1, 0(a0)

  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD
  sd a1, 8(a0)

  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE
  sd a1, 8(a0)

  # clear map 0x40201000 - 0x40201fff
  la a0,page_table_1_0
  la a1,page_table_1_1
  MAKE_PGD_UNVALID
  sd a1, 8(a0)

  SET_MPRV

  sfence.vma x0, x0

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  # refill 0x201108 to Page Cache
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  j sfence_2MB_1

sfence_2MB_1:

  CLEAR_MPRV
  # remap 0x401000 - 0x401fff to data_page_1
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD
  sd a1, 16(a0)
  # remap 0x201000 - 0x201fff to data_page_2
  la a0,page_table_1_1
  la a1,page_table_2_2
  MAKE_PMD
  sd a1, 8(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x201108, should equal to 1111
  # 0x201108 is in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: sfence other asid
  # only sfence asid 0, not current asid
  # However, Page Cache will flush all 2MB Pages with any asid
  # So 0x201108 will not be in Page Cache
  # But will still be in L1 TLB
  li x1, 0
  sfence.vma x0, x1

  # lw 0x401108, should equal to 1111
  # 0x401108 is not in Page Cache, need a request to mem
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

#ifdef ASID_L2TLB
  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail
#endif

#ifdef ASID_L1TLB
  # lw 0x201108, should equal to 1111
  # 0x201108 is still in L1 TLB
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail
#endif

  # 3: sfence other asid
  # only sfence asid 0, not current asid
  # However, Page Cache will flush all 2MB Pages with any asid
  # So 0x201108 will not be in Page Cache
  # But will still be in L1 TLB
  li x1, 2
  sfence.vma x0, x1

  # lw 0x401108, should equal to 1111
  # 0x401108 is not in Page Cache, need a request to mem
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

#ifdef ASID_L2TLB
  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail
#endif

#ifdef ASID_L1TLB
  # lw 0x201108, should equal to 1111
  # 0x201108 is still in L1 TLB
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail
#endif

  fence

  # 4: sfence current asid
  # only sfence asid 1, is current asid
  # However, Page Cache will flush all 2MB Pages with any asid
  # So 0x201108 will not be in Page Cache
  # Is current asid, 0x201108 will also be flushed from L1 TLB
  li x1, 1
  sfence.vma x0, x1

  # lw 0x401108, should equal to 1111
  # 0x401108 is not in Page Cache, need a request to mem
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  fence

  j sfence_2MB_2

sfence_2MB_2:

  CLEAR_MPRV
  # remap 0x201000 - 0x201fff to data_page_1
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD
  sd a1, 8(a0)
  # remap 0x401000 - 0x401fff to data_page_2
  la a0,page_table_1_1
  la a1,page_table_2_2
  MAKE_PMD
  sd a1, 16(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x401108, should equal to 1111
  # 0x401108 is in Page Cache now
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: sfence all asid
  sfence.vma x0, x0

  # lw 0x401108, should equal to 2222
  # 0x401108 has been flushed, need a request to mem
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  j sfence_2MB_3

sfence_2MB_3:

  CLEAR_MPRV
  # remap 0x401000 - 0x401fff to data_page_1 with global
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_GLOBAL
  sd a1, 16(a0)
  # remap 0x201000 - 0x201fff to data_page_2
  la a0,page_table_1_1
  la a1,page_table_2_2
  MAKE_PMD
  sd a1, 8(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x201108, should equal to 1111
  # 0x201108 is in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: refill fake-global entry to Page Cache
  # sfence all asid
  sfence.vma x0, x0

  # lw 0x401108, should equal to 1111
  # 0x401108 has been flushed, need a request to mem
  # refill 0x401108 to Page Cache
  # However, 2MB entry in Page Cache need 8-consecutive entries to be global
  # So in fact it is not global in Page Cache
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  # refill 0x201108 to Page Cache
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  CLEAR_MPRV
  # remap 0x201000 - 0x201fff to data_page_1
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD
  sd a1, 8(a0)
  # remap 0x401000 - 0x401fff to data_page_2
  la a0,page_table_1_1
  la a1,page_table_2_2
  MAKE_PMD
  sd a1, 16(a0)
  SET_MPRV

  # 3: before sfence
  # lw 0x401108, should equal to 1111
  # 0x401108 is still in Page Cache now
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 4: sfence current asid, but without global
  # only sfence asid 1, is current asid
  li x1, 1
  sfence.vma x0, x1

  # lw 0x401108, should equal to 2222
  # 0x401108 is fake-global, has been flushed, need a request to mem
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  j sfence_2MB_4

sfence_2MB_4:

  CLEAR_MPRV
  # remap 0x1000 - 0x1fff to data_page_1 with global
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_GLOBAL
  sd a1, 0(a0)
  # remap 0x201000 - 0x201fff to data_page_1 with global
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_GLOBAL
  sd a1, 8(a0)
  # remap 0x401000 - 0x401fff to data_page_1 with global
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_GLOBAL
  sd a1, 16(a0)
  # remap 0x601000 - 0x601fff to data_page_1 with global
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_GLOBAL
  sd a1, 24(a0)
  # remap 0x801000 - 0x801fff to data_page_1 with global
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_GLOBAL
  sd a1, 32(a0)
  # remap 0xa01000 - 0xa01fff to data_page_1 with global
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_GLOBAL
  sd a1, 40(a0)
  # remap 0xc01000 - 0xc01fff to data_page_1 with global
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_GLOBAL
  sd a1, 48(a0)
  # remap 0xe01000 - 0xe01fff to data_page_1 with global
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_GLOBAL
  sd a1, 56(a0)
  # remap 0x1001000 - 0x1001fff to data_page_1 with global
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_GLOBAL
  sd a1, 64(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x201108, should equal to 1111
  # 0x201108 is in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: refill fake-global entry to Page Cache
  # sfence all asid
  sfence.vma x0, x0

  # lw 0x401108, should equal to 1111
  # 0x401108 has been flushed, need a request to mem
  # refill 0x401108 to Page Cache with global
  # 2MB entry in Page Cache need 8-consecutive entries to be global
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  # refill 0x201108 to Page Cache with global
  # 2MB entry in Page Cache need 8-consecutive entries to be global
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  CLEAR_MPRV
  # remap 0x201000 - 0x201fff to data_page_2
  la a0,page_table_1_1
  la a1,page_table_2_2
  MAKE_PMD
  sd a1, 8(a0)
  # remap 0x401000 - 0x401fff to data_page_2
  la a0,page_table_1_1
  la a1,page_table_2_2
  MAKE_PMD
  sd a1, 16(a0)
  SET_MPRV

  # 3: before sfence
  # lw 0x401108, should equal to 1111
  # 0x401108 is still in Page Cache now
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 is still in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 4: sfence current asid, but without global
  # only sfence asid 1, is current asid
  li x1, 1
  sfence.vma x0, x1

  # lw 0x401108, should equal to 1111
  # 0x401108 is global, should not be flushed
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 is global, should not be flushed
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # 5: sfence all asid
  sfence.vma x0, x0

  # lw 0x401108, should equal to 2222
  # 0x40201108 has been flushed, need a request to mem
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  j before_sfence_4KB

before_sfence_4KB:

  CLEAR_MPRV

  # clear map 0x1000 - 0x1fff
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_UNVALID
  sd a1, 0(a0)

  # remap 0x201000 - 0x201fff
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_UNVALID
  sd a1, 8(a0)

  # remap 0x401000 - 0x401fff
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_UNVALID
  sd a1, 16(a0)

  # remap 0x601000 - 0x601fff
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_UNVALID
  sd a1, 24(a0)

  # remap 0x801000 - 0x801fff
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_UNVALID
  sd a1, 32(a0)

  # remap 0xa01000 - 0xa01fff
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_UNVALID
  sd a1, 40(a0)

  # remap 0xc01000 - 0xc01fff
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_UNVALID
  sd a1, 48(a0)

  # remap 0xe01000 - 0xe01fff
  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD_UNVALID
  sd a1, 56(a0)

  # map 0x201000 - 0x201fff to data_page_1
  la a0,page_table_1_0
  la a1,page_table_1_1
  MAKE_PGD
  sd a1, 0(a0)

  la a0,page_table_1_1
  la a1,page_table_1_2
  MAKE_PMD
  sd a1, 8(a0)

  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE
  sd a1, 8(a0)

  SET_MPRV

  sfence.vma x0, x0

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  # refill 0x201108 to Page Cache
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  j sfence_4KB_1

sfence_4KB_1:

  CLEAR_MPRV
  # remap 0x202000 - 0x202fff to data_page_1
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE
  sd a1, 16(a0)
  # remap 0x201000 - 0x201fff to data_page_2
  la a0,page_table_1_2
  la a1,data_page_2
  MAKE_PTE
  sd a1, 8(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x201108, should equal to 1111
  # 0x201108 is in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: sfence other asid
  # only sfence asid 0, not current asid
  # However, Page Cache will flush all 4KB Pages with any asid
  # So 0x201108 will not be in Page Cache
  # But will still be in L1 TLB
  li x1, 0
  sfence.vma x0, x1

  # lw 0x202108, should equal to 1111
  # 0x202108 is not in Page Cache, need a request to mem
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

#ifdef ASID_L2TLB
  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail
#endif

#ifdef ASID_L1TLB
  # lw 0x201108, should equal to 1111
  # 0x201108 is still in L1 TLB
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail
#endif

  # 3: sfence other asid
  # only sfence asid 0, not current asid
  # However, Page Cache will flush all 4KB Pages with any asid
  # So 0x201108 will not be in Page Cache
  # But will still be in L1 TLB
  li x1, 2
  sfence.vma x0, x1

  # lw 0x202108, should equal to 2222
  # 0x202108 is not in Page Cache, need a request to mem
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

#ifdef ASID_L2TLB
  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail
#endif

#ifdef ASID_L1TLB
  # lw 0x201108, should equal to 1111
  # 0x201108 is still in L1 TLB
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail
#endif

  fence

  # 4: sfence current asid
  # only sfence asid 1, is current asid
  # However, Page Cache will flush all 4KB Pages with any asid
  # So 0x201108 will not be in Page Cache
  # Is current asid, 0x201108 will also be flushed from L1 TLB
  li x1, 1
  sfence.vma x0, x1

  # lw 0x202108, should equal to 1111
  # 0x202108 is not in Page Cache, need a request to mem
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  fence

  j sfence_4KB_2

sfence_4KB_2:

  CLEAR_MPRV
  # remap 0x201000 - 0x201fff to data_page_1
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE
  sd a1, 8(a0)
  # remap 0x202000 - 0x202fff to data_page_2
  la a0,page_table_1_2
  la a1,data_page_2
  MAKE_PTE
  sd a1, 16(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x202108, should equal to 1111
  # 0x202108 is in Page Cache now
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: sfence all asid
  sfence.vma x0, x0

  # lw 0x202108, should equal to 2222
  # 0x202108 has been flushed, need a request to mem
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  j sfence_4KB_3

sfence_4KB_3:

  CLEAR_MPRV
  # remap 0x202000 - 0x202fff to data_page_1 with global
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE_GLOBAL
  sd a1, 16(a0)
  # remap 0x201000 - 0x201fff to data_page_2
  la a0,page_table_1_2
  la a1,data_page_2
  MAKE_PTE
  sd a1, 8(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x201108, should equal to 1111
  # 0x201108 is in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: refill fake-global entry to Page Cache
  # sfence all asid
  sfence.vma x0, x0

  # lw 0x202108, should equal to 1111
  # 0x202108 has been flushed, need a request to mem
  # refill 0x202108 to Page Cache
  # However, 4KB entry in Page Cache need 8-consecutive entries to be global
  # So in fact it is not global in Page Cache
  # However, pay attention that 0x202108 is global in L1 TLB
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  # refill 0x201108 to Page Cache
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  CLEAR_MPRV
  # remap 0x201000 - 0x201fff to data_page_1
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE
  sd a1, 8(a0)
  # remap 0x202000 - 0x202fff to data_page_2
  la a0,page_table_1_2
  la a1,data_page_2
  MAKE_PTE
  sd a1, 16(a0)
  SET_MPRV

  # 3: before sfence
  # lw 0x202108, should equal to 1111
  # 0x202108 is still in Page Cache now
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 4: sfence current asid, but without global
  # only sfence asid 1, is current asid
  li x1, 1
  sfence.vma x0, x1

#ifdef ASID_L2TLB
  # lw 0x202108, should equal to 2222
  # 0x202108 is fake-global, has been flushed, need a request to mem
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail
#endif

#ifdef ASID_L1TLB
  # lw 0x202108, should equal to 1111
  # 0x202108 is global in L1 TLB, should not be flusheds
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail
#endif

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  j sfence_4KB_4

sfence_4KB_4:

  CLEAR_MPRV
  # remap 0x200000 - 0x200fff to data_page_1 with global
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE_GLOBAL
  sd a1, 0(a0)
  # remap 0x201000 - 0x201fff to data_page_1 with global
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE_GLOBAL
  sd a1, 8(a0)
  # remap 0x202000 - 0x202fff to data_page_1 with global
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE_GLOBAL
  sd a1, 16(a0)
  # remap 0x203000 - 0x203fff to data_page_1 with global
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE_GLOBAL
  sd a1, 24(a0)
  # remap 0x204000 - 0x204fff to data_page_1 with global
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE_GLOBAL
  sd a1, 32(a0)
  # remap 0x205000 - 0x205fff to data_page_1 with global
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE_GLOBAL
  sd a1, 40(a0)
  # remap 0x206000 - 0x206fff to data_page_1 with global
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE_GLOBAL
  sd a1, 48(a0)
  # remap 0x207000 - 0x207fff to data_page_1 with global
  la a0,page_table_1_2
  la a1,data_page_1
  MAKE_PTE_GLOBAL
  sd a1, 56(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x201108, should equal to 1111
  # 0x201108 is in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 2: refill fake-global entry to Page Cache
  # sfence all asid
  sfence.vma x0, x0

  # lw 0x202108, should equal to 1111
  # 0x202108 has been flushed, need a request to mem
  # refill 0x202108 to Page Cache with global
  # 4KB entry in Page Cache need 8-consecutive entries to be global
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 has been flushed, need a request to mem
  # refill 0x201108 to Page Cache with global
  # 2MB entry in Page Cache need 8-consecutive entries to be global
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  CLEAR_MPRV
  # remap 0x201000 - 0x201fff to data_page_2
  la a0,page_table_1_2
  la a1,data_page_2
  MAKE_PTE
  sd a1, 8(a0)
  # remap 0x202000 - 0x202fff to data_page_2
  la a0,page_table_1_2
  la a1,data_page_2
  MAKE_PTE
  sd a1, 16(a0)
  SET_MPRV

  # 3: before sfence
  # lw 0x202108, should equal to 1111
  # 0x202108 is still in Page Cache now
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 is still in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  fence

  # 4: sfence current asid, but without global
  # only sfence asid 1, is current asid
  li x1, 1
  sfence.vma x0, x1

  # lw 0x202108, should equal to 1111
  # 0x202108 is global, should not be flushed
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # lw 0x201108, should equal to 1111
  # 0x201108 is global, should not be flushed
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 1111
  bne a0, a1, fail

  # 5: sfence all asid
  sfence.vma x0, x0

  # lw 0x202108, should equal to 2222
  # 0x401108 has been flushed, need a request to mem
  li a0, 0x202100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  # lw 0x201108, should equal to 2222
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 2222
  bne a0, a1, fail

  j before_sfence_1GB_sp

before_sfence_1GB_sp:

  # change to asid 3
  csrw satp, t3

  # lw 0x201108, in order to refill 0x201108 to Page Cache
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  j sfence_1GB_sp_1

sfence_1GB_sp_1:

  CLEAR_MPRV
  # remap 0x400000 - 0x5fffff to data_page_3
  la a0,page_table_3_1
  la a1,data_page_3
  MAKE_PTE
  sd a1, 16(a0)
  # remap 0x200000 - 0x3fffff to data_page_4
  la a0,page_table_3_1
  la a1,data_page_4
  MAKE_PTE
  sd a1, 8(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x201108, should equal to 3333
  # 0x201108 is in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  fence

  # 2: sfence other asid
  # only sfence asid 0, not current asid
  li x1, 0
  sfence.vma x0, x1

  # lw 0x401108, should equal to 3333
  # 0x401108 is not in Page Cache, need a request to mem
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  # lw 0x201108, should equal to 3333
  # 0x201108 is still in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  fence

  # 3: sfence other asid
  # only sfence asid 2, not current asid
  li x1, 2
  sfence.vma x0, x1

  # lw 0x401108, should equal to 3333
  # 0x401108 is in Page Cache now
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  # lw 0x201108, should equal to 3333
  # 0x201108 is still in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  fence

  # 4: sfence current asid
  # only sfence asid 3, is current asid
  li x1, 3
  sfence.vma x0, x1

  # lw 0x401108, should equal to 3333
  # 0x401108 has been flushed, need a request to mem
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  # lw 0x201108, should equal to 4444
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 4444
  bne a0, a1, fail

  j sfence_1GB_sp_2

sfence_1GB_sp_2:

  CLEAR_MPRV
  # remap 0x200000 - 0x3fffff to data_page_3
  la a0,page_table_3_1
  la a1,data_page_3
  MAKE_PTE
  sd a1, 8(a0)
  # remap 0x400000 - 0x5fffff to data_page_4
  la a0,page_table_3_1
  la a1,data_page_4
  MAKE_PTE
  sd a1, 16(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x401108, should equal to 3333
  # 0x401108 is in Page Cache now
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  fence

  # 2: sfence all asid
  sfence.vma x0, x0

  # lw 0x401108, should equal to 4444
  # 0x401108 has been flushed, need a request to mem
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 4444
  bne a0, a1, fail

  # lw 0x201108, should equal to 3333
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  j sfence_1GB_sp_3

sfence_1GB_sp_3:

  CLEAR_MPRV
  # remap 0x401000 - 0x401fff to data_page_3 with global
  la a0,page_table_3_1
  la a1,data_page_3
  MAKE_PTE_GLOBAL
  sd a1, 16(a0)
  # remap 0x201000 - 0x201fff to data_page_4
  la a0,page_table_3_1
  la a1,data_page_4
  MAKE_PTE
  sd a1, 8(a0)
  SET_MPRV

  # 1: before sfence
  # lw 0x201108, should equal to 3333
  # 0x201108 is in Page Cache now
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  fence

  # 2: refill global entry to Page Cache
  # sfence all asid
  sfence.vma x0, x0

  # lw 0x401108, should equal to 3333
  # 0x401108 has been flushed, need a request to mem
  # refill 0x401108 to Page Cache with global
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  # lw 0x201108, should equal to 4444
  # 0x201108 has been flushed, need a request to mem
  # refill 0x201108 to Page Cache
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 4444
  bne a0, a1, fail

  CLEAR_MPRV
  # remap 0x201000 - 0x201fff to data_page_3
  la a0,page_table_3_1
  la a1,data_page_3
  MAKE_PTE
  sd a1, 8(a0)
  # remap 0x401000 - 0x401fff to data_page_4
  la a0,page_table_3_1
  la a1,data_page_4
  MAKE_PTE
  sd a1, 16(a0)
  SET_MPRV

  # 3: before sfence
  # lw 0x401108, should equal to 3333
  # 0x401108 is still in Page Cache now
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  fence

  # 4: sfence current asid, but without global
  # only sfence asid 3, is current asid
  li x1, 3
  sfence.vma x0, x1

  # lw 0x401108, should equal to 3333
  # 0x401108 is global, should not be flushed
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  # lw 0x201108, should equal to 3333
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  # 5: sfence all asid
  sfence.vma x0, x0

  # lw 0x401108, should equal to 4444
  # 0x401108 has been flushed, need a request to mem
  li a0, 0x401100
  lw a0, 8(a0)
  li a1, 4444
  bne a0, a1, fail

  # lw 0x201108, should equal to 3333
  # 0x201108 has been flushed, need a request to mem
  li a0, 0x201100
  lw a0, 8(a0)
  li a1, 3333
  bne a0, a1, fail

  j success

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

# 1GB pte
.align 30
data_page_5: .dword 0

# 2MB pte, align 26 because 2GB address space is too small for align 30
.align 26
data_page_4: .dword 0

# 2MB pte
.align 21
data_page_3: .dword 0

# 4KB pte, align 21 because data_page_3 is 2MB pte
.align 21
data_page_2: .dword 0

# 4KB pte
.align 12
data_page_1: .dword 0

.align 12
page_table_1_0: .dword 0

.align 12
page_table_1_1: .dword 0

.align 12
page_table_1_2: .dword 0

.align 12
page_table_2_0: .dword 0

.align 12
page_table_2_1: .dword 0

.align 12
page_table_2_2: .dword 0

.align 12
page_table_3_0: .dword 0

.align 12
page_table_3_1: .dword 0

.align 12
page_table_4_0: .dword 0

.align 12
page_table_4_1: .dword 0

.align 12
page_table_5_0: .dword 0


RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
