// See LICENSE for license details.

// Test of PMP functionality.

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include "util.h"

volatile int trap_expected;
volatile int granule;
volatile int test_mode;
volatile int expect_excep;
volatile int pmp_rw;
volatile int is_smode;
enum TEST_MODE {
  LDST, PTW, INSTR
};

enum CMD {
  READ, WRITE, EXEC
};

// #define INLINE inline __attribute__((always_inline))
#define INLINE __attribute__((noinline))
#define min(x, y) (x > y ? y : x)
#define max(x, y) (x > y ? x : y)

INLINE void reset_mpp() __attribute__((optimize("O3")));
INLINE void reset_mpp() {
  uintptr_t mpp_s = MSTATUS_MPP;
  asm volatile ("mv t0, %0; csrs mstatus, t0; jr ra" : : "r" (mpp_s));
}

INLINE void reset_mprv() __attribute__((optimize("O3")));
INLINE void reset_mprv() {
  uintptr_t mpp_s = MSTATUS_MPRV;
  asm volatile ("mv t0, %0; csrc mstatus, t0; jr ra" : : "r" (mpp_s));
}

uintptr_t handle_trap(uintptr_t cause, uintptr_t epc, uintptr_t regs[32])
{
  if (cause == CAUSE_ILLEGAL_INSTRUCTION) {
    reset_mpp();
    return epc;
  }

  if (cause != CAUSE_LOAD_ACCESS && cause != CAUSE_FETCH_ACCESS && cause != CAUSE_STORE_ACCESS)
    exit(1); // no PMP support
  if (!trap_expected)
    exit(2);
  if (!(expect_excep == CAUSE_LOAD_ACCESS || expect_excep == CAUSE_FETCH_ACCESS || expect_excep == CAUSE_STORE_ACCESS))
    exit(3);
  if (cause != expect_excep) {
    exit(4);
  }

  // if (test_mode == LDST) {
  //   if (cause != expect_excep)
  //     exit(1);
  // } else if (test_mode == PTW) {
  //   if ((cause != expect_excep == EXCEP_LD) ||
  //       (cause != CAUSE_FETCH_ACCESS && expect_excep == EXCEP_INSTR) ||
  //       (cause != CASUE_STORE_ACCESS && expect_excep == EXCEP_ST))
  //     exit(2);
  // } else if (test_mode == INSTR) { // test_mode is INSTR
  //   if ((cause != CAUSE_FETCH_ACCESS))
  //     exit(3);
  // } else {
  //   exit(5);
  // }

  trap_expected = 0;
  if (cause == CAUSE_FETCH_ACCESS)
    return epc;
  else
    return epc + insn_len(epc);
}

#define SCRATCH RISCV_PGSIZE
uintptr_t scratch[RISCV_PGSIZE / sizeof(uintptr_t)] __attribute__((aligned(RISCV_PGSIZE)));
uintptr_t l1pt[RISCV_PGSIZE / sizeof(uintptr_t)] __attribute__((aligned(RISCV_PGSIZE)));
uintptr_t l2pt[RISCV_PGSIZE / sizeof(uintptr_t)] __attribute__((aligned(RISCV_PGSIZE)));
#if __riscv_xlen == 64
uintptr_t l3pt[RISCV_PGSIZE / sizeof(uintptr_t)] __attribute__((aligned(RISCV_PGSIZE)));
#else
#define l3pt l2pt
#endif

static void init_pt()
{
  l1pt[0] = ((uintptr_t)l2pt >> RISCV_PGSHIFT << PTE_PPN_SHIFT) | PTE_V;
  l1pt[2] = ((uintptr_t)0x80000000L >> RISCV_PGSHIFT << PTE_PPN_SHIFT) | PTE_V | PTE_X | PTE_R | PTE_W | PTE_A | PTE_D;
  l3pt[SCRATCH / RISCV_PGSIZE] = ((uintptr_t)scratch >> RISCV_PGSHIFT << PTE_PPN_SHIFT) | PTE_A | PTE_D | PTE_V | PTE_R | PTE_W;
#if __riscv_xlen == 64
  l2pt[0] = ((uintptr_t)l3pt >> RISCV_PGSHIFT << PTE_PPN_SHIFT) | PTE_V;
  uintptr_t vm_choice = SATP_MODE_SV39;
#else
  uintptr_t vm_choice = SATP_MODE_SV32;
#endif
  write_csr(sptbr, ((uintptr_t)l1pt >> RISCV_PGSHIFT) |
                   (vm_choice * (SATP_MODE & ~(SATP_MODE<<1))));
  write_csr(pmpaddr2, -1);
  write_csr(pmpcfg0, (PMP_NAPOT | PMP_R | PMP_W | PMP_X) << 16);
}

INLINE uintptr_t va2pa(uintptr_t va)
{
  if (va < SCRATCH || va >= SCRATCH + RISCV_PGSIZE)
    exit(5);
  return va - SCRATCH + (uintptr_t)scratch;
}

typedef struct {
  uintptr_t cfg;
  uintptr_t a0;
  uintptr_t a1;
} pmpcfg_t;

INLINE int pmp_ok(pmpcfg_t p, uintptr_t addr, uintptr_t size, int cmd)
{
  if ((p.cfg & PMP_A) == 0)
    return 1;

  if ((p.cfg & PMP_A) != PMP_TOR) {
    uintptr_t range = 1;

    if ((p.cfg & PMP_A) == PMP_NAPOT) {
      range <<= 1;
      for (uintptr_t i = 1; i; i <<= 1) {
        if ((p.a1 & i) == 0)
          break;
        p.a1 &= ~i;
        range <<= 1;
      }
    }

    p.a0 = p.a1;
    p.a1 = p.a0 + range;
  }

  p.a0 *= granule;
  p.a1 *= granule;
  addr = va2pa(addr);

  uintptr_t hits = 0;
  for (uintptr_t i = 0; i < size; i += granule) {
    if (p.a0 <= addr + i && addr + i < p.a1)
      hits += granule;
  }

  int cmd_ok = 0;
  if (cmd == READ) {
    cmd_ok = p.cfg & PMP_R;
  } else if (cmd == WRITE) {
    cmd_ok = p.cfg & PMP_W;
  } else if (cmd == INSTR) {
    cmd_ok = p.cfg & PMP_X;
  }

  return (hits == 0 || hits >= size) && cmd_ok;
}

INLINE void test_one_st(uintptr_t addr, uintptr_t size)
{
  uintptr_t new_mstatus = (read_csr(mstatus) & ~MSTATUS_MPP) | (MSTATUS_MPP & (MSTATUS_MPP >> 1)) | MSTATUS_MPRV;
  switch (size) {
    case 1: asm volatile ("csrrw %0, mstatus, %0; sb x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
    case 2: asm volatile ("csrrw %0, mstatus, %0; sh x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
    case 4: asm volatile ("csrrw %0, mstatus, %0; sw x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
#if __riscv_xlen >= 64
    case 8: asm volatile ("csrrw %0, mstatus, %0; sd x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
#endif
    default: __builtin_unreachable();
  }
}

INLINE void test_one_ld(uintptr_t addr, uintptr_t size)
{
  uintptr_t new_mstatus = (read_csr(mstatus) & ~MSTATUS_MPP) | (MSTATUS_MPP & (MSTATUS_MPP >> 1)) | MSTATUS_MPRV;
  switch (size) {
    case 1: asm volatile ("csrrw %0, mstatus, %0; lb x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
    case 2: asm volatile ("csrrw %0, mstatus, %0; lh x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
    case 4: asm volatile ("csrrw %0, mstatus, %0; lw x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
#if __riscv_xlen >= 64
    case 8: asm volatile ("csrrw %0, mstatus, %0; ld x0, (%1); csrw mstatus, %0" : "+&r" (new_mstatus) : "r" (addr)); break;
#endif
    default: __builtin_unreachable();
  }
}

INLINE void test_one_ldst(pmpcfg_t p, uintptr_t addr, int size) {
  expect_excep = CAUSE_LOAD_ACCESS;
  trap_expected = !pmp_ok(p, addr, size, READ);
  test_one_ld(addr, size);
  if (trap_expected)
    exit(6);

  expect_excep = CAUSE_STORE_ACCESS;
  trap_expected = !pmp_ok(p, addr, size, WRITE);
  test_one_st(addr, size);
  if (trap_expected)
    exit(7);
}

INLINE void test_all_sizes(pmpcfg_t p, uintptr_t addr)
{
  for (size_t size = 1; size <= sizeof(uintptr_t); size *= 2) {
    if (addr & (size - 1))
      continue;
    test_one_ldst(p, addr, size);
  }
}

INLINE void test_range_once(pmpcfg_t p, uintptr_t base, uintptr_t range)
{
  for (uintptr_t addr = base; addr < base + range; addr += granule)
    test_all_sizes(p, addr);
}

INLINE pmpcfg_t set_pmp(pmpcfg_t p)
{
  uintptr_t cfg0 = read_csr(pmpcfg0);
  write_csr(pmpcfg0, cfg0 & ~0xff00);
  write_csr(pmpaddr0, p.a0);
  write_csr(pmpaddr1, p.a1);
  write_csr(pmpcfg0, ((p.cfg << 8) & 0xff00) | (cfg0 & ~0xff00));
  asm volatile ("sfence.vma" ::: "memory");
  cfg0 = read_csr(pmpcfg0);
  cfg0 = read_csr(pmpaddr0);
  cfg0 = read_csr(pmpaddr1);
  return p;
}

INLINE uintptr_t granule_aligned(uintptr_t addr) {
  return addr & ~(granule - 1);
}

INLINE pmpcfg_t set_pmp_range(uintptr_t base_in, uintptr_t range, uintptr_t cfg)
{
  uintptr_t base = granule_aligned(base_in);
  range += base_in - base;
  range = (range / granule) * granule + (range % granule ? granule : 0);

  pmpcfg_t p;
  p.cfg = PMP_TOR | cfg;
  p.a0 = base >> PMP_SHIFT;
  p.a1 = (base + range) >> PMP_SHIFT;
  return set_pmp(p);
}

INLINE pmpcfg_t set_pmp_napot(uintptr_t base_in, uintptr_t range, uintptr_t cfg)
{
  uintptr_t base = granule_aligned(base_in);
  range += base_in - base;
  range = (range / granule) * granule + (range % granule ? granule : 0);

  pmpcfg_t p;
  p.cfg = cfg | (range > granule ? PMP_NAPOT : PMP_NA4);
  p.a0 = 0;
  p.a1 = (base + (range/2 - 1)) >> PMP_SHIFT;
  return set_pmp(p);
}

INLINE void test_range(uintptr_t addr, uintptr_t range, uintptr_t cfg)
{
  // pmpcfg_t p = set_pmp_range(va2pa(addr), range, cfg);
  // test_range_once(p, addr, range);

  if ((range & (range - 1)) == 0 && (addr & (range - 1)) == 0) {
    pmpcfg_t p = set_pmp_napot(va2pa(addr), range, cfg);
    test_range_once(p, addr, range);
  }
}

INLINE void test_ranges(uintptr_t addr, uintptr_t size)
{
  for (uintptr_t range = granule; range <= size; range += granule) {
    test_range(addr, range, 0);
    test_range(addr, range, PMP_R);
    test_range(addr, range, PMP_R | PMP_W);
  }
}

INLINE void exhaustive_test(uintptr_t addr, uintptr_t size)
{
  for (uintptr_t base = addr; base < addr + size; base += granule)
    test_ranges(base, size - (base - addr));
}

INLINE void detect_granule()
{
  write_csr(pmpcfg0, NULL);
  write_csr(pmpaddr0, 0xffffffffffffffffULL);
  uintptr_t ret = read_csr(pmpaddr0);
  int g = 2;
  for(uintptr_t i = 1; i; i<<=1) {
    if((ret & i) != 0)
      break;
    g++;
  }
  granule = 1UL << g;
}

INLINE void nothing() __attribute__((optimize("O0")));
INLINE void nothing() {
  return ;
}

INLINE void turn_to_smode() __attribute__((optimize("O3")));
INLINE void turn_to_smode() {
  uintptr_t mpp_s = MSTATUS_MPP & (MSTATUS_MPP >> 1);
  asm volatile ("mv t0, %0; csrs mstatus, t0; csrw mepc, ra; mret" : : "r" (mpp_s));
}

INLINE int instr_test_unit(uintptr_t base, uintptr_t size, uintptr_t will_trap, uintptr_t cfg) {
  expect_excep = CAUSE_FETCH_ACCESS;

  trap_expected = will_trap;
  set_pmp_range(base, size, cfg);
  turn_to_smode();
  // nothing();
  if (trap_expected)
    exit(9);

  if (((size & (size - 1)) == 0) && ((base & (size - 1)) == 0)) {
    trap_expected = will_trap;
    size = max(size, granule);
    set_pmp_napot(base, size, cfg);
    turn_to_smode();
    // nothing();
    if (trap_expected)
      exit(10);
  }

  return trap_expected;
}

INLINE void fetch_ptw_area(uintptr_t base, uintptr_t size) {
  instr_test_unit(base, size, 1, 0);
  instr_test_unit(base, size, 0, PMP_R | PMP_X);
}

INLINE void fetch_area(uintptr_t base, uintptr_t size) {
  instr_test_unit(base, size, 1, 0);
  instr_test_unit(base, size, 1, PMP_R | PMP_W);
  instr_test_unit(base, size, 0, PMP_X | PMP_R | PMP_W);
}

// instr is more conflict than ldst and ptw
// we need change priv mode to S mode.
INLINE void test_instr() {
  fetch_ptw_area((uintptr_t )&l1pt[2], 8);
  fetch_area((uintptr_t )0x80000000, 0x00080000);
}

INLINE void access_ldst(uintptr_t addr, uintptr_t size, uintptr_t will_trap, int trap_code) {
  expect_excep = CAUSE_LOAD_ACCESS;
  trap_expected = will_trap;
  test_one_ld(addr, size);
  if (trap_expected)
    exit(trap_code);

  expect_excep = CAUSE_STORE_ACCESS;
  trap_expected = will_trap;
  test_one_st(addr, size);
  if (trap_expected)
    exit(trap_code+1);
}

INLINE void access_ptw_area(uintptr_t base, uintptr_t size, uintptr_t trap_code) {
  uintptr_t addr = SCRATCH;
  for (uintptr_t range = granule; range <= size; range *= 2) {
    set_pmp_range(base, range, 0);
    access_ldst(addr, 4, 1, trap_code);
    access_ldst(addr + 512, 4, 1, trap_code+2);
    access_ldst(addr + RISCV_PGSIZE - 4, 4, 1, trap_code+4);

    if (((range & (range - 1)) == 0) && ((base & (range - 1)) == 0)) {
      set_pmp_napot(base, range, 0);
      access_ldst(addr, 4, 1, trap_code+6);
      access_ldst(addr + 512, 4, 1, trap_code+8);
      access_ldst(addr + RISCV_PGSIZE - 4, 4, 1, trap_code+10);
    }
  }

  for (uintptr_t range = granule; range <= size; range *= 2) {
    int will_trap = range < 8 ? 1 : 0;
    set_pmp_range(base, range, PMP_R);
    access_ldst(addr, 4, will_trap, trap_code+12);
    access_ldst(addr + 512, 4, will_trap, trap_code+14);
    access_ldst(addr + RISCV_PGSIZE - 4, 4, will_trap, trap_code+16);

    if (((range & (range - 1)) == 0) && ((base & (range - 1)) == 0)) {
      set_pmp_napot(base, range, PMP_R);
      access_ldst(addr, 4, will_trap, trap_code+18);
      access_ldst(addr + 512, 4, will_trap, trap_code+20);
      access_ldst(addr + RISCV_PGSIZE - 4, 4, will_trap, trap_code+22);
    }
  }
}

INLINE void test_ptw(uintptr_t size) {
  size = max(size, granule);
  access_ptw_area((uintptr_t)l1pt, size, 11);
  access_ptw_area((uintptr_t)l2pt, size, 35);
  access_ptw_area((uintptr_t)&l3pt[SCRATCH/RISCV_PGSIZE] & ~(granule - 1), size, 59);
}

int main() __attribute__((optimize("O0")));
int main()
{
  detect_granule();
  init_pt();

  test_mode = LDST;
  const int max_exhaustive = min((8 * granule), RISCV_PGSIZE);
  exhaustive_test(SCRATCH, max_exhaustive);
// exit(10);
  exhaustive_test(SCRATCH + RISCV_PGSIZE - max_exhaustive, max_exhaustive);
// exit(10);
  test_range(SCRATCH, RISCV_PGSIZE, 0);
  test_range(SCRATCH, RISCV_PGSIZE / 2, 0);
  test_range(SCRATCH + RISCV_PGSIZE / 2, RISCV_PGSIZE / 2, 0);

  test_range(SCRATCH, RISCV_PGSIZE, PMP_R | PMP_W);
  test_range(SCRATCH, RISCV_PGSIZE / 2, PMP_R | PMP_W);
  test_range(SCRATCH + RISCV_PGSIZE / 2, RISCV_PGSIZE / 2, PMP_R | PMP_W);

  test_range(SCRATCH, 128, 0);
  test_range(SCRATCH + 128, 128, 0);
  test_range(SCRATCH + RISCV_PGSIZE / 2, 128, 0);

  test_range(SCRATCH, 128, PMP_R | PMP_W);
  test_range(SCRATCH + 128, 128, PMP_R | PMP_W);
  test_range(SCRATCH + RISCV_PGSIZE / 2, 128, PMP_R | PMP_W);
// exit(10);
  test_mode = PTW;
  // exit(10);
  test_ptw(min(4 * granule, RISCV_PGSIZE));

  uintptr_t mprv = MSTATUS_MPRV;
  asm volatile ("csrc mstatus, %0" : : "r" (mprv));

  test_mode = INSTR;
  test_instr();

  return 0;
}
