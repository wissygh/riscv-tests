#include "riscv_test.h"
#undef RVTEST_RV64S
#define RVTEST_RV64S RVTEST_RV64M
#define __MACHINE_MODE

#include "../rv64si/debugCsrEXII.S"