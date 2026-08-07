#include "runtime.h"

void disable_aslr(long argv, long envp) {
  long p1 = PERSONALITY(0xffffffff);
  long p2 = p1 | ADDR_NO_RANDOMIZE;
  if (p1 != p2) {
    if (PERSONALITY(p2) == -1) {
      DIE("Could not change personality");
    }
    EXECVE("/proc/self/exe", argv, envp);
    DIE("Could not re-exec program");
  }
}
