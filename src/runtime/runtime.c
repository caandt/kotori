#include "runtime.h"

asm(R"(
.global rtd
a8_runtime_start:
  b cfi_abort
  b _start
  b hook
rtd: .fill 8

_start:
  add x0, sp, #8          // x0 = argv
  ldr x1, [sp]
  add x1, x0, x1, lsl #3
  add x1, x1, #8          // x1 = envp
  bl init                 // init(argv, envp)
  mov lr, #0
  ldr x19, rtd
  ldr x19, [x19, %0]
  br x19                  // goto real_entry
)" : : "i"(offsetof(rtd_t, entry)));

void cfi_abort() {
  DIE("CFI abort");
}
#ifdef A8_SEGV_HANDLER
  #include "sighandler.c"
#endif
#ifdef A8_NO_ASLR
  #include "disable_aslr.c"
#endif
#ifdef A8_HOOK
  #include "init_hook.c"
#endif
#ifdef A8_PRELOAD_REL
  #include "preload_rel.c"
#endif

void init(long argv, long envp) {
#ifdef A8_NO_ASLR
  disable_aslr(argv, envp);
#endif
#ifdef A8_HOOK
  init_hook(argv);
#endif
#ifdef A8_SEGV_HANDLER
  add_sighandler();
#endif
#ifdef A8_PRELOAD_REL
  init_rel();
#endif
}
