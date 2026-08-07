#include "runtime.h"

void segfault_handler(int sig, siginfo_t *info, void *context) {
  ucontext_t *uc = (ucontext_t*)context;
  rtd_t *rtd = get_rtd();
  long pc = uc->uc_mcontext.pc;
  long addr = (long)info->si_addr;
  if (rtd->text_start <= pc && pc < rtd->text_end) {
    syscall3(SYS_write, 2, (long)"a8 warn: fixup\n", 15);
    uc->uc_mcontext.pc = lookup(rtd, addr);
  } else {
    WRITE("Segmentation fault at "); print16(pc); WRITE("\n");
    EXIT(139);
  }
}
asm(R"(
sa_restorer:
  mov x8, %0
  svc #0
)" : : "i"(SYS_rt_sigreturn));
void add_sighandler() {
  struct kernel_sigaction sa = {0};
  sa.sigaction = segfault_handler;
  sa.sa_flags = SA_SIGINFO | SA_RESTORER;
  asm("adr %0, sa_restorer" : "=r"(sa.restorer));
  syscall4(SYS_rt_sigaction, SIGSEGV, (long)&sa, 0, sizeof(target_sigset_t));
}
