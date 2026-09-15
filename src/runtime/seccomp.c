#include "runtime.h"

#define ARG_LO(idx) (offsetof(struct seccomp_data, args[(idx)]))
#define ARG_HI(idx) (offsetof(struct seccomp_data, args[(idx)]) + 4)
#define MAGIC_ALLOW 0xa8621053

const struct sock_filter filter[] = {
  // if (sysnum != rt_sigaction) then allow
  BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_rt_sigaction, 0, 14),
  // if (act == NULL) then allow
  BPF_STMT(BPF_LD | BPF_W | BPF_ABS, ARG_LO(1)),
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 0, 2),
  BPF_STMT(BPF_LD | BPF_W | BPF_ABS, ARG_HI(1)),
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 0, 10, 0),
  // if ((u32)signum ^ (u32)act ^ MAGIC_ALLOW == arg4) then allow
  BPF_STMT(BPF_LD | BPF_W | BPF_ABS, ARG_LO(0)),
  BPF_STMT(BPF_ST, 0),
  BPF_STMT(BPF_LD | BPF_W | BPF_ABS, ARG_LO(1)),
  BPF_STMT(BPF_LDX | BPF_W | BPF_MEM, 0),
  BPF_STMT(BPF_ALU | BPF_XOR | BPF_X, 0),
  BPF_STMT(BPF_ALU | BPF_XOR | BPF_K, MAGIC_ALLOW),
  BPF_STMT(BPF_MISC | BPF_TAX, 0),
  BPF_STMT(BPF_LD | BPF_W | BPF_ABS, ARG_LO(4)),
  BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_X, 0, 1, 0),
  // else trap to sigsys_handler
  BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_TRAP),
  BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
};
void sigsys_handler(int sig, siginfo_t *info, void *ucontext) {
  ucontext_t *uc = (ucontext_t *)ucontext;
  long sysnum = uc->uc_mcontext.regs[8];
  long signum = uc->uc_mcontext.regs[0];
  long act = uc->uc_mcontext.regs[1];
  long oldact = uc->uc_mcontext.regs[2];
  long sigsetsize = uc->uc_mcontext.regs[3];
  if (sysnum != SYS_rt_sigaction || !act) {
    syscall3(SYS_write, 2, (long)"Bad system call\n", 16);
    EXIT(159);
  }
  long ret = 0;
  if (signum != SIGSYS
#ifdef A8_SEGV_HANDLER
    && signum != SIGSEGV
#endif
  ) {
    struct kernel_sigaction actp = *(struct kernel_sigaction*)act;
    rtd_t *rtd = get_rtd();
    actp.sigaction = (void*)lookup(rtd, (long)actp.sigaction);
    long checksum = (signum & 0xffffffff) ^ ((long)&actp & 0xffffffff) ^ MAGIC_ALLOW;
    ret = syscall5(SYS_rt_sigaction, signum, (long)&actp, (long)oldact, sigsetsize, checksum);
  }
  uc->uc_mcontext.regs[0] = ret;
}
void install_filter() {
  struct sock_fprog prog = {
    .len = (unsigned short)(sizeof(filter) / sizeof(filter[0])),
    .filter = (void*)filter,
  };
  struct kernel_sigaction sa = {0};
  sa.sigaction = sigsys_handler;
  sa.sa_flags = SA_SIGINFO;
  syscall4(SYS_rt_sigaction, SIGSYS, (long)&sa, 0, sizeof(target_sigset_t));
  syscall5(SYS_prctl, PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0);
  syscall5(SYS_prctl, PR_SET_SECCOMP, SECCOMP_MODE_FILTER, (long)&prog, 0, 0);
}
