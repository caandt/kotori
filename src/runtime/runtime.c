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
void segfault_handler(int sig, siginfo_t *info, void *context) {
  ucontext_t *uc = (ucontext_t*)context;
  rtd_t *rtd = get_rtd();
  long pc = uc->uc_mcontext.pc;
  long addr = (long)info->si_addr;
  if (rtd->text_start <= pc && pc < rtd->text_end) {
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
#endif
#ifdef A8_NO_ASLR
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
#endif
#ifdef A8_HOOK
static inline char *basename(char *path, char **end) {
  char *s = path;
  char *last = 0;
  while (*s)
    if (*s++ == '/')
      last = s;
  *end = s;
  return last == 0 ? path : last;
}
void init_hook(long argv) {
  char *end;
  char *path = basename(*(char**)argv, &end) - 5;
  long save_start = *(long*)path;
  long save_end = *(long*)end;
  path[0] = '/';
  path[1] = 't';
  path[2] = 'm';
  path[3] = 'p';
  path[4] = '/';
  end[0] = '.';
#if A8_HOOK == 'P'
  end[1] = 'p';
  end[2] = 'o';
  end[3] = 'l';
#else
  end[1] = 'c';
  end[2] = 'n';
  end[3] = 't';
#endif
  end[4] = '\0';
  long fd = syscall4(SYS_openat, 0, (long)path, O_RDWR, 0);
  rtd_t *rtd = get_rtd();
#if A8_HOOK == 'P'
  unsigned long nrets = rtd->nrets;
  unsigned long nextfree = sizeof(map_header) + rtd->nrets * sizeof(map_entry);
  unsigned long size = nextfree + (1024 * 1024);
#else
  unsigned long nrets = (rtd->new_text_end - rtd->new_text_start) >> 2;
  unsigned long nextfree = rtd->new_text_start;
  unsigned long size = sizeof(map_header) + nrets * sizeof(map_entry);
#endif
  char init = 0;
  if (fd < 0) {
    init = 1;
    fd = syscall4(SYS_openat, 0, (long)path, O_RDWR | O_CREAT, 0644);
    if (fd < 0) DIE("Could not create policy file");
    long res = syscall3(SYS_ftruncate, fd, size, 0);
    if (res < 0) {
      syscall1(SYS_close, fd);
      DIE("Count not resize policy file");
    }
  }
  unsigned long mapped = syscall6(SYS_mmap, BASE, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  syscall1(SYS_close, fd);
  if (mapped >= (unsigned long)-4095) {
    DIE("Could not mmap policy file");
  }
  map_header *header = (void*)BASE;
  if (init) {
    header->magic = MAP_HEADER_MAGIC;
    header->nrets = nrets;
    header->nextfree = nextfree;
  } else if (header->magic != MAP_HEADER_MAGIC || header->nrets != nrets) {
    DIE("Invalid policy file");
  }
  *(long*)path = save_start;
  *(long*)end = save_end;
}
#endif
#ifdef A8_PRELOAD_REL
void init_rel() {
  rtd_t *rtd = get_rtd();
  unsigned long n = (rtd->text_end - rtd->text_start) >> 2;
  unsigned long mapped = syscall6(SYS_mmap, BASE2, ((n << 2) | 0xfff) + 1, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
  if (mapped >= (unsigned long)-4095) {
    DIE("Could not mmap rel");
  }
  int *arr = (int*)mapped;
  unsigned int d = 0;
  unsigned long idx = 0;
  for (unsigned int i = 0; i < n; i++) {
    if (idx < rtd->dsize && i > rtd->d[idx].idx) {
      d = rtd->d[idx].dev;
      idx++;
    }
    arr[i] = rtd->new_text_start + 4 * (i + d);
  }
}
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
