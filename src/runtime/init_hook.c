#include "runtime.h"

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
    if (fd < 0) DIE("Could not create log file");
    long res = syscall3(SYS_ftruncate, fd, size, 0);
    if (res < 0) {
      syscall1(SYS_close, fd);
      DIE("Count not resize log file");
    }
  }
  unsigned long mapped = syscall6(SYS_mmap, BASE, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  syscall1(SYS_close, fd);
  if (mapped >= (unsigned long)-4095) {
    DIE("Could not mmap log file");
  }
  map_header *header = (void*)BASE;
  if (init) {
    header->magic = MAP_HEADER_MAGIC;
    header->nrets = nrets;
    header->nextfree = nextfree;
  } else if (header->magic != MAP_HEADER_MAGIC || header->nrets != nrets) {
    DIE("Invalid log file");
  }
  *(long*)path = save_start;
  *(long*)end = save_end;
}
