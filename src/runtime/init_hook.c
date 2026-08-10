#include "runtime.h"

static inline long sys_openat(int dfd, const char *path, int flags, int mode) {
  return syscall4(SYS_openat, dfd, (long)path, flags, mode);
}

static inline char *basename(char *path, char **end) {
  char *s = path;
  char *last = 0;
  while (*s)
    if (*s++ == '/')
      last = s;
  *end = s;
  return last == 0 ? path : last;
}
static inline int get_exec_segs(range_t *out, int len) {
  long fd = sys_openat(0, "/proc/self/maps", 0, 0);
  if (fd < 0) {
    DIE("Could not read maps");
  }
  unsigned long next_addr = 0;
  for (int i = 0; i < len; i++) {
    struct procmap_query q = {0};
    q.size = sizeof(q);
    q.query_flags = PROCMAP_QUERY_COVERING_OR_NEXT_VMA | PROCMAP_QUERY_VMA_EXECUTABLE;
    q.query_addr = next_addr;
    long ret = syscall3(SYS_ioctl, fd, PROCMAP_QUERY, (long)&q);
    if (ret < 0) {
      if (ret == -2) return i;
      DIE("PROCMAP_QUERY returned error");
    }
    out[i] = (range_t){ q.vma_start, q.vma_end, (q.vma_end - q.vma_start) / 4 };
    next_addr = q.vma_end;
  }
  return len;
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
  long fd = sys_openat(0, path, O_RDWR, 0);
  rtd_t *rtd = get_rtd();
#if A8_HOOK == 'P'
  unsigned long nrets = rtd->nrets;
  unsigned long nextfree = sizeof(map_header) + rtd->nrets * sizeof(map_entry);
  unsigned long size = nextfree + (1024 * 1024);
#else
  range_t segs[MAP_HEADER_SEGS];
  int nsegs = get_exec_segs(segs, MAP_HEADER_SEGS);
  unsigned long size = 0;
  for (int i = 0; i < nsegs; i++) {
    size += segs[i].size;
  }
  size = size * sizeof(map_entry) + sizeof(map_header);
#endif
  char init = 0;
  if (fd < 0) {
    init = 1;
    fd = sys_openat(0, path, O_RDWR | O_CREAT, 0644);
    if (fd < 0) DIE("Could not create log file");
    long res = syscall2(SYS_ftruncate, fd, size);
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
#if A8_HOOK == 'P'
    header->nrets = nrets;
    header->nextfree = nextfree;
#else
    for (int i = 0; i < nsegs; i++) {
      header->segs[i] = segs[i];
    }
#endif
  } else if (header->magic != MAP_HEADER_MAGIC) {
#if A8_HOOK == 'P'
    if (header->nrets != nrets)
      DIE("Invalid log file");
#else
    for (int i = 0; i < nsegs; i++)
      if (header->segs[i].start != segs[i].start || header->segs[i].end != segs[i].end)
        DIE("Invalid log file");
#endif
  }
  *(long*)path = save_start;
  *(long*)end = save_end;
}
