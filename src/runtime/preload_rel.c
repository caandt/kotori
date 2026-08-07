#include "runtime.h"

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
