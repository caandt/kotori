#include "runtime.h"
#ifdef A8_POL_HOOK
asm(R"(
log_b_epilogue:
  ldp x16, x17, [sp], #16
  ret
.global log_b
log_b:
  add x17, sp, #16
)");
void log_b_epilogue();
static inline void add(rtd_t*, unsigned long, unsigned long);
void _log_b() {
  unsigned long register src asm("x16");
  unsigned long register *dst asm("x17");
  rtd_t *rtd = get_rtd();
  if (*dst < rtd->text_end && rtd->text_start <= *dst)
    *dst = lookup(rtd, *dst);
  add(rtd, src, *dst);
  return log_b_epilogue();
}
#if A8_POL_HOOK == 1
static inline void add(rtd_t *rtd, unsigned long key, unsigned long val) {
  map_header *header = (map_header*)BASE;
  if (header->nrets <= key) DIE("Invalid polhook key");
  map_entry *e = ((map_entry*)(BASE + sizeof(map_header))) + key;
  while (1) {
    for (int i = 0; i < 7; i++) {
      if (e->vals[i] == 0) {
        e->vals[i] = val;
        return;
      } else if (e->vals[i] == val) {
        return;
      }
    }
    if (e->nextoffset == 0) {
      e->nextoffset = header->nextfree;
      *(unsigned long*)(BASE + header->nextfree) = val;
      header->nextfree += sizeof(map_entry);
      return;
    }
    e = (void*)(BASE + e->nextoffset);
  }
}
#else
static inline void add(rtd_t *rtd, unsigned long key, unsigned long val) {
  map_header *header = (map_header*)BASE;
  if (rtd->new_text_end <= val || val < rtd->new_text_start) return;
  map_entry *e = ((map_entry*)(BASE + sizeof(map_header))) + (val - rtd->new_text_start) / 4;
  e->count++;
}
#endif
#else
void log_b() {
  DIE("no pol hook");
}
#endif
