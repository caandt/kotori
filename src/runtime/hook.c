#include "runtime.h"

#ifdef A8_HOOK
asm(R"(
hook_epilogue:
  ldp x16, x17, [sp], #16
  ret
.global hook
hook:
  add x17, sp, #16
)");
void hook_epilogue();
static inline void add(unsigned long, unsigned long);
void _hook() {
  unsigned long register src asm("x16");
  unsigned long register *dst asm("x17");
  rtd_t *rtd = get_rtd();
  if (*dst < rtd->text_end && rtd->text_start <= *dst)
    *dst = lookup(rtd, *dst);
  add(src, *dst);
  return hook_epilogue();
}
#if A8_HOOK == 'P'
static inline void add(unsigned long key, unsigned long val) {
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
#elif A8_HOOK == 'C'
static inline void add(unsigned long key, unsigned long val) {
  map_header *header = (map_header*)BASE;
  long offset = sizeof(map_header);
  for (int i = 0; i < MAP_HEADER_SEGS; i++) {
    if (!header->segs[i].end) return;
    if (header->segs[i].end <= val || val < header->segs[i].start) {
      offset += header->segs[i].size * sizeof(map_entry);
    } else {
      map_entry *e = ((map_entry*)(BASE + offset)) + (val - header->segs[i].start) / 4;
      e->count++;
      return;
    }
  }
}
#endif
#else
void hook() {
  DIE("no hook function");
}
#endif
