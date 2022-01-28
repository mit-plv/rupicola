#include <stdint.h>
#include <stddef.h>

static uint32_t
pcg32(uint64_t *s)
{
    uint64_t m = 0x9b60933458e17d7d;
    uint64_t a = 0xd737232eeccdf7ed;
    *s = *s * m + a;
    int shift = 29 - (*s >> 61);
    return *s >> shift;
}


static void buffer_fill(uint8_t *p, size_t z)
{
    uint64_t s = 0;
    uint8_t *end = p + z;
    while (p < end) *p++ = pcg32(&s);
}

#if defined(MAIN)
#include <stdio.h>
int main() {
  uint8_t buf[1024 * 1024];
  buffer_fill(buf, sizeof(buf));
  FILE *f = fopen("testdata.bin", "wb");
  fwrite(buf, sizeof(buf), 1, f);
  fclose(f);
}
#endif
