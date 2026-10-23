// The driver for the Utf8 example. It does I/O, so it sits outside the
// claws subset and stock clang compiles it with code.hpp unchanged.
//
//   Utf8              checks a few strings, including Go's test cases
//   Utf8 text...      decodes each argument rune by rune
#include <cstdio>
#include <cstring>

#include "code.hpp"

static vec<uint8_t> bytes_of(const char *s) {
  vec<uint8_t> p{};
  for (const char *c = s; *c != '\0'; ++c) {
    p.push(static_cast<uint8_t>(*c));
  }
  return p;
}

static void show(const char *label, const vec<uint8_t> &p) {
  std::printf("%-22s valid=%-5s runes:", label, valid(p) ? "true" : "false");
  uint32_t at = 0;
  while (at < p.size()) {
    Decoded d = decode_rune(p, at);
    std::printf(" U+%04X", d.r);
    at += d.size;
  }
  std::printf("\n");
}

int main(int argc, char **argv) {
  if (argc > 1) {
    for (int i = 1; i < argc; ++i) {
      show(argv[i], bytes_of(argv[i]));
    }
    return 0;
  }
  show("ascii", bytes_of("hello, world"));
  show("euro", bytes_of("\xE2\x82\xAC"));
  show("emoji", bytes_of("\xF0\x9F\x98\x80"));
  show("overlong slash", bytes_of("\xC0\xAF"));
  show("surrogate half", bytes_of("\xED\xA0\x80"));
  show("past U+10FFFF", bytes_of("\xF4\x90\x80\x80"));
  show("truncated", bytes_of("\xE2\x82"));
  show("long ascii run", bytes_of("abcdefghijklmnopqrstuvwxyz\xE2\x82\xAC"));
  // Round trip every scalar value through append_rune and decode_rune.
  uint32_t bad = 0;
  for (uint32_t r = 0; r <= max_rune; ++r) {
    vec<uint8_t> p{};
    append_rune(p, r);
    Decoded d = decode_rune(p, 0);
    bool ok = valid_rune(r) ? (d.r == r && d.size == rune_len(r) && valid(p))
                            : (d.r == rune_error && d.size == 3);
    bad += ok ? 0 : 1;
  }
  std::printf("round trip of U+0000..U+10FFFF: %u failures\n", bad);
  return bad == 0 ? 0 : 1;
}
