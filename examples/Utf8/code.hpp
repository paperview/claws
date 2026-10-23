// Go's unicode/utf8, ported from Go 1.24 (src/unicode/utf8/utf8.go).
// Copyright 2009 The Go Authors. Used under Go's BSD-style license.
//
// A Go rune is an int32; here it is a uint32_t, which Go's own code
// converts it to before every range check, so negative runes behave the
// same. A slice p[at:] is a vec and an offset.
#pragma once

#include <cstdint>

#include <claws/decreases.hpp>
#include <claws/expects.hpp>
#include <claws/vec.hpp>

using claws::vec;

inline constexpr uint32_t rune_error = 0xFFFD;
inline constexpr uint32_t rune_self = 0x80;
inline constexpr uint32_t max_rune = 0x10FFFF;
inline constexpr uint32_t utf_max = 4;

inline constexpr uint32_t surrogate_min = 0xD800;
inline constexpr uint32_t surrogate_max = 0xDFFF;

inline constexpr uint8_t tx = 0b10000000;
inline constexpr uint8_t t2 = 0b11000000;
inline constexpr uint8_t t3 = 0b11100000;
inline constexpr uint8_t t4 = 0b11110000;

inline constexpr uint8_t maskx = 0b00111111;
inline constexpr uint8_t mask2 = 0b00011111;
inline constexpr uint8_t mask3 = 0b00001111;
inline constexpr uint8_t mask4 = 0b00000111;

inline constexpr uint32_t rune1_max = (1 << 7) - 1;
inline constexpr uint32_t rune2_max = (1 << 11) - 1;
inline constexpr uint32_t rune3_max = (1 << 16) - 1;

// The default lowest and highest continuation byte.
inline constexpr uint8_t locb = 0b10000000;
inline constexpr uint8_t hicb = 0b10111111;

// The names of these constants are chosen to give nice alignment in the
// table below. The first nibble is an index into acceptRanges or F for
// special one-byte cases. The second nibble is the Rune length or the
// Status for the special one-byte case.
inline constexpr uint8_t xx = 0xF1; // invalid: size 1
inline constexpr uint8_t as = 0xF0; // ASCII: size 1
inline constexpr uint8_t s1 = 0x02; // accept 0, size 2
inline constexpr uint8_t s2 = 0x13; // accept 1, size 3
inline constexpr uint8_t s3 = 0x03; // accept 0, size 3
inline constexpr uint8_t s4 = 0x23; // accept 2, size 3
inline constexpr uint8_t s5 = 0x34; // accept 3, size 4
inline constexpr uint8_t s6 = 0x04; // accept 0, size 4
inline constexpr uint8_t s7 = 0x44; // accept 4, size 4

inline constexpr uint8_t rune_error_byte0 = t3 | (rune_error >> 12);
inline constexpr uint8_t rune_error_byte1 = tx | ((rune_error >> 6) & maskx);
inline constexpr uint8_t rune_error_byte2 = tx | (rune_error & maskx);

// first is information about the first byte in a UTF-8 sequence.
inline constexpr uint8_t first[256] = {
    as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, // 0x00-0x0F
    as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, // 0x10-0x1F
    as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, // 0x20-0x2F
    as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, // 0x30-0x3F
    as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, // 0x40-0x4F
    as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, // 0x50-0x5F
    as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, // 0x60-0x6F
    as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, as, // 0x70-0x7F
    xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, // 0x80-0x8F
    xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, // 0x90-0x9F
    xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, // 0xA0-0xAF
    xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, // 0xB0-0xBF
    xx, xx, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, // 0xC0-0xCF
    s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, s1, // 0xD0-0xDF
    s2, s3, s3, s3, s3, s3, s3, s3, s3, s3, s3, s3, s3, s4, s3, s3, // 0xE0-0xEF
    s5, s6, s6, s6, s7, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, xx, // 0xF0-0xFF
};

// AcceptRange gives the range of valid values for the second byte in a
// UTF-8 sequence.
struct AcceptRange {
  uint8_t lo; // lowest value for second byte.
  uint8_t hi; // highest value for second byte.
};

// accept_ranges has size 16 to avoid bounds checks in the code that uses it.
inline constexpr AcceptRange accept_ranges[16] = {
    {locb, hicb},
    {0xA0, hicb},
    {locb, 0x9F},
    {0x90, hicb},
    {locb, 0x8F},
};

// FullRune reports whether the bytes in p[at:] begin with a full UTF-8
// encoding of a rune. An invalid encoding is considered a full rune since
// it will convert as a width-1 error rune.
inline bool full_rune(const vec<uint8_t>& p, uint32_t at) {
  claws::expects(at <= p.size());
  uint32_t n = p.size() - at;
  if (n == 0) {
    return false;
  }
  uint8_t x = first[p[at]];
  if (n >= (x & 7)) {
    return true; // ASCII, invalid or valid.
  }
  // Must be short or invalid.
  AcceptRange accept = accept_ranges[x >> 4];
  if (n > 1 && (p[at + 1] < accept.lo || accept.hi < p[at + 1])) {
    return true;
  } else if (n > 2 && (p[at + 2] < locb || hicb < p[at + 2])) {
    return true;
  }
  return false;
}

struct Decoded {
  uint32_t r;
  uint32_t size;
};

// DecodeRune unpacks the first UTF-8 encoding in p[at:] and returns the
// rune and its width in bytes. If p[at:] is empty it returns
// (rune_error, 0). Otherwise, if the encoding is invalid, it returns
// (rune_error, 1). Both are impossible results for correct, non-empty
// UTF-8.
//
// An encoding is invalid if it is incorrect UTF-8, encodes a rune that is
// out of range, or is not the shortest possible UTF-8 encoding for the
// value. No other validation is performed.
inline Decoded decode_rune(const vec<uint8_t>& p, uint32_t at) {
  claws::expects(at <= p.size());
  uint32_t n = p.size() - at;
  if (n < 1) {
    return Decoded{rune_error, 0};
  }
  uint8_t p0 = p[at];
  uint8_t x = first[p0];
  if (x >= as) {
    // The following code simulates an additional check for x == xx and
    // handling the ASCII and invalid cases accordingly. This mask-and-or
    // approach prevents an additional branch.
    // Go writes `rune(x) << 31 >> 31`, an arithmetic shift of a signed
    // rune that spreads the low bit of x over the word. claws has no
    // signed integers, so this computes the same mask unsigned.
    uint32_t mask = 0 - (static_cast<uint32_t>(x) & 1); // Create 0x0000 or 0xFFFF.
    return Decoded{(static_cast<uint32_t>(p[at]) & ~mask) | (rune_error & mask), 1};
  }
  uint32_t sz = x & 7;
  AcceptRange accept = accept_ranges[x >> 4];
  if (n < sz) {
    return Decoded{rune_error, 1};
  }
  uint8_t b1 = p[at + 1];
  if (b1 < accept.lo || accept.hi < b1) {
    return Decoded{rune_error, 1};
  }
  if (sz <= 2) { // <= instead of == to help the compiler eliminate some bounds checks
    return Decoded{static_cast<uint32_t>(p0 & mask2) << 6 | static_cast<uint32_t>(b1 & maskx), 2};
  }
  uint8_t b2 = p[at + 2];
  if (b2 < locb || hicb < b2) {
    return Decoded{rune_error, 1};
  }
  if (sz <= 3) {
    return Decoded{static_cast<uint32_t>(p0 & mask3) << 12 | static_cast<uint32_t>(b1 & maskx) << 6 |
                       static_cast<uint32_t>(b2 & maskx),
                   3};
  }
  uint8_t b3 = p[at + 3];
  if (b3 < locb || hicb < b3) {
    return Decoded{rune_error, 1};
  }
  return Decoded{static_cast<uint32_t>(p0 & mask4) << 18 | static_cast<uint32_t>(b1 & maskx) << 12 |
                     static_cast<uint32_t>(b2 & maskx) << 6 | static_cast<uint32_t>(b3 & maskx),
                 4};
}

// RuneLen returns the number of bytes in the UTF-8 encoding of the rune.
// It returns -1 (here 0xFFFFFFFF) if the rune is not a valid value to
// encode in UTF-8.
inline uint32_t rune_len(uint32_t r) {
  if (r <= rune1_max) {
    return 1;
  }
  if (r <= rune2_max) {
    return 2;
  }
  if (surrogate_min <= r && r <= surrogate_max) {
    return 0xFFFFFFFF;
  }
  if (r <= rune3_max) {
    return 3;
  }
  if (r <= max_rune) {
    return 4;
  }
  return 0xFFFFFFFF;
}

// AppendRune appends the UTF-8 encoding of r to the end of p. If the rune
// is out of range, it appends the encoding of rune_error.
inline void append_rune(vec<uint8_t>& p, uint32_t r) {
  claws::expects(p.size() <= 0xFFFFFFFA);
  uint32_t i = r;
  if (i <= rune1_max) {
    p.push(static_cast<uint8_t>(r));
  } else if (i <= rune2_max) {
    p.push(t2 | static_cast<uint8_t>(r >> 6));
    p.push(tx | (static_cast<uint8_t>(r) & maskx));
  } else if (i < surrogate_min || (surrogate_max < i && i <= rune3_max)) {
    p.push(t3 | static_cast<uint8_t>(r >> 12));
    p.push(tx | (static_cast<uint8_t>(r >> 6) & maskx));
    p.push(tx | (static_cast<uint8_t>(r) & maskx));
  } else if (i > rune3_max && i <= max_rune) {
    p.push(t4 | static_cast<uint8_t>(r >> 18));
    p.push(tx | (static_cast<uint8_t>(r >> 12) & maskx));
    p.push(tx | (static_cast<uint8_t>(r >> 6) & maskx));
    p.push(tx | (static_cast<uint8_t>(r) & maskx));
  } else {
    p.push(rune_error_byte0);
    p.push(rune_error_byte1);
    p.push(rune_error_byte2);
  }
}

// RuneStart reports whether the byte could be the first byte of an
// encoded, possibly invalid rune. Second and subsequent bytes always have
// the top two bits set to 10.
inline bool rune_start(uint8_t b) {
  return (b & 0xC0) != 0x80;
}

// Valid reports whether p consists entirely of valid UTF-8-encoded runes.
inline bool valid(const vec<uint8_t>& p) {
  uint32_t i = 0;
  // Fast path. Check for and skip 8 bytes of ASCII characters per iteration.
  while (p.size() - i >= 8) {
    claws::decreases(p.size() - i);
    // Combining two 32 bit loads allows the same code to be used for 32
    // and 64 bit platforms.
    uint32_t first32 = static_cast<uint32_t>(p[i]) | static_cast<uint32_t>(p[i + 1]) << 8 |
                       static_cast<uint32_t>(p[i + 2]) << 16 | static_cast<uint32_t>(p[i + 3]) << 24;
    uint32_t second32 = static_cast<uint32_t>(p[i + 4]) | static_cast<uint32_t>(p[i + 5]) << 8 |
                        static_cast<uint32_t>(p[i + 6]) << 16 | static_cast<uint32_t>(p[i + 7]) << 24;
    if (((first32 | second32) & 0x80808080) != 0) {
      // Found a non ASCII byte (>= rune_self).
      break;
    }
    i += 8;
  }
  uint32_t n = p.size();
  while (i < n) {
    claws::decreases(n - i);
    uint8_t pi = p[i];
    if (pi < rune_self) {
      i++;
      continue;
    }
    uint8_t x = first[pi];
    if (x == xx) {
      return false; // Illegal starter byte.
    }
    uint32_t size = x & 7;
    // Go writes `i+size > n`. Go's int has 64 bits, but here i + size can
    // wrap past 2^32 when p holds nearly 2^32 bytes, which would let a
    // truncated rune through and read past the end of p. The safety
    // obligation found it (p.size = 2^32 - 1, i = 2^32 - 2, p[i] = 0xF4).
    // n - i cannot wrap, since i < n.
    if (size > n - i) {
      return false; // Short or invalid.
    }
    AcceptRange accept = accept_ranges[x >> 4];
    if (uint8_t c = p[i + 1]; c < accept.lo || accept.hi < c) {
      return false;
    } else if (size == 2) {
    } else if (uint8_t c = p[i + 2]; c < locb || hicb < c) {
      return false;
    } else if (size == 3) {
    } else if (uint8_t c = p[i + 3]; c < locb || hicb < c) {
      return false;
    }
    i += size;
  }
  return true;
}

// ValidRune reports whether r can be legally encoded as UTF-8. Code points
// that are out of range or a surrogate half are illegal.
inline bool valid_rune(uint32_t r) {
  if (r < surrogate_min) {
    return true;
  }
  if (surrogate_max < r && r <= max_rune) {
    return true;
  }
  return false;
}
