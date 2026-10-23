// The driver for the Game example. It does I/O, so it sits outside the
// claws subset and stock clang compiles it with code.hpp unchanged. It
// draws the map only through cell(), and decides nothing itself: every
// move goes through key() and step().
//
//   Game              plays Bend's demo moves (left, left, up)
//   Game wasd...      plays the given keys
//   Game --play       reads keys from the terminal, one line at a time
#include <cstdio>
#include <cstring>

#include "code.hpp"

static char glyph(Cell c) {
  switch (c) {
  case Cell::Wall: return '#';
  case Cell::Flag: return 'F';
  case Cell::Start: return 'P';
  case Cell::Floor: return '.';
  }
  return '?';
}

static void draw(const Game &g) {
  for (uint32_t y = 0; y < map_h(); ++y) {
    for (uint32_t x = 0; x < map_w(); ++x) {
      std::putchar(x == g.x && y == g.y ? '@' : glyph(cell(x, y)));
    }
    std::putchar('\n');
  }
  std::printf("%s\n", is_won(g) ? "WON (this line is unreachable)" : "still not won");
}

static vec<Move> moves_of(const char *keys) {
  vec<Move> moves{};
  for (const char *k = keys; *k != '\0'; ++k) {
    Move m = Move::Up;
    if (key(static_cast<uint32_t>(*k), m)) {
      moves.push(m);
    }
  }
  return moves;
}

int main(int argc, char **argv) {
  if (argc > 1 && std::strcmp(argv[1], "--play") == 0) {
    Game g = start();
    char line[256];
    draw(g);
    while (std::printf("move (w a s d, q e z c, then enter): "), std::fgets(line, sizeof line, stdin)) {
      g = replay(g, moves_of(line));
      draw(g);
    }
    return 0;
  }
  draw(replay(start(), moves_of(argc > 1 ? argv[1] : "aaw")));
  return 0;
}
