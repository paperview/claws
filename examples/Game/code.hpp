// Winning Is Impossible, ported from Bend 2's demo
// (demos/app_win_is_bug_2d), Copyright 2026 HigherOrderCO, under the
// Apache License 2.0; NOTICE says what changed. The whole game and nothing
// else: a torus map, a walled room, a flag, eight moves. Stepping onto the
// flag's cell is the win. LAWS.lean claims that you can't win, and
// PROOF.lean proves it.
#pragma once

#include <cstdint>

#include <claws/vec.hpp>

using claws::vec;

enum class Move { Up, Down, Left, Right, UpLeft, UpRight, DownLeft, DownRight };

struct Game {
  uint32_t x;
  uint32_t y;
  bool won;
};

// Map
// The map is a torus: walk off one edge and come back on the opposite one.
// The flag sits in a room in the top left corner, sealed by two walls. The
// room's other two walls are the far edges of the screen, which on a torus
// are the other side of the room.

inline uint32_t map_w() { return 12; }
inline uint32_t map_h() { return 8; }
inline uint32_t room_w() { return 3; }
inline uint32_t room_h() { return 3; }
inline uint32_t flag_x() { return 1; }
inline uint32_t flag_y() { return 1; }
inline uint32_t start_x() { return 8; }
inline uint32_t start_y() { return 5; }

inline bool wall(uint32_t x, uint32_t y) {
  bool east = x == room_w() && y <= room_h();
  bool south = x <= room_w() && y == room_h();
  bool north = x <= room_w() && y == map_h() - 1;
  bool west = x == map_w() - 1 && y <= room_h();
  return east || south || north || west;
}

inline bool on_flag(uint32_t x, uint32_t y) {
  return x == flag_x() && y == flag_y();
}

// Step

inline uint32_t warp_up(uint32_t y) { return y == 0 ? map_h() - 1 : y - 1; }
inline uint32_t warp_down(uint32_t y) { return y + 1 == map_h() ? 0 : y + 1; }
inline uint32_t warp_left(uint32_t x) { return x == 0 ? map_w() - 1 : x - 1; }
inline uint32_t warp_right(uint32_t x) { return x + 1 == map_w() ? 0 : x + 1; }

// Moves g to (tx, ty), unless a wall is there. Reaching the flag wins.
inline void move_to(Game& g, uint32_t tx, uint32_t ty) {
  if (wall(tx, ty)) {
    return;
  }
  g.x = tx;
  g.y = ty;
  if (on_flag(tx, ty)) {
    g.won = true;
  }
}

// Moves g diagonally to (tx, ty), unless the move cuts a corner: a
// diagonal step may not squeeze between two walls, the cells beside it in
// each straight direction.
inline void move_diag(Game& g, uint32_t tx, uint32_t ty) {
  if (wall(tx, g.y) && wall(g.x, ty)) {
    return;
  }
  move_to(g, tx, ty);
}

inline void step(Game& g, Move m) {
  switch (m) {
  case Move::Up:
    move_to(g, g.x, warp_up(g.y));
    break;
  case Move::Down:
    move_to(g, g.x, warp_down(g.y));
    break;
  case Move::Left:
    move_to(g, warp_left(g.x), g.y);
    break;
  case Move::Right:
    move_to(g, warp_right(g.x), g.y);
    break;
  case Move::UpLeft:
    move_diag(g, warp_left(g.x), warp_up(g.y));
    break;
  case Move::UpRight:
    move_diag(g, warp_right(g.x), warp_up(g.y));
    break;
  case Move::DownLeft:
    move_diag(g, warp_left(g.x), warp_down(g.y));
    break;
  case Move::DownRight:
    move_diag(g, warp_right(g.x), warp_down(g.y));
    break;
  }
}

inline Game start() {
  return Game{start_x(), start_y(), false};
}

// The board after playing moves from g, in order.
inline Game replay(Game g, const vec<Move>& moves) {
  for (uint32_t i = 0; i < moves.size(); ++i) {
    step(g, moves[i]);
  }
  return g;
}

inline bool is_won(const Game& g) {
  return g.won;
}

// Keys
// The driver sends each key press as its character code and plays the move
// this sets, if it returns true: w, a, s and d, and the diagonals q, e, z
// and c.

inline bool key(uint32_t k, Move& m) {
  if (k == 119) {
    m = Move::Up;
    return true;
  }
  if (k == 115) {
    m = Move::Down;
    return true;
  }
  if (k == 97) {
    m = Move::Left;
    return true;
  }
  if (k == 100) {
    m = Move::Right;
    return true;
  }
  if (k == 113) {
    m = Move::UpLeft;
    return true;
  }
  if (k == 101) {
    m = Move::UpRight;
    return true;
  }
  if (k == 122) {
    m = Move::DownLeft;
    return true;
  }
  if (k == 99) {
    m = Move::DownRight;
    return true;
  }
  return false;
}

// Show
// What the driver draws at each cell. It draws the map only through this
// function, so LAWS.lean can state its flag law on what the player sees.

enum class Cell { Floor, Wall, Flag, Start };

inline Cell cell(uint32_t x, uint32_t y) {
  if (wall(x, y)) {
    return Cell::Wall;
  }
  if (on_flag(x, y)) {
    return Cell::Flag;
  }
  if (x == start_x() && y == start_y()) {
    return Cell::Start;
  }
  return Cell::Floor;
}
