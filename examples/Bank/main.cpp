// The driver for the Bank example. It does I/O, so it sits outside the
// claws subset and stock clang compiles it with code.hpp unchanged.
#include <cstdio>

#include "code.hpp"

int main() {
  Account alice{1, 100};
  Account bob{2, 5};
  std::printf("transfer 30: %s\n", transfer(alice, bob, 30) ? "moved" : "refused");
  std::printf("transfer 500: %s\n", transfer(alice, bob, 500) ? "moved" : "refused");
  pay_in_parts(alice, bob, 20, 5);
  std::printf("alice %u, bob %u, total %u\n", alice.balance, bob.balance, alice.balance + bob.balance);
  return 0;
}
