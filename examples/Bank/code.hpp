// The claws subset part of the Bank example: transfers between accounts
// passed by reference, as C++ code usually does it.
#pragma once

#include <cstdint>

struct Account {
  uint32_t id;
  uint32_t balance;
};

// Moves amount from `from` to `to`, if `from` holds enough and `to` has
// room. Returns whether it moved anything.
inline bool transfer(Account& from, Account& to, uint32_t amount) {
  if (from.balance < amount) {
    return false;
  }
  if (to.balance > 0xFFFFFFFFu - amount) {
    return false;
  }
  from.balance -= amount;
  to.balance += amount;
  return true;
}

// Tries the same transfer n times, as a payment plan would.
inline void pay_in_parts(Account& from, Account& to, uint32_t amount, uint32_t n) {
  for (uint32_t i = 0; i < n; ++i) {
    transfer(from, to, amount);
  }
}
