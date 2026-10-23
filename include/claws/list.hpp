// claws::list<T>: an immutable singly linked list. claws-lean translates
// it to Lean's `List T`, so this file is trusted: it must behave as that
// model does.
//
// In the claws subset, a list is built with `list<T>{}` (the empty list)
// and `cons(head, tail)`, and taken apart only with `match`:
//
//   xs.match([&] { return on_empty; },
//            [&](T head, list<T> tail) { return on_cons; })
//
// which claws-lean translates to `match xs with | [] => .. | h :: t => ..`.
// Every other member is for drivers outside the subset.
#pragma once

#include <initializer_list>
#include <memory>
#include <utility>
#include <vector>

namespace claws {

template <class T>
class list;

template <class T>
list<T> cons(T head, list<T> tail);

template <class T>
class list {
public:
  list() = default;
  list(const list &) = default;
  list(list &&) noexcept = default;
  list &operator=(const list &) = default;
  list &operator=(list &&) noexcept = default;

  // Nodes are shared between lists and never change, so copying a list is
  // cheap and no list can observe another. The destructor unlinks the
  // nodes it owns alone one at a time, so a long list does not recurse.
  ~list() {
    while (node_ && node_.use_count() == 1) {
      std::shared_ptr<node> next = std::move(node_->tail.node_);
      node_ = std::move(next);
    }
  }

  template <class OnNil, class OnCons>
  auto match(OnNil on_nil, OnCons on_cons) const -> decltype(on_nil()) {
    if (!node_) {
      return on_nil();
    }
    return on_cons(node_->head, node_->tail);
  }

  // For drivers: build a list from values, and copy one out.
  static list from(std::initializer_list<T> values) {
    list out;
    for (auto it = values.end(); it != values.begin();) {
      --it;
      out = cons(*it, std::move(out));
    }
    return out;
  }

  std::vector<T> to_vector() const {
    std::vector<T> out;
    for (const node *n = node_.get(); n != nullptr; n = n->tail.node_.get()) {
      out.push_back(n->head);
    }
    return out;
  }

private:
  struct node {
    T head;
    list tail;
  };

  std::shared_ptr<node> node_;

  friend list cons<T>(T head, list tail);
};

template <class T>
list<T> cons(T head, list<T> tail) {
  list<T> out;
  out.node_ = std::make_shared<typename list<T>::node>(
      typename list<T>::node{std::move(head), std::move(tail)});
  return out;
}

} // namespace claws
