# claws: design notes

claws is a verifiable subset of C++ modeled on Bend 2's Laws feature. A
human states laws about a program. An AI (or a human) proves them. A gate
command refuses the build until every law holds. Proofs never reach the
compiled binary.

These notes come from reading Bend 2 at `github.com/bendlang/bend`
(commit 881cb2e): the BendTT paper (`bend2/docs/BendTT/main.typ`), the
kernel (`bend2/bendtt.lean`), the Bend to kernel translation
(`bend2/safe.ts`) and the demos.

## How to read these notes

These notes were kept as the work went, and each section was written when
its step was done. They fall into four parts:

1. **The design:** how Bend 2's Laws work, what claws keeps and changes,
   and how the repository is laid out (from "How Bend's Laws work" to
   "Toolchain").
2. **The plan:** the milestones, the step to a real program, and the
   design of the trusted translation, which checks every translation
   against a formal semantics ("Milestones" to "A trusted translation").
3. **The lessons,** one section per milestone and per stage, in order.
   Each says what broke and the rule it led to; the rules for proofs are
   collected in `CLAUDE.md`.
4. **Prior art,** and a comparison of proof sizes with Bend 2.

## How Bend's Laws work

- `LAWS.bend` holds claims, written by a human, which the AI must not edit.
  Example: `law add_zero: for x: Nat {Nat.add(x, 0n) == x : Nat}`.
- `PROOF.bend` imports `LAWS.bend` and proves each law with a def of the
  same name. The AI writes it along with the code.
- `bend PROOF.bend` is the gate. It prints SOME PROOFS FAIL while any law
  is open or false, and ALL PROOFS CHECK once every law holds.
- A proposition is a type and a proof is a def of that type. There are no
  tactics. Matching splits the goal, a recursive call is the induction
  hypothesis, `%e : P` rewrites with an equation.
- `--verdict` rechecks everything with a small kernel (`bendtt.lean`,
  about 4,000 lines) whose consistency is proven in Lean. The parser and
  the TypeScript translation into that kernel are not proven.

Laws are not a bolt-on. They fall out of BendTT, an affine dependent type
theory. Running ("live") code must use each variable at most once, may copy
only first-order data, and may recurse only on smaller arguments. Types,
laws and proofs are "dead" code: checked, never run, erased.

## Key decision: no custom kernel

The BendTT kernel exists to solve problems Bend chose to have: `Type :
Type`, negative datatypes and impredicative function types, each of which
normally makes a logic inconsistent. A C++ subset needs none of them.

claws translates the subset into Lean 4 and proves laws there. Lean's
kernel is the trusted checker. Proof erasure is automatic, because proofs
never enter the C++ and stock clang compiles the code unchanged.

The trust base is the same shape as Bend's `--verdict`:

1. The Clang front end.
2. The claws translator (C++ AST to Lean).
3. The Lean models of library types and foreign code.
4. Lean's kernel.
5. Clang codegen agreeing with the C++ semantics we modeled.

## What carries over from Bend

| Bend | claws |
|---|---|
| `LAWS.bend` (human) and `PROOF.bend` (AI), one gate command | `LAWS.lean` and `PROOF.lean`, gate is `lake build` |
| Dead code (laws, proofs) is checked and never run | Laws and proofs live in Lean and never reach the binary |
| Affinity: a value holding functions is used at most once | Move-only types, no use after move, no aliasing |
| `U32` modeled as a 32-bit word of Bools in `base.bend` | `uint32_t` modeled as Lean's `BitVec 32`, with `bv_decide` for automation |
| Opaque defs with models for foreign code and effects | Same. I/O and anything outside the subset gets a trusted Lean model |
| F32 is axiomatic | Same. Nothing about floating point is provable |

## What is new work

### Mutation and references

Bend has no mutation. Follow Aeneas (Rust to Lean) instead: a `T&`
parameter becomes "takes a T, returns the new T". Phase 1 allows no
references at all: pass and return by value. Phase 2 adds `T&` with strict
rules. A reference is never stored, never returned, and never aliased by
another argument of the same call.

### Loops

Bend only has recursion, checked by "descent" (arguments shrink left to
right). claws translates loops into recursive Lean functions and lets
Lean's `termination_by` replace the descent check. A `for` loop over a
bounded counter needs nothing extra. A `while` loop needs a decreasing
measure, supplied as an attribute such as `[[claws::decreases(n - i)]]`.
An unbounded loop, like a server main loop, needs a counter, as in Bend.

### Undefined behavior

Bend has none. The subset bans signed overflow, null, uninitialized reads
and raw pointers. Operations that can fail at run time, like indexing,
become proof obligations the translator emits automatically.

### Laws are not C++

In Bend a proof is an ordinary def, because Bend has dependent types. C++
has none, so laws are written in Lean. C++26 contracts (`pre`/`post`) may
later serve as sugar for simple laws, if the Clang in use supports them.

## Library versus tool

The library supplies vocabulary. The tool enforces everything.

The library (`include/claws/`) is the `base.bend` analogue:

- Value-semantic types that leak no pointers or iterators:
  `claws::list<T>`, `claws::option<T>`, `claws::array<T, N>`. Each has a
  Lean model and proven lemmas in `lean/Claws/Base.lean`. `std::vector` is
  too large to model (allocators, iterators, exceptions).
- Move-only wrappers for affine values. C++23's `std::move_only_function`
  already covers closures.
- Attributes for loop measures and for marking law-relevant functions.

Only the Clang tool can:

- Reject anything outside the subset.
- Check ownership and affinity. C++ compiles use after move without
  complaint, and clang-tidy's `bugprone-use-after-move` is a heuristic.
- Rule out undefined behavior.
- Translate the program to Lean.

## Layout

```
tools/claws-lean/          Clang LibTooling: subset check and C++ to Lean
tools/claws-ast/           prints Clang's AST as a Lean term, for the semantics
include/claws/list.hpp     claws::list<T>, translated to Lean's List T
include/claws/expects.hpp  claws::expects(c), a precondition
include/claws/decreases.hpp claws::decreases(m), a while loop's measure
include/claws/vec.hpp      claws::vec<T>, translated to Lean's Array T
lean/Claws/Verdict.lean    the #claws_verdict gate command
lean/Claws/Sem.lean        the semantics of the subset (trusted, reviewed once)
lean/Claws/Det.lean        proof that the semantics is deterministic
lean/Claws/Interp.lean     an interpreter for it, proven sound
lean/Claws/Codec.lean      decodings of values, proof aids for claws_valid
lean/Claws/Validate.lean   claws_valid, which proves a Valid law
lean/Claws/Loop.lean       claws_loop, which proves what a loop does
scripts/gate.sh            translate, check laws, diff, compile with stock clang
scripts/diff.sh            differential test: C++ against the Lean translation
examples/Sorting/          insertion sort over claws::list (milestone 2)
examples/Stats/            running statistics with local mutation (milestone 3)
examples/Loops/            counting loops, nested loops (milestone 4)
examples/Bank/             transfers through T& parameters (milestone 5)
examples/Bits/             division, shifts and preconditions (milestone 6)
examples/Vectors/          reading, writing and growing vecs (milestone 7)
examples/Game/             Bend's "winning is impossible" game (milestone 9)
examples/Utf8/             Go's unicode/utf8, a real program (milestone 10)
CLAUDE.md                  file ownership and the rules for PROOF.lean
examples/Clamp/
  code.hpp                 the claws subset (translated)
  main.cpp                 the driver, outside the subset (I/O)
  Code.lean                generated from code.hpp, never edited
  Ast.lean                 generated by claws-ast, never edited
  LAWS.lean                laws, written by a human
  PROOF.lean               proofs, written by the AI
  Verdict.lean             the gate, owned by a human
```

`claws::list<T>` needs no `Base.lean` model: it maps straight onto
Lean's core `List`, and the claim that the header behaves like `List` is
part of the trust base. A library type with no core Lean counterpart will
need a model in `lean/Claws/Base.lean`. The subset check lives inside
claws-lean for now. It splits into `claws-check` once the ownership rules
make it large.

## Running

```
scripts/gate.sh examples/Clamp
```

The gate rebuilds claws-lean if needed, regenerates `Code.lean`, builds
`Clamp.Verdict` with Lake, and only then compiles and runs `main.cpp`
with stock clang. It exits nonzero if the C++ leaves the subset, if a
proof fails, or if any law is open, uses `sorry`, or relies on an
unexpected axiom.

A law is a `def` of type `Prop` in namespace `<Project>.Laws`. Its proof
is a theorem of the same name in `<Project>.Proof`. Each project needs a
`[[lean_lib]]` entry in `lakefile.toml`.

## Toolchain

- Homebrew LLVM 23 (`/opt/homebrew/opt/llvm`, keg-only) for the Clang
  libraries; `gate.sh` takes another LLVM from `LLVM_PREFIX` or
  `llvm-config`. CMake bakes its `clang++`, resource directory and the macOS
  SDK path into claws-lean, because LibTooling otherwise looks for
  builtin headers next to the claws-lean binary.
- Lean 4.35.0 via elan, pinned in `lean-toolchain`. No Mathlib yet.
  `BitVec` and `bv_decide` are in core.
- Apple clang compiles both claws-lean and the user's C++.

## Milestones

1. **Done.** Pure functions over `uint32_t`, `bool` and aggregate
   structs, with `const` locals, `if` and `?:`. No loops, references or
   recursion. `examples/Clamp` proves five laws with `bv_decide`.
2. **Done.** `claws::list<T>` with `list<T>{}`, `cons` and
   `xs.match(lambda, lambda)`; `enum class` with exhaustive `switch`;
   recursion, with termination left to Lean. `examples/Sorting` proves
   that insertion sort is sorted, a permutation, and keeps the sum.
3. **Done.** Local mutation: `=`, `+= -= *= &= |= ^=`, `++`, `--` on
   locals and parameters, including struct fields (`s.lo.x = v`). Each
   assignment becomes a shadowing `let`. A branch, block or `switch` that
   falls through becomes an expression over the outer variables it
   assigns, bound back with `let (a, b) := ..`. `switch` arms may end in
   `break`. `examples/Stats` proves five laws about running statistics.
4. **Done.** Counting loops: `for (uint32_t i = a; i < b; ++i)` whose
   body never returns and assigns neither `i` nor anything `b` reads.
   Each loop becomes a recursive Lean function `f.loopN` over the
   variables it uses, checking `i < b` on every step as C++ does, with
   `termination_by (b - i).toNat` proved by `bv_omega` in the generated
   code. `examples/Loops` proves four laws, including nested loops.
5. **Done.** `T&` and `const T&` parameters, under mutable value
   semantics as in Hylo: references are parameters only, never locals,
   fields or results. `bool f(A& a, B& b)` becomes a Lean function
   returning `Bool × A × B`, and a call rebinds what it modifies,
   `let (r'1, a, b) := f a b`, including field paths (`f(s.lo)`). `void`
   is allowed with at least one `T&`. `examples/Bank` proves six laws,
   including conservation of money across a loop of transfers.
6. **Done.** Proof obligations for partial operations: `/` and `%`
   (divisor not zero) and `<<`, `>>` (amount below 32), plus their
   compound assignments. A function's leading `claws::expects(c);`
   statements are its precondition `f.pre`. The translator generates
   `f.safe`, a Bool function that mirrors f and checks each partial
   operation and each callee's `pre` on the path f takes, and an
   obligation `∀ args, f.pre args → f.safe args` in
   `<Project>.Laws.Safety`, which the verdict requires like a law.
   Indexing will use the same mechanism in milestone 7.
   `examples/Bits` proves five laws and five obligations.
7. **Done.** `claws::vec<T>`, mapped to Lean's `Array`: `vec<T>{}`,
   `vec<T>(n, fill)`, `size()`, `v[i]`, `v[i] = x` and `push`. Assignment
   paths now mix fields and indexes (`s.items[i].x += 1`), and a `T&`
   argument may be an element (`f(v[i])`). Every index must be below
   `size()`, and every push must keep the size below 2^32 - 1, as part of
   the safety obligation. A loop bound of `v.size()` may coexist with
   element writes to v, since they keep its size. `examples/Vectors`
   proves seven laws and five obligations.
8. **Done.** Differential testing as a tool. `claws-lean --diff-cpp
   --diff-lean` writes two harnesses that run every function on the same
   generated inputs, and `scripts/diff.sh` compiles one, evaluates the
   other and compares them line by line. The gate runs it with 100 inputs
   per function.
9. **Done.** A port of Bend's `app_win_is_bug_2d` demo as the first real
   program: `examples/Game`. Both of Bend's laws hold (no sequence of
   moves wins; the player never stands on the drawn flag), plus the
   safety of `replay`. Deleting the room's far-edge wall makes the game
   winnable, and the gate blocks it with the counterexample (11, 0). Diagonal moves came later from an agent trial, without corner
   cutting.
10. **Done.** A port of a real, non-demo program, Go's `unicode/utf8`:
    `examples/Utf8`. It brought `uint8_t`, `inline constexpr` constants
    and lookup tables, `while` loops with `claws::decreases`, `break`,
    `continue` and early `return`, branches that sometimes return, and
    `if (T x = e; c)`. Seven laws compare it with UTF-8 as the Unicode
    Standard defines it, and four safety obligations cover it.
11. Later: counting down, signed integers, `uint64_t`, methods,
    templates, several headers.

## Toward a real tool

The prototype shows the idea works end to end, including an AI working
against laws it cannot edit. What it does not yet show is that the idea
holds up on code nobody chose for being easy to verify. In order:

1. **Port a real, non-demo program.** Done: Go's `unicode/utf8`
   (`examples/Utf8`, milestone 10). See "Lessons from the utf8 port".
2. **Fill the language gaps.** `while` with a measure, `break` and
   `continue`, early return from loops; signed integers (overflow is
   undefined, so it becomes an obligation), `uint8_t` and `uint64_t`;
   member functions as `T& this`, templates, sum types like
   `std::optional` and `std::variant`, several headers. Rejections should
   say why a construct is outside the subset and show the subset form.
3. **Laws in C++.** Writing Lean is the biggest barrier for C++
   developers. A `claws::law` function returning `bool`, its parameters
   universally quantified, could translate to the Lean statement, and
   C++26 contracts (`pre`, `post`) could map onto `expects` and
   postconditions.
4. **Proof automation.** Most proofs so far follow one recipe: unfold,
   `repeat' split`, `bv_decide`, and `fun_induction` for loops. A
   `claws_auto` tactic would close the easy cases and leave hand or AI
   proofs for real invariants such as Game's `safe`.
5. **Build integration.** Read `compile_commands.json`, add a CMake
   target and a CI action, verify incrementally (only functions that
   changed), and show failed laws and counterexamples as clangd
   diagnostics.
6. **Shrink the trusted base.** The translator is about 3,600 unverified
   lines, guarded only by differential testing. The plan is in "A trusted
   translation" below: a formal semantics of the subset, validation of
   every translation against it, and in the end a translator written in
   Lean and proven once. `list.hpp` and `vec.hpp` are trusted to match
   their Lean models, and `bv_decide` proofs trust Lean's compiler; offer
   a fully kernel-checked mode.
7. **Performance.** Measure the cost of value semantics: `vec` copies on
   pass by value, and `list` allocates `shared_ptr` nodes. Compare with
   idiomatic C++.

## A trusted translation

A law is proven about `Code.lean`. Until stage A, `Code.lean` was
trusted to mean what `code.hpp` means, and that trust rested on 3,600
lines of unverified C++ in claws-lean, checked only by the differential
test. Bend is in the same position with its elaborator, as its paper
says, but claws can do better, in stages of increasing strength. Stages
A to D are done: every function in the examples is validated against a
formal semantics of the subset.

### The target

The end state is a **verified translator**: a translation from the
subset to Lean, written in Lean, with one theorem, proven once, that
every translation it produces means what the C++ means. What remains
trusted is then:

- Clang's front end, which parses and type checks, as now.
- A printer that writes Clang's AST as a Lean term. It makes no
  decisions: every node it does not know becomes `other "<kind>"`,
  which the semantics gives no meaning to.
- `Sem.lean`, the semantics of the subset: one rule per kind of AST
  node, each citing the clause of the C++ standard it follows. It is
  reviewed once against the standard, not once per program.
- Lean's kernel, clang's code generation, and the library headers, as
  now.

The subset check, the translation, the safety obligations and
claws-lean itself all leave the trusted base. A construct claws-lean
mishandles, or one outside the subset that slips past it, has no
derivation in the semantics, so its validation cannot be proven.

### The design

- **The semantics is a relation, `Exec`.** A derivation exists only for
  a run that is defined and ends. Undefined behavior (signed overflow, a
  bad index, reading a variable before it is initialized, falling off
  the end of a function that returns a value) has no rule, so the run
  gets stuck, as in CompCert. The rules are syntax directed, so `Exec`
  is deterministic: a derivation that ends in `ret v` says the C++
  returns v and nothing else.
- **The AST mirrors Clang's.** Clang has already decided every implicit
  conversion, promotion and value category, so the semantics only says
  what each node does. An `int` is a mathematical integer that gets
  stuck outside 32 bits, which is the standard's own rule; the
  translator's reasoning about `uint8_t` promotion is then checked
  instead of trusted.
- **Each variable is named by where it is declared** (`x@16:32`), so
  shadowing and `uint32_t x = x;` mean what C++ says.
- **Validation is a law.** For each function the printer states
  `Laws.Valid.f`: for all arguments, the function returns the encoding
  of `Code.f` applied to them. The verdict requires it like any other
  law. With a precondition, it holds for arguments that meet it.
- **Safety follows from validation.** A function that provably returns
  never reaches undefined behavior on the way, so the generated
  `Laws.Safety` obligations become corollaries, and the `f.safe`
  functions become proof aids instead of trusted definitions.
- **An interpreter does the work.** `exec`, a Lean function with fuel,
  is proven sound against `Exec` once. A validation proof runs it
  symbolically on the function's AST and compares the result with
  `Code.f`, with the usual tactics (`simp`, `bv_decide`). This
  interpreter is the seed of the verified translator.

### Stages

- **A. The Clamp fragment.** Done (see "Lessons from stage A").
  `Sem.lean` for `uint32_t`, `bool`, `int`
  literals, structs, `const` locals, `if`, `?:`, `&&`, `||`, calls and
  `return`. The printer `claws-ast` writes `Ast.lean`, a separate tool
  that shares only Clang with claws-lean, so a bug in one cannot hide
  the same bug in the other. `Valid.*` for every Clamp function, first
  by hand, then by a `claws_validate` tactic. The verdict reports
  whether a project's translation is validated.
- **B. Mutation and partial operations.** Done (see "Lessons from
  stage B"). Assignment, compound assignment, `++`, blocks, `switch`,
  enums, `/`, `%`, shifts and `claws::expects`. A validated function
  provably runs without undefined behavior whenever its `claws::expects`
  hold, so for it the generated safety obligation adds nothing to the
  trust argument; the verdict still requires both for now.
- **C. References.** Done (see "Lessons from stage C"). Real C++
  lvalues: a `T&` parameter names an object in the caller's memory. The
  translator's "takes a T, returns the new T" reading is no longer
  trusted: each function's validation law says, for any memory and any
  distinct objects as its `T&` arguments, that the C++ leaves them as
  `Code.f` does.
- **D. Loops, recursion, lists and vecs.** Done (see "Lessons from
  stage D"). `for` and `while` by induction over the loop function,
  recursion by induction over the translated function, `claws::list`
  and `claws::vec` as built in types whose rules state what the
  headers do.
- **E. Testing the semantics.** The semantics becomes the trusted part,
  so it is tested as claws-lean is now: the interpreter runs as a third
  column of the differential test (C++, `Code.lean`, semantics), and
  clang's constant evaluator, which must reject undefined behavior,
  serves as an independent oracle for the cases where a run gets
  stuck.
- **F. The verified translator.** Prove the interpreter's unfolding
  produces `Code.lean` itself: a Lean command reads `Ast.lean`, defines
  each `Code.f` by partially evaluating the interpreter on its AST
  (with loops becoming recursive functions as they do now), and proves
  `Valid.f` by the one theorem that the interpreter is sound. claws-lean
  then retires from the trusted base entirely, kept only for its error
  messages, which say why a construct is outside the subset.

Stages A to E are translation validation: each translation is checked,
and a bad one fails its own `Valid` law. Stage F turns the check into a
proof about the translator, so no translation can fail. Reading first:
BRiCk (C++ semantics over a Clang AST dump, in Coq), Cerberus (C's
undefined behavior, catalogued), Aeneas (the symbolic semantics behind
its Rust to Lean translation), CompCert's Clight (a small big-step
semantics), and CakeML's proof-producing translator, which does stage
F's job in the other direction.

## Lessons from milestone 1

- `bv_decide` in Lean 4.35 no longer uses `Lean.ofReduceBool`. Each proof
  gets its own axiom, `<theorem>._native.bv_decide.ax_..`, which trusts
  Lean's compiler. The verdict allows these and marks the law
  "trusts Lean's compiler". A stricter mode could reject them.
- C++ names can collide with Lean's root names. Inside the generated
  namespace `min` resolves to the C++ one, but `open Clamp.Code` makes
  `min` ambiguous with Lean's `Min.min`. Lean reports this as an error
  rather than guessing, so proofs write `Code.min`.
- `bv_decide` turns a false law into a concrete counterexample. Breaking
  `clamp` produced `x = 4294967295, lo = hi = 4294967294`. That is the
  feedback loop an AI needs to retry.
- `uint32_t` is the only integer type in the subset because narrower
  unsigned types promote to `int`, where overflow is undefined.

## Lessons from milestone 2

- Lean's termination checker replaces Bend's descent check outright.
  `sort(o, xs)` recursing on its whole input fails in `Code.lean` with
  "failed to infer structural recursion", so claws-lean needs no
  termination analysis of its own.
- Pattern matching as `xs.match(lambda, lambda)` is real C++ that runs,
  and maps one to one onto a Lean `match`. Because nothing in the subset
  mutates, a lambda's captures can be translated as the outer variables.
- Library names are trusted only when declared under `include/claws/`.
  A fake `claws/list.hpp` beside the code, whose `cons` drops elements,
  is rejected as an unknown type rather than translated as `::`.
- Structural proofs (sortedness, permutation) need ordinary induction.
  `bv_decide` still closes the leaves: totality and transitivity of the
  order, and commutativity of wrapping addition for `sum`.
- A broken `insert` shows up as a type mismatch inside a proof, not as a
  counterexample. That tells an AI which proof step broke but not why, a
  weaker signal than `bv_decide` gives.

## Lessons from milestone 3

- Mutation of locals is pure in disguise. Shadowing `let` covers
  straight-line code, and a join on the assigned variables covers
  branches. Requiring each branch to either always return or never
  return means the code after a branch is never duplicated.
- What the translator rejects: a branch that sometimes returns, an
  assignment inside an expression (`a + (b = 2)`, `b = a++`), a lambda
  assigning a variable it captures, a case that falls into the next, a
  switch mixing `return` and `break`, and an uninitialized local.
- A first differential test (360 input combinations through the
  compiled C++ and through Lean's evaluation of the translation) agreed
  on every line. It exercised shadowing inside a block, nested field
  updates, a partial `switch` with `break`, and mutation before a match.
- Proofs must not depend on the shape of the code. The first Stats
  proofs used `split <;> split`, so a refactor broke them for structural
  reasons and gave the AI no useful signal. Written as `repeat' split`
  then `bv_decide`, the step lemmas survive refactors. A real bug
  (`else if` in `record`, which skips the max update for the first value
  seen) then fails exactly one lemma, with a concrete counterexample.
- Generated Lean sets `linter.unusedVariables false`, since C++ allows a
  store that is overwritten before it is read.

## Lessons from milestone 4

- The loop translation is literal. The loop function re-checks `i < b` on
  every step, as C++ does, rather than precomputing an iteration count.
  The translator only has to be trusted to copy the loop, not to reason
  about it. Termination is Lean's job, and for the counting shape
  `bv_omega` always proves it.
- Generated code must read the way a person writes Lean. Literals were
  `0#32`, which Lean treats as a different term from the `0` a law or
  proof writes, so rewrites failed for no semantic reason. They are now
  `(0 : BitVec 32)`.
- Generated names must not collide with C++ names. A parameter `h` hid
  the loop hypothesis `h`; the hypothesis is now `lt'`, since a C++
  identifier cannot contain an apostrophe.
- `fun_induction` on a loop function gives exactly the two cases a loop
  invariant needs: one step with an induction hypothesis, and exit.
  `grind` closes wrapping ring arithmetic (`2 * (s + i) + n * (n - 1)`)
  that `bv_decide` would have to bit-blast. These proofs are kernel
  checked and do not trust Lean's compiler.

## Lessons from milestone 5

- Exclusivity is about references only. A by-value argument is copied
  before the callee runs, so `keep(x, x)` with `keep(uint32_t&, uint32_t)`
  is well defined and allowed. What is rejected is two reference
  arguments (`T&` with `T&` or `const T&`) that overlap: `swap(x, x)` and
  `touch(p, p.a)` are rejected, `swap(p.a, p.b)` is allowed.
- A call that modifies a `T&` argument may only be a statement, an
  initializer, an assignment's right side or a returned value. Inside a
  larger expression C++ leaves the order of its effects unspecified, so
  the program would have no single meaning to translate.
- `x = f(x)` and `x += f(x)` follow C++17 order: the call and its effect
  on x happen first, then the assignment.
- A void function may fall off its end. The translator appends an
  implicit `return`, which hands back the `T&` parameters.
- Laws only guard what they state. Changing `<` to `<=` in `transfer`
  made it refuse exact-balance transfers, and the gate passed it,
  correctly, since refusing conserves money. Adding the law
  `moves_when_possible` caught it. Writing laws is the human's job for
  this reason.
- Proofs must be shape-independent, again. The first `transfer_cases`
  proof broke on both bugs for structural reasons. Rewritten as
  `repeat' split` with `bv_omega` in each branch, it fails only when a
  claim is false, and the missing overflow guard then shows up as a
  counterexample with `amt + to.balance >= 2^32`.
- A match lambda may not assign a variable it captures, so recursion
  that updates an inout through a match must copy it into a lambda
  local and return it (see `count_down` in the milestone 5 tests). Later,
  a match whose arms assign captures could join like an `if`.
- The boundary is not checked. `main.cpp` is outside the subset, so it
  could call `transfer(alice, alice, 5)`. The laws assume claws calling
  conventions, so code outside the subset must keep exclusivity itself.

## Lessons from milestone 6

- Obligations beside the code, not inside it. Making every function
  that might fail return `Option` (as Aeneas does with `Result`) would
  spread to most functions once vectors arrive, and every law would have
  to unwrap it. Instead f stays total (Lean's `x / 0 = 0`), laws about it
  stay as they were, and absence of undefined behavior is a separate
  generated claim. Code with nothing to check gets no `f.safe` and no
  obligation, so the earlier examples did not change at all.
- Safety is modular. A call obligates the caller to establish the
  callee's `pre`, and nothing about the callee's body, which is the
  callee's own obligation. A recursive function's self-call needs only
  its own `pre`, which is sound because Lean has proved it terminates.
- `&&`, `||` and `?:` check their later operands only where C++ evaluates
  them, so `count == 0 ? 0 : total / count` is safe with no
  precondition, and its obligation is `if count == 0 then true else
  count != 0`.
- Literal operands are checked at translation time: `x / 0` and `x << 32`
  are rejected, and `x << 16` produces no obligation.
- The four bugs tried all failed the gate: `rotl` without
  `expects(k != 0)` (counterexample `k = 0`), `mean` without its zero
  check (`count = 0`), a new caller passing a possibly zero divisor (its
  obligation is OPEN and unprovable), and `spin` rotating by its counter
  (fails at `i = 0`).
- `expects` traps at run time. Inside claws code it is proven never to
  fail; the check protects calls from code outside the subset.
- Shape-independent proofs, a fourth time: the first `Safety.mean` proof
  used `split`, so removing the zero check broke it structurally.
  `bv_decide` on the safety function gives the counterexample instead.
  The rules for writing PROOF.lean are now in `CLAUDE.md`.

## Lessons from milestone 7

- A claws type beats `std::vector`. `std::vector::size()` is a 64-bit
  `size_t`, outside the subset's integer types, and `vector<bool>` hands
  out proxies instead of references. `claws::vec` has a `uint32_t` size,
  refuses `bool` with a `static_assert`, and traps on a bad index or a
  full push at run time, which protects calls from outside the subset.
- Mutation needed no new idea. An index is one more kind of path step
  beside a field, so `v[i] = x` becomes
  `Array.setIfInBounds v i.toNat x` the way `s.f = x` becomes
  `{ s with f := x }`, and joins, loops and `T&` arguments all work with
  it unchanged.
- Exclusivity with indexes is conservative. `swap(v[i], v[j])` is
  rejected, since i may equal j; `swap(v[0], v[1])` is allowed.
- `size()` must fit 32 bits, so `push` carries an obligation that the
  size stays below 2^32 - 1, and every obligation about a vec parameter
  assumes `v.size < 2^32`, which no claws::vec can break.
- Safety can depend on real facts. `histogram` writes
  `counts[bucket(x, width, n)]`, which is in bounds only because
  `bucket` clamps to n - 1. Its safety proof uses the lemma
  `bucket_lt`, and removing the clamp fails that lemma with a
  counterexample `q >= n`.
- Rule 1 needed a corollary. With the clamp removed, `bucket` had no
  branch left, and a normalizing `simp only` made no progress, which is
  an error, so the proof broke on structure again. Every normalizing step
  in a uniform proof is now wrapped in `try`.
- A loop that pushes onto the vec it is bounded by would never end in
  C++. The translator rejects it: the bound may change inside the loop.

## Lessons from milestone 8

- The translator draws each input once and renders it twice, as a C++
  literal and a Lean literal, so the two sides cannot disagree about
  inputs. Outputs use one printed format: the result, then after `|` the
  final value of each `T&` argument.
- Inputs favor edge values (0, 1, 31, 32, 2^16, 2^31 - 1, 2^31,
  2^32 - 1), where wrapping and shift bugs live. Parameters that reach a
  loop bound or a vec's size, directly or through locals, assignments and
  calls, get values up to 10, so `replicate(x, 2^32 - 1)` never runs.
- Preconditions are respected on both sides: the C++ harness copies each
  `claws::expects` condition from the source, Lean uses `f.pre`, and
  failing inputs print `skip` on both.
- A tester that never fails proves nothing, so it was checked against
  four deliberately broken translators: `>` turned round, the branches of
  a joining `if` swapped, `-=` as `+`, and vec writes one index off. Each
  was caught on the first run with a concrete differing line.
- A sweep of 20 seeds with 500 inputs per function across all seven
  examples ran 288,159 cases with no disagreement.
- The gate's differential step is what protects proofs from a bad
  translation. A proof says the translation meets the law; the diff says
  the translation behaves like the C++. Neither alone says the C++ meets
  the law.

## Lessons from milestone 9

- The rules ported as ordinary C++: `step(Game&, Move)` switches on the
  move and updates the board through `T&`, `move_to` returns early on a
  wall, and `replay` loops over a `const vec<Move>&`. No construct needed
  a workaround; the port exercised milestones 3 to 7 together.
- Bend states its flag law on the game's drawn text, so the proof covers
  what the page shows. claws has no strings, so `cell(x, y)` returns a
  `Cell` enum, the driver draws only through it, and the law says the
  player's cell is never `Cell.Flag`. The driver's mapping from `Cell`
  to characters is outside the subset and not proven.
- The port found a translator bug no earlier example could: safety
  obligations named the project's own types (`Game`, `Move`) without
  opening the code namespace. Every earlier obligation used only
  `BitVec` and `Array (BitVec 32)`.
- Bend proves the geometric heart by enumerating the map. Here
  `bv_decide` proves that every move from a safe cell lands on a safe
  cell for every pair of 32-bit coordinates, which also covers cells off
  the map.
- Sizes, not like for like, counting lines of code without comments or
  blank lines: Bend's game is 166 lines and its proof 391; the port is
  136 lines and its proof of the laws 61, apart from the one line per
  function that validates its translation (stage D). Bend's figure
  includes proving the text drawing, which the port moved to the driver,
  and the port's `bv_decide` steps trust Lean's compiler, where Bend's
  proof is kernel checked throughout.
- Three tactic lessons, now rules in CLAUDE.md: `simp only` that unfolds
  a constant inside an `if` condition can leave the term ill typed (use
  full `simp`); `simp_all` before `bv_decide` can rewrite hypotheses into
  forms `bv_decide` cannot use, which shows up as a counterexample at a
  point the hypotheses exclude; and `bv_decide` treats a field of a
  structure literal as an unknown until `dsimp only` reduces it.

## An agent trial

A fresh agent, given only this repository, was asked to add diagonal
moves (q, e, z, c) to `examples/Game`. Nobody told it about any trap.

- Its first version, four new cases calling `move_to`, compiled and ran.
  The gate refused it: `step_safe` failed with the counterexample
  (11, 7).
- It did not assume the law was false, since an invariant step can fail
  on values no game reaches. It reproduced the values in the driver
  instead. On the torus, a down-right step from (11, 7) lands at (0, 0),
  inside the sealed room, and `dddsscc` wins.
- It stopped without committing or touching `LAWS.lean`, checked every
  diagonal neighbor of the room to show (11, 7) was the only leak, and
  offered three ways forward: wall off (11, 7), forbid diagonal steps
  that squeeze between two walls, or have the owner change the law.
- The owner chose no corner cutting. `move_diag` blocks a diagonal step
  when both cells beside it are walls, and the proof needed only
  `move_diag` added to its unfold list, because `step_safe` was written
  shape independent. About two minutes of agent work end to end.
- The trial is the claim of this project in miniature: a plausible
  feature that compiled and played normally was a real bug, and the laws caught it
  before it shipped. The two habits the agent showed (check a
  counterexample against the program; meet a conflicting request with
  law-preserving options) are now rules in CLAUDE.md.

## Lessons from the utf8 port

Go's `unicode/utf8` was the first program chosen because people rely on
it, not because it suited claws. It is a table-driven decoder with a
hand-optimized validator, the kind of code where overlong encodings and
surrogates have caused real security bugs.

- What the port needed, in the order claws-lean rejected it: constant
  globals and lookup tables, `uint8_t`, branches where one path returns
  and another falls through (Go's `if .. else if ..` chains), `while`
  loops with `break`, `continue` and early `return`, and
  `if (T x = e; c)`. Each became a translator feature; nothing needed
  a workaround in the C++. The one change to Go's logic is its
  signed-shift mask trick, `rune(x) << 31 >> 31`, which has an unsigned
  equivalent, since claws has no signed integers.
- C++ promotes a byte to `int` in any arithmetic. Rather than ban that,
  the subset admits an `int` only under operations that keep it between
  0 and 2^31 - 1 (`&`, `|`, `^`, `>>` by a literal, comparisons), where
  it equals the BitVec 32 of the same value. Byte code then reads like
  Go's.
- A `while` loop's Lean function recurses only when its
  `claws::decreases` measure has shrunk, so Lean accepts it without a
  termination proof, and the safety obligation proves the measure always
  shrinks. Termination joined division by zero and indexing as one more
  thing the obligation checks.
- The safety obligation found a bug the port introduced. Go's
  `i+size > n` cannot overflow a 64-bit `int`; the port's `uint32_t`
  can, when p holds nearly 2^32 bytes, letting a truncated rune through
  and reading past the end. The counterexample was exact: p.size =
  2^32 - 1, i = 2^32 - 2, p[i] = 0xF4. No test would reach a 4 GiB
  input.
- Planning a proof found a false law. `full_rune_stable`, as first
  written, claimed full_rune holds exactly when no bytes added to p could
  change the decoding. A vec within 3 bytes of 2^32 cannot grow, so every
  decoding is trivially stable, yet full_rune is false for a truncated
  rune there. The law now assumes room for the longest completion.
- The port matches Go itself: on 200,000 random byte strings, `valid`
  and `decode_rune` and `full_rune` at every offset agree with Go's
  `unicode/utf8`, and so do `rune_len`, `valid_rune` and `append_rune`
  at the edge values.
- The laws catch the classic decoder bugs. Planting each in Go's tables,
  and updating the proof's description of the tables to match (as an AI
  repairing the proof would), `decode_sound` fails with a counterexample
  every time: C0 and C1 as lead bytes (`C1 BD` decodes to an overlong
  `}`), surrogates (`ED A2 AB` decodes to U+D8AB), values past U+10FFFF
  (`F4 AF BF 9D`), and overlong 3-byte encodings (`E0 82 8B`).
- Most proofs are one recipe with no case splitting: unfold the code,
  rewrite each table read into a description of the byte's range
  (checked against every entry by `decide`), turn each comparison with
  `p.size` into a BitVec comparison, and let `bv_decide` check every
  path at once. The obligations of `decode_rune` and `full_rune` are
  four lines each. The hard law, `valid_well_formed`, rests on one step
  lemma derived from the decode laws and two loop invariants.
- Sizes: code.hpp is 301 lines, LAWS.lean 96, PROOF.lean about 500, and
  the gate checks everything in about 30 seconds. Roughly 200 of the
  proof's lines are reusable bridges (prefixes as reads, reads of
  `p ++ more`) that a proof library would provide.

## Lessons from stage A

- The trusted base for Clamp's translation is now Clang, `Sem.lean`
  (330 lines) and claws-ast (530 lines), in place of claws-lean (3,600).
  The interpreter's soundness (370 lines) and the semantics'
  determinism (100) are proven once, and need no review.
- All six Clamp functions validate, kernel checked with no trust in
  Lean's compiler, in about a second, by one tactic call each.
- Validation is semantic, not a comparison of text. With `>`
  translated as `>=`, clamp still validates, because it returns the
  same value either way (at `x = hi` both return `hi`), and the proof
  says exactly that. With `>` translated as `<`, `Valid.clamp` fails
  with the counterexample `clamp(0, 0, 2^31)`.
- Split on the translation's conditions before running the
  interpreter. Run first, a branch the interpreter cannot yet decide is
  copied into the store, every later statement copies the store, and
  `widen` (two calls, then a struct) exhausted Lean's recursion limit.
  Split first, each branch is decided the moment it is reached.
- The printer emits each function as its own definition, with a
  `found` lemma (by `rfl`) for looking it up. Unfolding the whole
  program instead put a copy of it into every step of the run.
- `simp only` runs no simprocs unless they are named, so string
  comparisons (`String.reduceBEq`) and literal arithmetic
  (`Nat.reduceAdd`) must be listed; without them the tactic split on
  whether two variable names are equal.
- A hypothesis `a > b` did not rewrite the same `a > b` in the goal, so
  the semantics states `a > b` as `b < a`, which says the same and
  normalizes the same way the translation's `BitVec.ult b a` does.

## Lessons from stage B

- 30 functions in six examples now validate: all of Clamp, Bits but
  `spin` (a loop), Stats but `summarize` (a list), Sorting's
  `in_order` (a `switch`), and 16 of Game's 22 (the rest take `T&`).
- Validation is modular. `claws_valid f [Code.f]` proves, for every fuel
  above a base, that the interpreter returns what `Code.f` computes, and
  registers that lemma, so a caller uses it at each call instead of
  running the callee again. Each function is validated after its
  callees. Without this, Game's `cell`, which calls `wall`, did not
  finish at ten times the default time limit; with it, all of Game
  validates in seconds.
- The callee lemma holds for every fuel `n` with `base ≤ n`, not for
  `k + base`. `simp` indexes a lemma by the literals in its left side,
  so `k + 1000` never matched a call at fuel `k + 2996`.
- A function's precondition is the `claws::expects` statements its body
  starts with, read by the semantics (`Sem.Pre`), not the translator's
  `f.pre`: a translator that made `pre` false would make every law
  vacuous. At a call, the tactic establishes the callee's precondition
  by running its conditions.
- The interpreter has one equation per kind of AST node. With one
  equation for all nodes, `simp` unfolded it on a statement not yet
  known (the code after a `switch` whose label was not yet decided) and
  ran through all its fuel.
- `&&`, `||` and `?:` compute a value when both sides evaluate, instead
  of branching. Branching nested the rest of `wall`'s body inside every
  case of each of its four Boolean locals, and the proof timed out.
- The semantics states unsigned arithmetic with `BitVec 32`'s
  operations, which compute arithmetic modulo 2^32. Stated on numbers,
  every result needed a lemma back to bit vectors, and literal
  arithmetic kept rewriting the result before the lemma could match.
- Exceeding Lean's recursion or time limit is not an error `try`
  catches, so an unbounded unfolding stops the whole proof rather than
  one step of it.
- A translator that turns `+=` into `|=` fails `Valid.ceil_div` with the
  counterexample `ceil_div(2^32 - 1, 2^32 - 2)`: C++ returns 2, the
  translation 1.
- Not yet: the `int` that a promoted `uint8_t` becomes (Utf8's
  `rune_start` needs lemmas from the semantics' integers to the
  translation's bit vectors), `T&` (stage C) and loops (stage D).

## Lessons from stage C

- The semantics has memory now: objects by address, names that point
  at them, `T&` parameters that point at the caller's objects. Calls
  and blocks cut memory back when they end, so a callee changes only
  what its references name. Soundness and determinism were redone for
  seven relations instead of four.
- A law quantifies over all memory: for any objects `m` and distinct
  addresses holding the `T&` arguments, the call returns `Code.f`'s
  value and leaves `m` with each argument replaced by what `Code.f`
  returns for it. 38 functions validate, including Bank's `transfer`
  and Game's `step`, a `switch` whose eight cases pass `g` by reference
  to `move_to` and `move_diag`, each used through its own lemma.
- The plan called for one theorem, proven once, that copy-in and
  copy-out agree with references when arguments do not overlap. Each
  function's law says exactly that for that function, checked per
  translation, so the general theorem became unnecessary.
- The law needs distinct arguments, and Bank's proof shows why: in
  C++, `transfer(a, a, 5)` on an account holding 10 ends at 10, while
  the translation's model ends one copy at 5 and the other at 15.
  claws-lean rejects two `T&` arguments that may overlap; that rule is
  now justified by a computation, not assumed.
- A lemma about a function must name every value in the call it
  rewrites, and the object behind a `T&` is not in the call. So each
  lemma reads its struct and enum arguments back through a decoder
  (`S.ofVal`) that claws-ast writes, and the law the verdict checks,
  stated with plain values, is derived from it.
- A discharger that leaves a goal open inside `simp` does not fail; Lean
  logs the goal and admits it. A discharger that ran the interpreter
  with itself as discharger produced wrong rewrites that way. The
  build still fails on the logged error, so nothing unsound passed, but
  the discharger is now non-recursive.
- `0#32` and `(0 : BitVec 32)` are different terms to `simp`, so a fact
  `a ≠ 0#32` did not settle a branch on `a = 0`; everything after it
  nested inside both cases and the proof timed out. Literals are
  normalized to `BitVec.ofNat` everywhere.
- A translator that returns the changed objects in reverse order, so
  `transfer` hands back `to` and `from` swapped, fails `Valid.transfer`
  with a counterexample.

## Lessons from stage D

- The semantics covers `for` and `while` loops with `break`,
  `continue` and `return`, `claws::vec`, `constexpr` constants and
  tables, array subscripts, `if` with an initializer, and
  `claws::list` with recursion. Every function of all nine examples
  validates.
- A loop is proven once, by induction over its translation, as a lemma
  `Proof.Loop.f.loopN`: for any memory holding the loop's variables, the
  loop ends with them as `Code.f.loopN` leaves them. The function's
  proof uses the lemma where the loop stands, as it uses a callee's.
- Where the C++ would trap, at an index out of bounds or a `push` at
  2^32 - 1 elements, the semantics has no rule, so a run needs the
  safety obligation: `claws_valid` takes `Proof.Safety.f`, and each loop
  lemma takes `f.loopN.safe`, unfolded one step per pass. Their
  conditions become hypotheses, guarded by the branch that tests them.
- A `return` now ends the objects of each block it leaves, as
  [stmt.jump]/2 says. Before, a loop that returned left memory whose
  length depended on how deeply the `return` was nested, and no lemma
  could state it.
- Stage B made `&&` and `||` compute a value instead of branching. In
  Utf8, `n > 1 && p[at + 1] < lo` reads `p[at + 1]` only when `n > 1`,
  so its right side does not evaluate unless the left holds, and the
  value-computing form left a `match` that never reduced. The
  interpreter branches again, and a lemma folds the branch back into
  `x && y` whenever both sides evaluate, which keeps stage B's case.
- `claws_case` splits a compound condition on its first unsettled
  atom, in the order C++ evaluates it, and constant lemmas settle the
  rest. Splitting on whole conditions left the interpreter's branches
  unsettled; splitting atoms without the constant lemmas left
  `false && b` to split again and made 259 cases of `full_rune`'s 12.
- A run that sticks on a condition makes simp evaluate everything after
  it with unknown names and memory, which is where every timeout came
  from. Three causes: an `int` index from a byte (fixed by stating the
  `int` as the `toInt` of a bit vector), a catch-all `match` equation
  whose side condition went to the full discharger (now tried by
  `contradiction` alone), and definitions by cases that simp unfolded
  into raw `match`es on unknown values (now registered by their
  equations only).
- The semantics computes `int` on the integers and the translation on
  `BitVec 32`. Lemmas restate each `int` that comes from a byte as the
  `toInt` of a bit vector, so comparisons, shifts, indices and the
  conversion back to `uint8_t` end up where `bv_decide` reads them. A
  byte promoted to `int` compares signed as the translation compares it
  unsigned, and a lemma says so, which halves the cases.
- Constant tables are checked against the translation by `rfl`, one
  lemma per table: the semantics holds Clang's computed values, and the
  lemma says they are the encoding of the `Code.lean` constant.
- `claws_run` evaluates only the path the interpreter takes. A `match`
  of the interpreter simplifies what it tests, and an `if` whose
  branches run more of the program its condition, and neither looks
  into a branch until that settles which one runs. Plain simp also
  simplified every branch not yet taken, with nothing known about the
  names and memory there: on the 17 paths of Utf8 `valid`'s second loop
  that never finished (67 minutes and 50 GB before it was stopped).
  Evaluated lazily it takes 5 minutes, the first loop drops from 46 s to
  13 s, and nothing in the trusted base changed.
- Before the run, a proof splits on the translation's conditions, but
  not on what a translated loop returns: that split cut the link between
  the translation and the loop's lemma, which the run meets later.
- A run reads a call's result from the semantics (`semCall`, the
  result `Call` derives, chosen classically) instead of running the
  callee with its own fuel. Fuel bounded the depth of the whole run, so
  a recursive function needed fuel growing with its list, and a caller
  of one, such as `sort` calling `insert` on `sort`'s own result,
  needed to bound the length of what that returns. Read from the
  semantics, a call costs no fuel: each function's fuel covers its own
  body, a callee's lemma `Proof.Call.f` says what the call reads, and
  determinism (`Claws.Det`) says it is the only result.
- A recursive function is proven by induction over its translation, as
  a loop is: the hypothesis says what the recursive call reads, for any
  objects, since the call comes with the body's locals on top. All four
  of Sorting's functions validate in under three seconds.
- `xs.match(on_nil, on_cons)` takes two lambdas; claws-ast lists each
  as a function of the program, named by its position, whose body runs
  in the scope it is written in. That kept `Expr` and `Stmt` apart:
  a lambda in an expression would have made them one mutual type.
- A list is stated by its elements everywhere, `.list (l.map f)`. With
  an opaque encoding `ofList f l` in some places, the `match` that
  takes a list apart could not see the constructor; with a fold back to
  `ofList`, `cons` could not. The induction hypothesis is put in the
  same form before the run, since simp rewrites with a hypothesis as it
  is stated.
- A translator that turns `cons(h, t)` into `t ++ [h]` fails
  `Valid.insert` on each of its four paths. The report names the path
  (the order, and whether `in_order` held), not a list: what is left is
  an equation between lists, which `bv_decide` reads as unknowns.

## Prior art

- cpp2v and BRiCk (BedRock Systems, now Bluerock): a Clang plugin that
  dumps C++ ASTs into Coq, with a formal C++ semantics. The closest existing
  project to claws.
- Aeneas: Rust to Lean as pure functions, using ownership as Bend uses
  affinity. The model for the functional translation.
- Verus and hax: other Rust verification approaches.
- Frama-C with ACSL: specification and proof for C.

## Data point

Bend's `app_win_is_bug_2d` demo, counted without comments or blank
lines, has 166 lines of game code and 391 lines of tactic-free proof
(240 and 484 with them). The claws port of the same game, with four
diagonal moves added, has 136 lines of code and 61 lines of proof of
its laws, plus 23 one-line commands that validate its translation.
Tactics and `bv_decide` do the work that Bend's proof spells out, with
the trade-off in "Lessons from milestone 9": the `bv_decide` steps trust
Lean's compiler.
