# claws

**Laws for C++.** Write claims about a C++ program, prove them in Lean,
and refuse the build until every claim holds. The proofs never reach the
binary: the same header compiles with stock clang, unchanged.

claws brings the Laws workflow of [Bend 2](https://github.com/bendlang/bend)
to a subset of C++. A human states the laws. An AI (or a human) writes
the code and the proofs. A gate checks everything and prints
`ALL PROOFS CHECK`, or refuses.

> **Status: research prototype.** Nine examples, including a port of Go's
> `unicode/utf8`, are fully proven. The subset is small, the tools have
> been tested on macOS only, and nothing here is stable. See
> [Limitations](#limitations).

## What it looks like

A project is a directory of seven files:

| File | Written by | What it is |
|---|---|---|
| `code.hpp` | AI | The program, in the claws subset of C++ |
| `main.cpp` | AI | A driver for I/O, outside the subset, never translated |
| `LAWS.lean` | **Human** | The claims. The AI may not edit or weaken them |
| `PROOF.lean` | AI | Proofs of the laws |
| `Verdict.lean` | Human | The gate: one line, `#claws_verdict <Project>` |
| `Code.lean` | generated | `code.hpp` translated to Lean by `claws-lean` |
| `Ast.lean` | generated | `code.hpp` as data for the semantics, by `claws-ast` |

The C++ is ordinary:

```cpp
// examples/Clamp/code.hpp
inline uint32_t clamp(uint32_t x, uint32_t lo, uint32_t hi) {
  if (x < lo) {
    return lo;
  }
  if (x > hi) {
    return hi;
  }
  return x;
}
```

A law is a Lean proposition about the translation:

```lean
-- examples/Clamp/LAWS.lean
-- LAW: when lo <= hi, clamp lands inside [lo, hi].
def clamp_in_range : Prop :=
  ∀ x lo hi : BitVec 32, lo ≤ hi → contains ⟨lo, hi⟩ (clamp x lo hi) = true
```

and its proof is usually short, because `bv_decide` (a SAT solver over
bit vectors) does the work, and reports a concrete counterexample when a
law is false:

```lean
-- examples/Clamp/PROOF.lean
theorem clamp_in_range : Laws.clamp_in_range := by
  intro x lo hi h
  simp only [clamp, contains]
  bv_decide

-- The translation of each function, checked against the C++ semantics.
claws_valid clamp [Code.clamp]
```

The gate translates, checks, tests and compiles:

```
$ scripts/gate.sh examples/Clamp
...
info: examples/Clamp/Verdict.lean:6:0: ALL PROOFS CHECK
OK      Valid.clamp
...
OK      clamp_in_range (trusts Lean's compiler)
OK      clamp_keeps
translation: validated against Claws.Sem (6 functions)
== differential test
C++ and Lean agree on 600 cases (0 skipped by preconditions, seed 1)
== compile with stock clang
range [10, 25], span 15
clamp(3) = 10, clamp(99) = 25
```

The gate exits nonzero if the C++ leaves the subset, if any law is open,
fails, uses `sorry`, or relies on an unexpected axiom, if any function's
translation is not validated (once `PROOF.lean` imports the project's
`Ast`, as every example does), or if the differential test finds a
difference.

## What `ALL PROOFS CHECK` means

When the gate passes, you know this: **for every input that meets each
function's `claws::expects` preconditions, the C++ program, as the
semantics in [`lean/Claws/Sem.lean`](lean/Claws/Sem.lean) defines C++,
satisfies every law in `LAWS.lean`, and never reaches undefined
behavior.**

That rests on three checks:

1. **The laws hold of the translation.** Lean's kernel checks
   `PROOF.lean` against `LAWS.lean`, about `Code.lean`.
2. **The translation is the C++.** For each function, a validation law
   (`Valid.f`) says: called with any arguments and any memory, whenever
   its preconditions hold, the C++ function, run by the semantics,
   returns exactly what `Code.f` computes and leaves its `T&` arguments as
   `Code.f` says. `claws_valid` proves it by running an interpreter
   symbolically over the function's AST. A translator bug fails this
   proof, so `claws-lean` is checked, not trusted.
3. **The translation behaves like the compiled code.** A differential
   test runs every function on the same generated inputs, as C++ built by
   clang and as Lean, and the gate fails on any difference.

### What you still trust

No verifier proves everything. Here is the trusted base, so you can
judge it:

| Part | Size | Why it is trusted |
|---|---|---|
| Lean's kernel | | Checks every proof. Shared with every Lean user and with Bend 2's own consistency proof |
| Lean's compiler | | Only for laws marked `trusts Lean's compiler`: `bv_decide` checks its SAT certificates with compiled code |
| Clang's front end | | Parses and type checks `code.hpp`, and resolves every implicit conversion |
| [`Sem.lean`](lean/Claws/Sem.lean) | ~800 lines | The meaning of the subset, one rule per kind of AST node, each citing the clause of the C++20 standard it follows. Not yet tested against a compiler |
| [`claws-ast`](tools/claws-ast/main.cpp) | ~1,200 lines | Prints Clang's AST for the semantics. Shares only Clang with `claws-lean`, so a wrong translation passes only if `claws-ast` misprints the same code to match |
| [`include/claws/*.hpp`](include/claws) | ~200 lines | `claws::vec` and `claws::list`, trusted to behave as their rules in `Sem.lean` say |
| `LAWS.lean` | yours | The laws say what you meant. Nothing can check that for you |

Not trusted: `claws-lean` (3,600 lines), the interpreter (proven sound
against the semantics), and every proof.

The boundary is also unchecked: `main.cpp` is outside the subset, and
could call into the code in ways the laws exclude, such as passing one
object as two `T&` arguments. The validation laws state that condition
(distinct arguments) explicitly.

## The subset

claws accepts a subset of C++20 in which each construct has one meaning,
and rejects everything else with a message saying why. It never
approximates.

- **Types:** `uint32_t`, `uint8_t`, `bool`, `int` where Clang promotes a
  byte to it, `enum class`, structs, `claws::vec<T>`, `claws::list<T>`,
  and `constexpr` constants and lookup tables.
- **Statements:** locals, assignment and compound assignment, `++`, `if`
  (with an initializer too), `switch`, `?:`, `&&`, `||`, `for` and
  `while` with `break`, `continue` and `return`, and recursion.
- **Functions:** value and `T&` / `const T&` parameters, no aliasing
  between `T&` arguments, and `claws::expects(c)` preconditions.
- **Undefined behavior is an obligation, not an assumption.** Division
  by zero, shifts of 32 or more, indexes out of bounds, a `vec` growing
  past 2^32 - 1, a `while` loop whose `claws::decreases` measure fails
  to shrink, and calls outside a callee's preconditions each become a
  safety theorem (`Safety.f`) the gate requires.
- **Out:** signed arithmetic beyond promoted bytes, pointers, heap
  allocation, classes with methods, templates, floats, exceptions.

## Examples

| Example | What it shows | Functions |
|---|---|---|
| [`Clamp`](examples/Clamp) | Comparisons, structs, `bv_decide` | 6 |
| [`Sorting`](examples/Sorting) | Insertion sort over `claws::list`, recursion | 4 |
| [`Stats`](examples/Stats) | Running statistics with local mutation | 4 |
| [`Loops`](examples/Loops) | Counting loops, nested loops, building a list | 3 |
| [`Bank`](examples/Bank) | Transfers through `T&` parameters | 2 |
| [`Bits`](examples/Bits) | Division, shifts and preconditions | 7 |
| [`Vectors`](examples/Vectors) | Reading, writing and growing `claws::vec` | 5 |
| [`Game`](examples/Game) | Bend 2's "winning is impossible" game, proven unwinnable | 22 |
| [`Utf8`](examples/Utf8) | Go's `unicode/utf8`, 301 lines, against the Unicode Standard | 7 |

Every function in every example is validated against the semantics.

Utf8 is the real test. Its laws compare the port with UTF-8 as the
Unicode Standard defines it, written independently with plain
arithmetic. Proving them found a 32-bit overflow introduced in the port
(safe in Go's 64-bit `int`), showed that one of the laws as first
written was false, and caught each of four classic decoder bugs planted
in its tables, each with a concrete byte sequence.

## Getting started

Requirements:

- [elan](https://github.com/leanprover/elan), which installs Lean 4.35.0
  from `lean-toolchain`
- LLVM with the Clang development libraries (developed with LLVM 23).
  On macOS, `brew install llvm`
- CMake 3.20 or later, Ninja, and a `clang++` on the `PATH` to compile
  the examples. On macOS, `brew install cmake ninja` and the Xcode
  command line tools

`gate.sh` looks for LLVM at `$LLVM_PREFIX`, then at Homebrew's
`/opt/homebrew/opt/llvm`, then wherever `llvm-config` says. On Linux,
set `LLVM_PREFIX` (for example `/usr/lib/llvm-23`) or put `llvm-config`
on the `PATH`; this has not been tested yet.

Then:

```sh
scripts/gate.sh examples/Clamp      # a few seconds, plus a first build
scripts/gate.sh examples/Utf8       # about seven minutes
scripts/diff.sh examples/Clamp 5000 7   # a larger differential test
```

The first run configures CMake, builds `claws-lean` and `claws-ast`, and
builds the Lean library, which takes a few minutes.

### A new project

1. Make `examples/<Project>/` with `code.hpp`, `main.cpp`, `LAWS.lean`,
   `PROOF.lean`, and a `Verdict.lean` that imports `Claws` and
   `<Project>.PROOF` and runs `#claws_verdict <Project>`. Copy
   `examples/Clamp` as a start.
2. Add a `[[lean_lib]]` entry for it in `lakefile.toml`.
3. Write laws as `def`s of type `Prop` in namespace `<Project>.Laws`.
   Prove each with a theorem of the same name in `<Project>.Proof`.
4. In `PROOF.lean`, import `<Project>.Ast` and validate each function
   with `claws_valid f [Code.f]`, callees first; prove each loop with
   `claws_loop f N []` before the function that contains it.
5. Run `scripts/gate.sh examples/<Project>` until it passes.

[`CLAUDE.md`](CLAUDE.md) holds the rules an AI agent follows in this
repository: who owns which file, and fifteen rules for writing proofs
that do not break when the code changes shape. They are useful for a
human too.

## How it works

```
                 +--> claws-lean --> Code.lean --+
code.hpp, Clang -+                               +--> Lean's kernel --> verdict
                 +--> claws-ast  --> Ast.lean  --+
                                        ^
                                        |
                                 Sem.lean (the semantics)
```

- **claws-lean** ([`tools/claws-lean`](tools/claws-lean)) is a Clang
  LibTooling tool. It rejects anything outside the subset, writes
  `Code.lean` as readable Lean (loops become recursive functions,
  `T&` parameters become returned values), generates a safety theorem
  per function, and emits the two harnesses for the differential test.
- **claws-ast** ([`tools/claws-ast`](tools/claws-ast)) prints the same AST
  as a Lean term, with every implicit conversion as a node, and states a
  validation law for each function.
- **The semantics** ([`lean/Claws/Sem.lean`](lean/Claws/Sem.lean)) is a
  big-step relation over that term: memory as a list of objects,
  references as addresses, undefined behavior as the absence of a rule.
  [`Det.lean`](lean/Claws/Det.lean) proves it deterministic, so a
  validation law says what the C++ does, not something it might do.
- **The interpreter** ([`lean/Claws/Interp.lean`](lean/Claws/Interp.lean))
  is proven sound against the semantics once.
  [`Validate.lean`](lean/Claws/Validate.lean) and
  [`Loop.lean`](lean/Claws/Loop.lean) run it symbolically to prove each
  validation law: loops and recursive functions by induction over their
  translation, each callee through its own lemma.
- **The verdict** ([`lean/Claws/Verdict.lean`](lean/Claws/Verdict.lean))
  lists every law with its status and every axiom it depends on.

[`DESIGN.md`](DESIGN.md) is the full design: the comparison with Bend 2,
each milestone, and the lessons behind every rule, including the bugs
the gate caught.

## Limitations

- **Tested on macOS only.** The build is meant to work on Linux too
  (see [Getting started](#getting-started)), but nobody has tried it.
- **The semantics is untested.** It is reviewed against the standard,
  rule by rule, but not yet run against a compiler. That is the next
  stage: run it as a third column of the differential test, with
  clang's constant evaluator as an oracle for undefined behavior.
- **One header per project,** and a small language: see
  [The subset](#the-subset).
- **Proofs are slow where code branches a lot.** Validating Utf8's
  `valid`, whose second loop has seventeen paths, takes about five
  minutes.
- **Laws are written in Lean.** C++ developers have to read and write
  Lean propositions.
- **Lean's compiler is trusted** wherever `bv_decide` is used. The
  verdict marks those laws; there is no kernel-only mode yet.

## Acknowledgements

claws follows the design of Bend 2's Laws feature. The Game example is a
port of Bend 2's "Winning Is Impossible" demo, Copyright 2026
HigherOrderCO, under the Apache License 2.0
([`examples/Game/NOTICE`](examples/Game/NOTICE) says what changed).
The Utf8 example is ported from Go's `unicode/utf8`, Copyright 2009 The
Go Authors, used under Go's BSD-style license
([`examples/Utf8/LICENSE`](examples/Utf8/LICENSE)). The trusted translation
draws on BRiCk, Cerberus, Aeneas, CompCert's Clight and CakeML.

## License

claws is licensed under the [Apache License 2.0](LICENSE). The Utf8
example is a port of Go's code and keeps Go's BSD-style license, in
[`examples/Utf8/LICENSE`](examples/Utf8/LICENSE). The Game example is
derived from Bend 2, also under Apache 2.0; see
[`examples/Game/NOTICE`](examples/Game/NOTICE).
