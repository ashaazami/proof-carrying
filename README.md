# proof-carrying

![A theorem statement feeds a model, which drafts a proof; the Lean kernel accepts or
refuses it, and an accepted proof compiles to an ordinary program.](docs/banner.jpg)

Code that ships with a machine-checked proof of its own correctness — and the math
proofs that support it.

## Why this exists

An LLM can write plausible code. Plausible is not correct, and reading it carefully is
the only check most workflows have. That check scales badly and it depends on trusting
the reviewer.

Formal proof is different. Lean's kernel verifies a proof against the axioms without
caring who or what produced it — a person, a model, a search procedure. The proof either
typechecks or it does not. This makes verified code an unusually good fit for AI
assistance: **generation and verification are separate, and only one of them has to be
trusted.**

That is the direction this repository is a small argument for. Generate aggressively,
verify mechanically, and let the compiler settle what is true. Everything below is a
concrete instance of it, small enough to read in one sitting.

![A theorem statement goes to an LLM, which drafts a proof in Lean. The Lean kernel
either accepts it or refuses and returns the failing goal, which the model answers.
An accepted proof compiles to C with the proof erased.](docs/pipeline.svg)

## The example: `Programs/ListMax/`

`listMax` finds the largest number in a list. It walks the list carrying a best-so-far
value, replacing it whenever it meets something bigger:

```lean
def listMax (x : ℕ) (xs : List ℕ) : ℕ :=
  match xs with
  | [] => x
  | y :: ys => listMax (if x ≥ y then x else y) ys
```

Taking the head `x` and the tail `xs` as separate arguments is doing real work: there is
no empty-list case to handle, because the type makes an empty input impossible. No
`Option`, no error path, no "what should this return for `[]`" question.

Alongside it sit two theorems — statements **about this code**, not about mathematics in
general:

```lean
theorem le_listMax     (x : ℕ) (xs : List ℕ) : listMax x xs ≥ x
theorem listMax_is_max (x : ℕ) (xs : List ℕ) (a : ℕ) : a ∈ x :: xs → listMax x xs ≥ a
```

The second is the specification: **whatever `listMax` returns is at least every element
of the list it was given.** The first is the lemma it needs — that the running best never
decreases.

## Why prove a property of code

A theorem about a program differs from a theorem about numbers in one way that matters:
it is checked against the **actual implementation**, not a description of it.

That has consequences a test suite cannot offer.

**It quantifies over every input.** `listMax_is_max` holds for all lists of all lengths
containing any naturals. Not a thousand sampled cases — all of them, including the ones
nobody thought to try.

**It cannot drift from the code.** Change `listMax` and the proof stops compiling until
you fix it. The specification is not a comment or a wiki page that goes stale; it is
enforced by the build. There is no way to ship a version where the docs and the behaviour
disagree.

**It survives refactoring.** Rewrite the loop, change the accumulator, make it faster —
if the proof still compiles, the property still holds. That is a much stronger safety net
than a test suite, which only tells you the cases you wrote still pass.

**And it costs nothing at runtime.** The compiled program is an ordinary tail-recursive
loop with no trace of the proof in it — see `## The point` below.

This is what "proof-carrying" means: the code and the argument for its correctness travel
together, and the compiler refuses to separate them.

## The point

A test checks the inputs you thought of. A proof covers the ones you didn't.

`listMax_is_max` says the result dominates **every** element of **any** list — not a
thousand random cases, every case. Once it typechecks that class of bug is gone and
cannot return: change the algorithm and the proof stops compiling until you fix it.
The specification is enforced by the build, not by discipline.

And it costs nothing at runtime. `listMax` compiles to an ordinary tail-recursive loop,
and none of its three theorems appear anywhere in the generated C.

**[`docs/proof-to-code.md`](docs/proof-to-code.md)** shows it end to end — the Lean
source, the C it becomes, and the measurements: `listMax` appears 9 times in the output,
each theorem exactly 0.

Correctness is paid for once, at build time. What ships is the code you would have
written anyway.

## The catch, and closing it

A proof is only as strong as the statement you wrote — and this repository's own example
got that wrong at first.

`listMax_is_max` says the answer is an *upper bound* on the list. It does not say the
answer is one of the elements. So this passes it:

```lean
def sumAll (x : ℕ) (xs : List ℕ) : ℕ := (x :: xs).sum
```

A sum of naturals dominates every element, so it satisfies the specification exactly as
well as the real implementation does — while `sumAll 3 [1, 7]` returns **11**, which is
not even in the list.

The fix is a second theorem:

```lean
theorem listMax_mem (x : ℕ) (xs : List ℕ) : listMax x xs ∈ x :: xs
```

An upper bound that is *also a member* is the maximum, and nothing else is. `sumAll`
fails this one immediately.

The general point survives the fix: **the kernel guarantees the proof; nothing guarantees
you asked for the right thing.** Writing the proof is mechanical once you know what to
prove. Deciding what to prove is judgment, it is where the real work is, and no machine
checks it for you.

The practical defence is the one used above — write a deliberately wrong implementation
and see whether your specification rejects it. If it does not, the specification is
incomplete.

## Setup

```sh
git clone https://github.com/ashaazami/proof-carrying.git
cd proof-carrying
```

Install [elan](https://github.com/leanprover/elan), Lean's version manager — it reads
`lean-toolchain` and fetches the exact Lean this project pins:

```sh
brew install elan-init                                    # macOS
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh    # Linux
```

Then:

```sh
scripts/setup.sh       # checks what is missing, asks before installing anything
```

Or do it by hand:

```sh
lake exe cache get     # prebuilt Mathlib, ~8 GB — skipping this means hours of compiling
lake build             # check every proof
```

`setup.sh` is safe to re-run — after pulling, or whenever the build misbehaves.
`scripts/setup.sh --check` reports without changing anything.

For the editor, open *this folder* in VS Code (not a single file — the extension finds
the project by walking up to `lakefile.toml`). It will offer to install the **lean4**
extension; accept. `Cmd+Shift+Enter` opens the InfoView, which shows the proof goal at
your cursor — Lean is hard to use without it.

Wait for `lake build` to finish before opening the folder. If the editor starts
configuring the workspace while Lake is still downloading packages, the two collide and
the server fails to start.

## What is here

| | |
|---|---|
| `MathTheorems/` | proofs. One file: `√2` is irrational, from Euclid's descent |
| `Programs/` | verified programs, one folder each. `ListMax/` finds a list maximum |
| `docs/` | `proof-to-code.md` — Lean in, C out; `running.md` — six ways to run it |
| `scripts/` | `setup.sh` — verify the machine; `build.sh`, `show-c.sh` — read the generated C |

## Running

```sh
lake exe listmax 3 1 7 2 9 4      # max = 9
```

Or put the cursor on an `#eval` line in `Programs/ListMax/Main.lean` and read the answer
in the InfoView. `docs/running.md` has the rest.

## Conventions

- Proofs go in `MathTheorems/`, programs in `Programs/<Name>/`, each added to the
  matching root file (`MathTheorems.lean`, `Programs.lean`).
- `lake build` must pass before committing. CI runs it on every push, and fails
  separately if any theorem is admitted with `sorry` — `lake build` alone only warns.
- Never leave a `sorry`. It admits anything unproved; `#print axioms yourTheorem` is the
  honest check — if `sorryAx` appears there, it is not proved.
- Mathlib's style linters are on deliberately.

## License

Apache-2.0 — see `LICENSE`. The same license Lean, Mathlib and cslib use, so this
composes with the ecosystem it depends on.
