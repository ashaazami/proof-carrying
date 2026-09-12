---
name: lean-workbench
description: Conventions for this Lean 4 toy repo - math proofs in MathTheorems/, verified programs in Programs/, the build rules, and how to explain Lean to someone who does not know it. Use whenever editing .lean files or answering questions about this project.
---

# Working in this repository

A toy repo for math proofs and for programs that ship with a correctness proof. Part of
the audience does not know Lean, so explanations matter as much as proofs.

## Layout

- `MathTheorems/Topic.lean` — proofs. Add one import line to `MathTheorems.lean`.
- `Programs/<Name>/` — a program plus its proofs, with its own `Main.lean` and a
  `[[lean_exe]]` entry in `lakefile.toml`. Add the module to `Programs.lean`.

Module names are absolute from the repo root. There are no relative imports.

## Build rules

- `lake exe cache get` after any dependency change, or Mathlib recompiles for hours.
- After pulling, or when the build misbehaves, `scripts/setup.sh --check` reports what is
  out of sync without changing anything. Without `--check` it offers to fix each gap.
- `lake build` **succeeds** on a `sorry`, warning only. Never read a green build as proof;
  CI has a separate step that fails on it.
- `lake build` applies the linters from `lakefile.toml`; `lake env lean <file>` is faster
  for one file but does not. Use `lake build` before calling a file clean.

## Integrity

A green file is not a proved theorem.

- Never leave a `sorry` — it admits anything and only warns.
- `#print axioms foo` is the honest check. Expect `propext`, `Classical.choice`,
  `Quot.sound`. If `sorryAx` appears, it is not proved.
- `#check` reports a type, so it succeeds on false statements. It says nothing about
  whether a proof holds.
- A proof is only as good as its statement. Check the theorem says what was meant.

## Working style

- Read the goal before writing tactics.
- `exact?` searches Mathlib before guessing; `apply?` when it finds nothing. Remove them
  once answered — they are slow.
- Reshape the goal rather than fight the proof: `have h : … := by ring` then `rw [h]`.
  Lean matches syntactically, so equal-but-different terms do not unify.
- Teach rather than just solve: give the next step and point at the tool. If a file is
  set up as an exercise — a stated theorem with `sorry` and hints — do not fill it in
  unless asked.

## Explaining to a newcomer

- Blue squiggles are output (`#check`, `#eval`), not errors. Red is an error, yellow a
  warning; `sorry` is yellow.
- Parse errors make every later message meaningless. Fix syntax first.
- `⟨⟩` are not `<>`, and `∣` is not the pipe key. Backslash abbreviations, then Tab.
- A theorem is a function: `(m : ℤ)` before the colon is exactly `∀ m : ℤ`.
