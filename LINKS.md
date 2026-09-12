# References

## Cheat sheets — worth printing
Lean 4 cheat sheet — language constructs and syntax reference, one page.
  How to build and destructure each of ∧ ∨ → ↔ ∀ ∃, plus def/match/structure.
  https://mbty.fr/projects/lean_cheat_sheet.pdf

Lean 4 tactic cheatsheet — every tactic by category, three pages.
  Opens with a "logical symbol → what to do in the goal vs in a hypothesis" table.
  https://leanprover-community.github.io/papers/lean-tactics.pdf

## Learning
Mathematics in Lean — the textbook, with exercises
  https://leanprover-community.github.io/mathematics_in_lean/

Theorem Proving in Lean 4 — why the language works this way
  https://leanprover.github.io/theorem_proving_in_lean4/

Learning Lean 4 — community index, includes the Natural Number Game
  https://leanprover-community.github.io/learn.html

## Looking things up
Loogle — search Mathlib by shape, e.g. `Irrational, _ + _`
  https://loogle.lean-lang.org

Mathlib API docs
  https://leanprover-community.github.io/mathlib4_docs/

The Lean Language Reference
  https://lean-lang.org/doc/reference/latest/

## In the editor
  exact?          search all of Mathlib for a lemma closing the goal
  apply?          same, accepting partial matches
  Cmd+Click       jump to a definition's source
  Cmd+Shift+Enter InfoView

## Dependencies
Mathlib is the only one. Everything else in lake-manifest.json arrives through it.
  https://github.com/leanprover-community/mathlib4
