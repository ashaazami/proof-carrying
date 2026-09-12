import Mathlib

/-! # Maximum of a non-empty list, verified -/

/-- Finds the max of a non-empty list. Taking a head `x` and a tail `xs`
separately is what guarantees non-emptiness: there is no empty case to handle. -/
def listMax (x : ℕ) (xs : List ℕ) : ℕ :=
  match xs with
  | [] => x
  | y :: ys => listMax (if x ≥ y then x else y) ys

/-- The accumulator is a lower bound on the result.

This is the missing piece: `listMax` only ever replaces the accumulator with
something larger, so whatever it returns is at least what it started with. -/
theorem le_listMax (x : ℕ) (xs : List ℕ) : listMax x xs ≥ x := by
  induction xs generalizing x with
  | nil => simp [listMax]
  | cons y ys ih =>
    simp only [listMax]
    split_ifs with hxy
    · have := ih x; omega
    · have := ih y; omega

/-- **Correctness**: the result dominates every element of the list. -/
theorem listMax_is_max (x : ℕ) (xs : List ℕ) (a : ℕ) :
    a ∈ x :: xs → listMax x xs ≥ a := by
  induction xs generalizing x with
  | nil =>
    intro h
    simp only [List.mem_singleton] at h
    subst h
    simp [listMax]
  | cons y ys ih =>
    intro h
    simp only [listMax]
    split_ifs with hxy
    · -- `x ≥ y`, so `x` carries forward as the accumulator
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_listMax _ _
      · rcases List.mem_cons.mp h' with rfl | h''
        · have := le_listMax x ys; omega
        · exact ih x (List.mem_cons_of_mem _ h'')
    · -- `x < y`, so `y` takes over
      rcases List.mem_cons.mp h with rfl | h'
      · have := le_listMax y ys; omega
      · rcases List.mem_cons.mp h' with rfl | h''
        · exact le_listMax _ _
        · exact ih y (List.mem_cons_of_mem _ h'')

/-- **The result is one of the elements it was given.**

This is the other half of the specification, and it is not optional. `listMax_is_max`
alone says only that the answer is an *upper bound* — a function returning the sum of
the list would satisfy it too, since a sum of naturals dominates each of them.

With both theorems the answer is pinned down: an upper bound that is also a member of
the list is the maximum, and nothing else is. -/
theorem listMax_mem (x : ℕ) (xs : List ℕ) : listMax x xs ∈ x :: xs := by
  induction xs generalizing x with
  | nil => simp [listMax]
  | cons y ys ih =>
    simp only [listMax]
    split_ifs with hxy
    · rcases List.mem_cons.mp (ih x) with h | h
      · simp [h]
      · simp [h]
    · rcases List.mem_cons.mp (ih y) with h | h
      · simp [h]
      · simp [h]
