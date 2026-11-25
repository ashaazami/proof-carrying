import Mathlib
import Programs.ListMax.ListMax
import Init.Data.List.Basic
import Mathlib.Data.List.Pairwise

/-! # Sorting, verified -/

def inversion_count {α : Type} [LinearOrder α] (l : List α) : ℕ :=
  match l with
  | [] => 0
  | x :: xs =>
    let count := xs.countP (fun y => x > y)
    count + inversion_count xs

def sort {α : Type} [LinearOrder α] (l : List α) : List α :=
  match l with
  | [] => []
  | x :: xs =>
    let xs_1 := xs.filter (fun y => y ≤ x)
    let xs_2 := xs.filter (fun y => y > x)
    sort (xs_1) ++ [x] ++ sort (xs_2)
  termination_by l.length
  decreasing_by
    all_goals
      simp only [List.length_unattach, List.length_cons]
      grind [List.length_filter_le]


#eval sort [3, 12, 6, 5, 3, 5]

/-!
lemma sort_inversion_count_is_zero {α : Type} [LinearOrder α] (l : List α) :
  inversion_count (sort l) = 0 := by
  induction l with
  | nil => simp [inversion_count, sort]
  | cons x xs ih =>
    simp only [inversion_count, sort]
    let xs_1 := xs.filter (fun y => y ≤ x)
    let xs_2 := xs.filter (fun y => y > x)
    s1: inversion_count (sort xs_1) = 0 := by
      apply ih
    s2: inversion_count (sort xs_2) = 0 := by
        apply ih
-/

theorem sort_perm {α : Type} [LinearOrder α] (l : List α) :
  (sort l).Perm l := by
  induction l with
  | nil => simp [sort]
  | cons x xs ih =>
    let xs_1 := xs.filter (fun y => y ≤ x)
    let xs_2 := xs.filter (fun y => y > x)
    have s1: (sort xs_1).Perm xs_1 :=by
      if h: xs_1 = [] then
        simp [h, sort]
      else
        -- xs_1 = cons z :: zs
        -- simp [ih]
        sorry
    have s2: (sort xs_2).Perm xs_2 := by
      -- `apply ih` fails: `ih` is about `xs`, not `xs_2`. Plain `induction` only gives
      -- the hypothesis for the tail; recursing on a filtered list needs strong induction.
      sorry
    all_goals sorry

theorem sort_correct {α : Type} [LinearOrder α] (l : List α) :
  (sort l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [sort]
  | cons x xs ih =>
    simp only [sort]
    let xs_1 := xs.filter (fun y => y ≤ x)
    let xs_2 := xs.filter (fun y => y > x)
    have s1: (sort xs_1).Pairwise (· ≤ ·)
    refine List.sortedLE_iff_pairwise.mp ?_
    have s2: (sort xs_2).Pairwise (· ≤ ·)
    refine List.sortedLE_iff_pairwise.mp ?_
    have s1x: ∀ y ∈ sort xs_1, y ≤ x := by
      sorry
    all_goals sorry

    -- have s2: (sort xs_2).Pairwise (· ≤ ·) := by
    --   apply ih
    -- have s1x: ∀ y ∈ sort xs_1, y ≤ x := by
    --   apply xs_1

    --   have h: y ∈ xs_1 := by
    --     apply List.mem_of_mem_filter hy
    --   have h2: y ≤ x := by
    --     apply List.mem_filter.mp h
    --   exact h2
