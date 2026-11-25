import MathTheorems.ShannonCapacity.Defs
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Two lower bounds on Shannon capacity

1. `indepNum_le_shannonCapacity` — `α(G) ≤ Θ(G)`: one use of the channel is already a code.
2. `sqrt_five_le_shannonCapacity_C5` — `√5 ≤ Θ(C₅)`, Shannon's 1956 observation.

The definitions — `SimpleGraph.strongPower` and `ShannonBounds.shannonCapacity` — are in
`Defs.lean`, copied from the `ShannonBounds` library of Buys, Polak and Zuiddam
(<https://github.com/spectra-research/shannon-capacity-lean>). That library proves lower
bounds for `C₇, C₁₁, …, C₂₃`; it does not cover `C₅`, and this file does.

## Why `√5`

`α(C₅) = 2`, so one use of the pentagon channel carries 2 messages. But **two** uses
carry 5, not just `2 · 2 = 4`: the words `(i, 2i mod 5)` for `i = 0, …, 4` are pairwise
distinguishable. Five messages in two uses is a rate of `5^(1/2) = √5 ≈ 2.236` per use.
Lovász proved in 1979 that nothing beats it; that upper bound is not proved here.

## Trust

Unlike the library's odd-cycle bounds, nothing here uses `native_decide`: the one finite
check (25 cases) runs through `decide`, inside the kernel. `#print axioms` on both
theorems shows only `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace ShannonCapacity

open Finset SimpleGraph ShannonBounds

variable {V : Type*} [Fintype V]

/-- **`α(G) ≤ Θ(G)`.** Reading each vertex as a word of length 1 sends independent sets
of `G` to independent sets of `G^⊠1`, so `α(G) ≤ α(G^⊠1)`, which is the `n = 1` term of
the supremum. -/
theorem indepNum_le_shannonCapacity (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ shannonCapacity G := by
  have h1 : G.indepNum ≤ (strongPower G 1).indepNum := by
    refine independenceNumber_le_of_cohomomorphism G _ (fun v _ ↦ v) ?_
    intro u v huv hnadj
    refine ⟨fun h ↦ huv (congrFun h 0), fun ⟨_, h⟩ ↦ ?_⟩
    rcases h 0 with h | h
    · exact huv h
    · exact hnadj h
  have := shannonCapacity_ge_root G 1 le_rfl
  simp only [Nat.cast_one, div_one, Real.rpow_one] at this
  exact le_trans (by exact_mod_cast h1) this

/-! ### The pentagon -/

/-- Shannon's code of length 2 for the pentagon: the five words `(i, 2i)`. -/
def code : Finset (Fin 2 → Fin 5) := univ.image fun i ↦ ![i, 2 * i]

theorem card_code : code.card = 5 := by decide

/-- The one finite check: for distinct `a ≠ b` in `ℤ/5`, the words `(a, 2a)` and
`(b, 2b)` are distinguishable — in some coordinate the letters differ and are not
adjacent in `C₅`. 25 cases, checked by `decide`. -/
theorem code_distinguishable : ∀ a b : Fin 5, a ≠ b →
    ¬ ((a = b ∨ (cycleGraph 5).Adj a b) ∧
       (2 * a = 2 * b ∨ (cycleGraph 5).Adj (2 * a) (2 * b))) := by
  decide

theorem code_isIndepSet : (strongPower (cycleGraph 5) 2).IsIndepSet (code : Set _) := by
  rintro _ hx _ hy hxy ⟨_, h⟩
  simp only [code, coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a ≠ b := fun h ↦ hxy (h ▸ rfl)
  exact code_distinguishable a b hab ⟨by simpa using h 0, by simpa using h 1⟩

/-- **`√5 ≤ Θ(C₅)`** (Shannon 1956). -/
theorem sqrt_five_le_shannonCapacity_C5 : √5 ≤ shannonCapacity (cycleGraph 5) := by
  have h5 : 5 ≤ (strongPower (cycleGraph 5) 2).indepNum :=
    card_code ▸ code_isIndepSet.card_le_indepNum
  calc √5 = (5 : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) := by
        rw [Real.sqrt_eq_rpow]; norm_num
    _ ≤ ((strongPower (cycleGraph 5) 2).indepNum : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) := by
        gcongr; exact_mod_cast h5
    _ ≤ shannonCapacity (cycleGraph 5) := shannonCapacity_ge_root _ 2 (by norm_num)

end ShannonCapacity
