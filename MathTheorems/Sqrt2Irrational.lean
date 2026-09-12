import Mathlib

/-!
# `√2` is irrational, from first principles

Mathlib proves this in one line — `(Nat.prime_two).irrational_sqrt`. This file does
it the long way instead, because the long way is the interesting one.

The argument is Euclid's, by **infinite descent**: assume `p² = 2q²` with `q ≠ 0`.
Then `p` must be even, so `p = 2k`; substituting gives `q² = 2k²`, so `q` is even
too, `q = 2m`, and `k² = 2m²`. But `k < p`, so we have produced a strictly smaller
solution. Since the naturals cannot descend forever, no solution exists.

Four steps, each proved below:

1. `even_of_even_sq`  — if `n²` is even, so is `n`
2. `no_sq_eq_two_sq`  — no naturals satisfy `p² = 2q²` with `q ≠ 0`
3. `no_rat_sq_two`    — hence no rational squares to `2`
4. `sqrt_two_irrational` — hence `√2` is not rational
-/

/-- If `n²` is even, so is `n`.

Proved by contraposition: an odd number squared is odd. This is the only place
the primality of `2` really enters. -/
theorem even_of_even_sq {n : ℕ} (h : Even (n ^ 2)) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exact absurd ho.pow (Nat.not_odd_iff_even.mpr h)

/-- **Infinite descent.** No naturals satisfy `p² = 2q²` with `q ≠ 0`.

Strong induction on `p`: from any solution we build one with a strictly smaller
first component, which the induction hypothesis forbids. -/
theorem no_sq_eq_two_sq : ∀ p q : ℕ, q ≠ 0 → p ^ 2 ≠ 2 * q ^ 2 := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro q hq h
    -- `p² = 2q²` is even, so `p` is even: write `p = k + k`
    have hp : Even p := even_of_even_sq ⟨q ^ 2, by omega⟩
    obtain ⟨k, hk⟩ := hp
    subst hk
    -- substituting and halving: `q² = 2k²`
    have hq2 : q ^ 2 = 2 * k ^ 2 := by nlinarith [h]
    -- so `q` is even too: write `q = m + m`
    have hqe : Even q := even_of_even_sq ⟨k ^ 2, by omega⟩
    obtain ⟨m, hm⟩ := hqe
    subst hm
    -- and again: `k² = 2m²` — a smaller solution
    have hk2 : k ^ 2 = 2 * m ^ 2 := by nlinarith [hq2]
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp at hq2; omega
      · exact hpos
    exact ih k (by omega) m (by omega) hk2

/-- No rational squares to `2`.

A rational is `num / den`; squaring and clearing denominators turns `r² = 2` into
`num² = 2·den²` over `ℤ`, which `no_sq_eq_two_sq` rules out. -/
theorem no_rat_sq_two (r : ℚ) : r ^ 2 ≠ 2 := by
  intro h
  have hq : (r.num : ℚ) ^ 2 = 2 * (r.den : ℚ) ^ 2 := by
    rw [← Rat.num_div_den r] at h
    field_simp at h
    linarith [h]
  have key : r.num ^ 2 = 2 * (r.den : ℤ) ^ 2 := by exact_mod_cast hq
  refine no_sq_eq_two_sq r.num.natAbs r.den r.den_nz ?_
  have final : (r.num.natAbs : ℤ) ^ 2 = 2 * (r.den : ℤ) ^ 2 := by
    rw [Int.natAbs_pow_two]; exact key
  exact_mod_cast final

/-- **`√2` is irrational.**

`Irrational x` means `x` is not in the range of the coercion `ℚ → ℝ`. So assume it
is some rational `r`; then `r² = 2`, which the previous step forbids. -/
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  rintro ⟨r, hr⟩
  apply no_rat_sq_two r
  have : ((r : ℝ)) ^ 2 = 2 := by
    rw [hr]; exact Real.sq_sqrt (by norm_num)
  exact_mod_cast this
