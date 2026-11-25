/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/

/-
Vendored, unmodified apart from this note, from `ShannonBounds/Defs.lean` in
https://github.com/spectra-research/shannon-capacity-lean (commit aa21eeb, Apache-2.0),
the Lean code accompanying Buys, Polak and Zuiddam, "Lean-verified lower bounds for the
Shannon capacity of odd cycles" (arXiv:2607.29681). Copied rather than required as a Lake
dependency so this repo stays on its own Mathlib version; the rest of that library (the
`C₇`–`C₂₃` certificates, which rely on `native_decide`) is not included.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The strong product, the strong power, and the Shannon capacity

These are the definitions the capacity bounds use.

`shannonCapacity G` is `⨆ n, α(G^⊠(n+1))^(1/(n+1))`, the usual supremum, and
`shannonCapacity_ge_root` is the bound that turns one independent set in one
strong power into a lower bound on the capacity.  `indepNum` is Mathlib's.
-/

namespace ShannonBounds

variable {U V W : Type*}

/-- The strong product of two simple graphs.
    Vertices (a,x) and (b,y) are adjacent iff
    (a = b ∨ a ~ b) ∧ (x = y ∨ x ~ y) and (a,x) ≠ (b,y). -/
def strongProduct (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) where
  Adj p q := p ≠ q ∧ (p.1 = q.1 ∨ G.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ H.Adj p.2 q.2)
  symm := ⟨by
    intro p q ⟨hne, h1, h2⟩
    refine ⟨hne.symm, ?_, ?_⟩
    · cases h1 with
      | inl h => left; exact h.symm
      | inr h => right; exact h.symm
    · cases h2 with
      | inl h => left; exact h.symm
      | inr h => right; exact h.symm⟩
  loopless := ⟨fun _ ⟨hne, _, _⟩ => (hne rfl).elim⟩

@[inherit_doc] infixl:70 " ⊠ " => strongProduct

end ShannonBounds

namespace SimpleGraph

variable {V W : Type*}

/-- The n-th strong power of a graph G^⊠n.
    Vertices are functions `Fin n → V`, and two vertices f, g are adjacent iff
    f ≠ g and for all i, either f(i) = g(i) or f(i) ~ g(i) in G. -/
def strongPower (G : SimpleGraph V) (n : ℕ) : SimpleGraph (Fin n → V) where
  Adj f g := f ≠ g ∧ ∀ i, f i = g i ∨ G.Adj (f i) (g i)
  symm := ⟨by
    intro f g ⟨hne, h⟩
    refine ⟨hne.symm, fun i => ?_⟩
    cases h i with
    | inl heq => left; exact heq.symm
    | inr hadj => right; exact hadj.symm⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => (hne rfl).elim⟩

/-- A cohomomorphism from G to H implies α(G) ≤ α(H).
    A cohomomorphism maps distinct non-adjacent pairs to distinct non-adjacent pairs,
    so it maps independent sets injectively to independent sets. -/
theorem independenceNumber_le_of_cohomomorphism [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hf : ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v)) :
    G.indepNum ≤ H.indepNum := by
  classical
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  have hS_indep : G.IsIndepSet (S : Set V) :=
    (SimpleGraph.isMaximumIndepSet_iff G S).1 hSmax |>.1
  let fS := S.image f
  have hfS_indep : H.IsIndepSet (fS : Set W) := by
    apply (SimpleGraph.isIndepSet_iff H).2
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    have hxy : x ≠ y := fun h => huv (by simp [h])
    have hpair := (SimpleGraph.isIndepSet_iff G).1 hS_indep
    have hnadj : ¬ G.Adj x y := hpair (by simpa using hx) (by simpa using hy) hxy
    exact fun hadj => (hf x y hxy hnadj).2 hadj
  have hf_inj : Set.InjOn f ↑S := by
    intro x hx y hy hxy
    by_contra hne
    have hpair := (SimpleGraph.isIndepSet_iff G).1 hS_indep
    have hnadj : ¬ G.Adj x y := hpair (by simpa using hx) (by simpa using hy) hne
    exact (hf x y hne hnadj).1 hxy
  have hcard : fS.card = S.card := Finset.card_image_of_injOn hf_inj
  have hle : S.card ≤ H.indepNum := by
    simpa [hcard] using SimpleGraph.IsIndepSet.card_le_indepNum (G := H) (t := fS) hfS_indep
  have hS_card : S.card = G.indepNum := by
    simpa using SimpleGraph.maximumIndepSet_card_eq_indepNum (G := G) S hSmax
  calc G.indepNum = S.card := hS_card.symm
    _ ≤ H.indepNum := hle

/-- A graph isomorphism is a cohomomorphism. -/
private lemma iso_is_cohomomorphism' {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v) := by
  intro u v huv hnadj
  exact ⟨fun h => huv (f.injective h), fun hadj => hnadj (f.map_rel_iff'.mp hadj)⟩

set_option linter.unusedFintypeInType false in

/-- Independence number is monotone under graph isomorphisms. -/
private lemma indepNum_le_of_iso' [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    G.indepNum ≤ H.indepNum :=
  independenceNumber_le_of_cohomomorphism G H f (iso_is_cohomomorphism' f)

set_option linter.unusedFintypeInType false in

/-- Independence number is preserved under graph isomorphism.
    This follows because isomorphisms bijectively map independent sets to independent sets. -/
theorem independenceNumber_iso [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    G.indepNum = H.indepNum :=
  le_antisymm (indepNum_le_of_iso' f) (indepNum_le_of_iso' f.symm)

end SimpleGraph

namespace ShannonBounds

open SimpleGraph

variable {U V W : Type*}

/-- Adjacency in `strongPower G n` is
`f ≠ g ∧ ∀ i, f i = g i ∨ G.Adj (f i) (g i)`, which is decidable componentwise. -/
instance strongPower_adj_decidable {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    DecidableRel (SimpleGraph.strongPower G n).Adj := fun f g => by
  change Decidable (f ≠ g ∧ ∀ i : Fin n, f i = g i ∨ G.Adj (f i) (g i))
  exact instDecidableAnd

/-- Associativity of the strong product as a graph isomorphism:
    `(A ⊠ B) ⊠ C ≃g A ⊠ (B ⊠ C)`. -/
def strongProduct_assoc_iso (A : SimpleGraph U) (B : SimpleGraph V) (C : SimpleGraph W) :
    (A ⊠ B) ⊠ C ≃g A ⊠ (B ⊠ C) where
  toEquiv := Equiv.prodAssoc U V W
  map_rel_iff' := by
    intro ⟨⟨a₁, b₁⟩, c₁⟩ ⟨⟨a₂, b₂⟩, c₂⟩
    simp only [strongProduct, Equiv.prodAssoc_apply, ne_eq, Prod.mk.injEq]
    tauto

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in

/-- The Shannon capacity Θ(G) = sup_{n≥1} α(G^⊠n)^(1/n) -/
noncomputable def shannonCapacity (G : SimpleGraph V) [Fintype V] : ℝ :=
  ⨆ n : ℕ, ((strongPower G (n + 1)).indepNum : ℝ) ^ (1 / (n + 1 : ℝ))

/-- The independence number is bounded by the number of vertices. -/
theorem independenceNumber_le_card (G : SimpleGraph V) [Fintype V] :
    G.indepNum ≤ Fintype.card V := by
  classical
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  have hS_card : S.card = G.indepNum := by
    simpa using
      (SimpleGraph.maximumIndepSet_card_eq_indepNum (G := G) S hSmax)
  have hle : S.card ≤ Fintype.card V := by
    simpa using (Finset.card_le_univ (s := S))
  simpa [hS_card] using hle

set_option linter.unusedFintypeInType false in

/-- The Shannon capacity sequence is bounded above by the cardinality of the vertex set. -/
lemma shannonCapacity_bddAbove (G : SimpleGraph V) [Fintype V] :
    BddAbove (Set.range fun m =>
      ((strongPower G (m + 1)).indepNum : ℝ) ^ (1 / (m + 1 : ℝ))) := by
  use (Fintype.card V : ℝ)
  intro x ⟨m, hm⟩
  rw [← hm]
  have hexp_pos : (0 : ℝ) ≤ 1 / (m + 1) := by positivity
  have hcard_pos : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hindep_le : ((strongPower G (m + 1)).indepNum : ℝ) ≤
      (Fintype.card (Fin (m + 1) → V) : ℝ) := by
    exact_mod_cast independenceNumber_le_card (strongPower G (m + 1))
  have hcard_eq : Fintype.card (Fin (m + 1) → V) = (Fintype.card V) ^ (m + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin]
  calc ((strongPower G (m + 1)).indepNum : ℝ) ^ (1 / (m + 1 : ℝ))
      ≤ (Fintype.card (Fin (m + 1) → V) : ℝ) ^ (1 / (m + 1 : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) hindep_le hexp_pos
    _ = ((Fintype.card V : ℝ) ^ (m + 1 : ℕ)) ^ (1 / (m + 1 : ℝ)) := by
        rw [hcard_eq]; norm_cast
    _ = (Fintype.card V : ℝ) ^ ((m + 1 : ℕ) * (1 / (m + 1 : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hcard_pos]
    _ = (Fintype.card V : ℝ) ^ (1 : ℝ) := by
        congr 1; push_cast; field_simp
    _ = Fintype.card V := Real.rpow_one _

/-- Lower bound: Shannon capacity is at least α(G^⊠n)^(1/n) for any n ≥ 1.
This follows directly from the definition of Shannon capacity as a supremum. -/
theorem shannonCapacity_ge_root (G : SimpleGraph V) [Fintype V] (n : ℕ) (hn : n ≥ 1) :
    shannonCapacity G ≥ ((strongPower G n).indepNum : ℝ) ^ (1 / (n : ℝ)) := by
  simp only [shannonCapacity]
  apply le_ciSup_of_le (shannonCapacity_bddAbove G) (n - 1)
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [h]
  simp only [← Nat.cast_add_one, h, le_refl]

end ShannonBounds
