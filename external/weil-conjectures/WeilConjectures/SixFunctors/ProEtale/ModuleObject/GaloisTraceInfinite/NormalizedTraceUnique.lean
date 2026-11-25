/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Preadditive.TraceSplitting
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Uniqueness of the invariant retraction

Let `u : G ⟶ T` be a morphism in a preadditive category with a trace `t : T ⟶ G` factoring the
norm of finitely many endomorphisms `ρ i` of `T` through `u` (`t ≫ u = ∑ i, ρ i`), with `d` the
number of the `ρ i` invertible on `G`. Then a retraction `r` of `u` invariant under the `ρ i`
(`ρ i ≫ r = r`) is the normalized trace `d⁻¹ t` (`CategoryTheory.eq_normalizedTrace`): indeed
`d • r = ∑ i, ρ i ≫ r = t ≫ u ≫ r = t`. This gives the compatibility of the normalized traces
in a tower of Galois coverings without computing the traces.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- **Uniqueness of the invariant retraction**: a retraction `r` of `u` invariant under the `ρ i`
is the normalized trace, when the trace factors the norm `∑ i, ρ i` through `u`. -/
lemma eq_normalizedTrace {G T : C} {u : G ⟶ T} {t : T ⟶ G} {ι : Type*} [Fintype ι]
    {ρ : ι → (T ⟶ T)} {d : ℕ} [IsIso (d • 𝟙 G)] (hd : Fintype.card ι = d)
    (ht : t ≫ u = ∑ i, ρ i) {r : T ⟶ G} (hr : u ≫ r = 𝟙 G) (hρr : ∀ i, ρ i ≫ r = r) :
    r = normalizedTrace t d := by
  have h : d • r = t := by
    calc d • r = ∑ i : ι, ρ i ≫ r := by simp [hρr, ← hd]
      _ = t := by rw [← Preadditive.sum_comp, ← ht, assoc, hr, comp_id]
  rw [← cancel_mono (d • 𝟙 G), normalizedTrace, assoc, IsIso.inv_hom_id, comp_id,
    Preadditive.comp_nsmul, comp_id, h]

/-- The normalized trace is invariant under endomorphisms fixing the trace. -/
lemma comp_normalizedTrace_of_comp_eq {G T : C} {t : T ⟶ G} {d : ℕ} [IsIso (d • 𝟙 G)]
    {ρ : T ⟶ T} (hρ : ρ ≫ t = t) : ρ ≫ normalizedTrace t d = normalizedTrace t d := by
  rw [normalizedTrace, reassoc_of% hρ]

/-- An endomorphism `ρ a` of a finite group of endomorphisms fixes a trace factoring the norm
through a monomorphism `u`. -/
lemma comp_eq_of_comp_eq_sum {G T : C} {u : G ⟶ T} [Mono u] {t : T ⟶ G} {Γ : Type*} [Group Γ]
    [Fintype Γ] {ρ : Γ → (T ⟶ T)} (hρ : ∀ a b, ρ a ≫ ρ b = ρ (b * a)) (ht : t ≫ u = ∑ i, ρ i)
    (a : Γ) : ρ a ≫ t = t := by
  rw [← cancel_mono u, assoc, ht, Preadditive.comp_sum]
  simp_rw [hρ]
  exact Fintype.sum_equiv (Equiv.mulRight a) _ _ fun _ ↦ rfl

end CategoryTheory
