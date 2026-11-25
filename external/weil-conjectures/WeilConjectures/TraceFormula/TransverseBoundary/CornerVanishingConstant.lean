/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.OpenClosed.CohomologyVanishing
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerStrictLocalization

/-!
# Constant coefficients in the vanishing at the transverse corner

Let `S` be the strict localization of the surface of a transverse corner at a geometric point
`z̄` over the corner point, `ι : X_S - z ⟶ S - Y_S` the closed immersion of the punctured trait
and `i' : S - (X_S ∪ Y_S) ⟶ S - Y_S` the complementary open immersion. If the restriction maps
`H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)` are bijective (blueprint
`lemma-punctured-surface-punctured-curve--1`), then `H^q(S - Y_S, i'_! ℤ/ℓ) = 0` for all `q`: by the
open–closed sequence `0 → i'_! ℤ/ℓ → ℤ/ℓ → ι_* ℤ/ℓ → 0` (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`, constant coefficients).

## Main statements

- `AlgebraicGeometry.Scheme.TransverseCorner.range_puncturedTraitι`: the punctured trait is the
  complement of `S - (X_S ∪ Y_S)` in `S - Y_S`.
- `AlgebraicGeometry.Scheme.TransverseCorner.subsingleton_sheafH_strictLocalizationComplement`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] (C : TransverseCorner k) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (zbar : Spec (.of Ω) ⟶ C.Z)

/-- In `Z - Y`, the complement `Z - (X ∪ Y)` is the complement of the inverse image of `X`. -/
lemma range_i_eq_compl_preimage_range_iX :
    Set.range C.i = (C.j ⁻¹' Set.range C.iX)ᶜ := by
  ext u
  refine ⟨?_, fun hX ↦ ?_⟩
  · rintro ⟨v, rfl⟩ hX
    have h : C.j (C.i v) ∈ Set.range (C.i ≫ C.j) := ⟨v, Scheme.Hom.comp_apply _ _ _⟩
    rw [C.range_i_j] at h
    exact h (Or.inl hX)
  · have hY : C.j u ∉ Set.range C.iY := by
      rw [← Set.mem_compl_iff, ← C.range_j]
      exact ⟨u, rfl⟩
    have h : C.j u ∈ Set.range (C.i ≫ C.j) := by
      rw [C.range_i_j]
      rintro (h | h)
      exacts [hX h, hY h]
    obtain ⟨v, hv⟩ := h
    rw [Scheme.Hom.comp_apply] at hv
    exact ⟨v, C.j.isOpenEmbedding.injective hv⟩

/-- The punctured trait `X_S - z = (X - z) ×_{Z - Y} (S - Y_S)` is the closed complement of
`S - (X_S ∪ Y_S)` in `S - Y_S`. -/
lemma range_puncturedTraitι :
    Set.range (pullback.snd (pullback.snd C.iX C.j)
        (pullback.fst C.j (strictLocalizationToBase zbar))).base =
      (Set.range (C.strictLocalizationComplementι zbar).base)ᶜ := by
  have h₁ := Scheme.Pullback.range_snd (pullback.snd C.iX C.j)
    (pullback.fst C.j (strictLocalizationToBase zbar))
  have h₂ := Scheme.Pullback.range_snd C.i (pullback.fst C.j (strictLocalizationToBase zbar))
  have h₃ := Scheme.Pullback.range_snd C.iX C.j
  rw [C.range_i_eq_compl_preimage_range_iX, ← h₃] at h₂
  rw [h₂, Set.preimage_compl, compl_compl]
  exact h₁

/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1`, constant coefficients: if the
restriction maps `H^q(S - Y_S, ℤ/ℓ) ⟶ H^q(X_S - z, ℤ/ℓ)` are bijective in every degree, then
`H^q(S - Y_S, i'_! ℤ/ℓ) = 0` for the open immersion `i' : S - (X_S ∪ Y_S) ⟶ S - Y_S`. -/
theorem subsingleton_sheafH_strictLocalizationComplement (ℓ : ℕ)
    (h : ∀ q : ℕ, Function.Bijective (Etale.cohomologyMap
      (pullback.snd (pullback.snd C.iX C.j) (pullback.fst C.j (strictLocalizationToBase zbar)))
      ((pullback C.j (strictLocalizationToBase zbar)).constantZMod ℓ) q)) (q : ℕ) :
    Subsingleton (Sheaf.H ((C.strictLocalizationComplementι zbar)_!open[AddCommGrpCat.{u + 1}].obj
      ((C.strictLocalizationComplementι zbar)^*[AddCommGrpCat.{u + 1}].obj
        ((pullback C.j (strictLocalizationToBase zbar)).constantZMod ℓ))) q) :=
  Etale.subsingleton_sheafH_openImmersionLowerShriek_of_bijective_cohomologyMap _ _
    (C.range_puncturedTraitι zbar) _ h q

end AlgebraicGeometry.Scheme.TransverseCorner
