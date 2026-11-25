/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCanonicalFinite
public import WeilConjectures.WeilSheaf.SmoothPurityReductionFaithful
public import WeilConjectures.WeilSheaf.SmoothPurityReductionHomShift

/-! # Uniqueness of the normalized integral and rational smooth orientations -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

private lemma map_eq_of_comparison
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ≅ G)
    {K W : C} (φ ψ : K ⟶ W) (h : F.map φ = F.map ψ) : G.map φ = G.map ψ := by
  apply (cancel_epi (α.hom.app K)).mp
  rw [← α.hom.naturality φ, ← α.hom.naturality ψ, h]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

/-- The finite normalization determines the integral orientation uniquely. -/
theorem eq_of_isIntegralSmoothOrientation
    {φ ψ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)}
    (hφ : IsIntegralSmoothOrientation ℓ E f d φ)
    (hψ : IsIntegralSmoothOrientation ℓ E f d ψ) : φ = ψ := by
  let K := (shiftFunctor _ (2 * d : ℤ)).obj
    (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)
  let W := (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)
  have hW : derivedCompleteIntegers ℓ E.1 X.left W.obj := by
    have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
    exact derivedCompleteIntegers_of_boundedConstructible W.property
  have := fun n : ℕ ↦ finite_shift_hom_integralOrientation_reduction
    (ℓ := ℓ) (E := E.1) f d (n + 1)
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  apply eq_of_derivedReduction_map_eq (K := K.obj) (L := W.obj) hW
  intro n
  have hred := (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E.1 (n + 1) X)).map_injective
    ((hφ n).trans (hψ n).symm)
  have hι := congrArg (boundedConstructible (condensedRingObj
    (Profinite.integersModPowRingObj ℓ E.1 (n + 1)) X.left)).ι.map hred
  exact map_eq_of_comparison
    (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E.1 (n + 1)) φ ψ hι

/-- The specified integral normalization determines the rational orientation uniquely. -/
theorem eq_of_isCanonicalSmoothOrientation
    {φ ψ : boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))}
    (hφ : IsCanonicalSmoothOrientation ℓ f d φ)
    (hψ : IsCanonicalSmoothOrientation ℓ f d ψ) : φ = ψ := by
  obtain ⟨φ₀, hφ₀, rfl⟩ := hφ
  obtain ⟨ψ₀, hψ₀, rfl⟩ := hψ
  exact congrArg (extendScalarsIntegralOrientation ℓ ⟨⊥, inferInstance⟩ f d)
    (eq_of_isIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d hφ₀ hψ₀)

end AlgebraicGeometry.ProEtale.CondensedRing
