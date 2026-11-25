/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCanonicalCriterion
public import WeilConjectures.WeilSheaf.SmoothPurityReductionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms

/-! # Reconstruction of the canonical integral smooth orientation

The prescribed finite orientations lift once they commute with the actual reduction
transitions. Derived Nakayama makes every such lift invertible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d f.left]

/-- The same prescribed orientation in the ambient derived category of the reduction. -/
noncomputable def canonicalAmbientIntegralOrientationIso (n : ℕ) :
    (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.obj
        ((shiftFunctor _ (2 * d : ℤ)).obj
          (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)).obj ≅
      (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctor.obj
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)).obj :=
  purityReductionIso _ _ _ _
    (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E.1 n)
    (canonicalFiniteIntegralOrientationIso ℓ E f d n)

/-- Compatibility with the actual reduction transitions is the sole reconstruction input. -/
def CanonicalIntegralOrientationCompatible : Prop :=
  ∀ n : ℕ,
    (Mod.comap (integersModPowReduction X.left ℓ E.1 (n + 1 + 1))).mapDerivedCategory.map
        (canonicalAmbientIntegralOrientationIso ℓ E f d (n + 1 + 1)).hom ≫
      reductionTransition E.1 (n + 1)
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)).obj =
    reductionTransition E.1 (n + 1)
        ((shiftFunctor _ (2 * d : ℤ)).obj
          (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)).obj ≫
      (Mod.comap (integersModPowReduction X.left ℓ E.1 (n + 1))).mapDerivedCategory.map
        (canonicalAmbientIntegralOrientationIso ℓ E f d (n + 1)).hom

/-- Reconstruct the prescribed finite orientations, with their normalization intact. -/
theorem exists_isIntegralSmoothOrientation_of_compatible
    (h : CanonicalIntegralOrientationCompatible ℓ E f d) :
    ∃ φ, IsIntegralSmoothOrientation ℓ E f d φ := by
  let K := (shiftFunctor _ (2 * d : ℤ)).obj
    (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)
  let W := (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)
  have hW : derivedCompleteIntegers ℓ E.1 X.left W.obj := by
    have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
    exact derivedCompleteIntegers_of_boundedConstructible W.property
  let ι := (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1)
    X.left)).ι
  obtain ⟨φ, hφ⟩ := exists_derivedReduction_map_eq
    (K := K.obj) hW
    (fun n ↦ (canonicalAmbientIntegralOrientationIso ℓ E f d (n + 1)).hom) h
  let g : K ⟶ W := (ObjectProperty.fullyFaithfulι _).preimage φ
  have hg : ι.map g = φ := (ObjectProperty.fullyFaithfulι _).map_preimage _
  refine ⟨g, isIntegralSmoothOrientation_of_reduction_map_eq ℓ E f d g (fun n ↦ ?_)⟩
  have hr : (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 (n + 1)).map g =
      (canonicalFiniteIntegralOrientationIso ℓ E f d (n + 1)).hom := by
    apply purity_reduction_map_eq_of_comparison ι _ _ _
      (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E.1 (n + 1))
    exact (congrArg
      (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 (n + 1))).leftDerivedFunctor.map
      hg).trans (hφ n)
  exact hr

/-- The integral reconstruction supplies an invertible canonical rational orientation. -/
theorem exists_isIso_isCanonicalSmoothOrientation_of_compatible
    (h : CanonicalIntegralOrientationCompatible ℓ ⟨⊥, inferInstance⟩ f d) :
    ∃ φ, IsIso φ ∧ IsCanonicalSmoothOrientation ℓ f d φ := by
  obtain ⟨φ₀, hφ₀⟩ := exists_isIntegralSmoothOrientation_of_compatible ℓ
    ⟨⊥, inferInstance⟩ f d h
  have := isIso_of_isIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀ hφ₀
  exact ⟨extendScalarsIntegralOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀,
    inferInstance, φ₀, hφ₀, rfl⟩

end AlgebraicGeometry.ProEtale.CondensedRing
