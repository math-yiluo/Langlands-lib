/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SmoothPurity.OrientationCanonical
public import WeilConjectures.WeilSheaf.SmoothPurityReductionComparison

/-! # Prescribed finite smooth orientations and their invertibility criterion -/

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

/-- A lift of the canonical finite orientations is invertible already modulo `ℓ`. -/
theorem isIso_of_isIntegralSmoothOrientation
    (φ : (shiftFunctor (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) (2 * d : ℤ)).obj
        (integralTateTwistBoundedConstructible ℓ E.1 X.hom d) ⟶
      (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _))
    (hφ : IsIntegralSmoothOrientation ℓ E f d φ) : IsIso φ := by
  apply isIso_of_isIso_etaleReduction_map ℓ E.1 one_ne_zero φ
  change IsIso ((finiteEtaleReading ℓ E.1 1 X).map
    ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 1).map φ))
  rw [hφ 0]
  infer_instance

/-- A rational orientation with the specified integral normalization is invertible. -/
theorem isIso_of_isCanonicalSmoothOrientation
    (φ : boundedConstructibleTateTwist ℓ X d (2 * d) ⟶
      (boundedConstructibleUpperShriek ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (hφ : IsCanonicalSmoothOrientation ℓ f d φ) : IsIso φ := by
  obtain ⟨φ₀, hφ₀, rfl⟩ := hφ
  have := isIso_of_isIntegralSmoothOrientation ℓ ⟨⊥, inferInstance⟩ f d φ₀ hφ₀
  infer_instance

/-- The finite orientation together with its specified étale reading. -/
noncomputable def canonicalFiniteIntegralOrientationData (n : ℕ) :=
  purityPreimageIsoWithHom
    (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E.1 n X))
    ((finiteEtaleReading ℓ E.1 n X).mapIso
        (boundedConstructibleIntegersModPowReductionShiftIso ℓ E.1 n X.left _ (2 * d : ℤ)) ≪≫
      ((finiteEtaleReading ℓ E.1 n X).commShiftIso (2 * d : ℤ)).app _ ≪≫
      etaleReductionSmoothOrientationIso ℓ E f d n)

/-- The canonical finite orientation, transported back from the fully faithful étale reading. -/
noncomputable def canonicalFiniteIntegralOrientationIso (n : ℕ) :
    (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
        ((shiftFunctor _ (2 * d : ℤ)).obj
          (integralTateTwistBoundedConstructible ℓ E.1 X.hom d)) ≅
      (boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) :=
  (canonicalFiniteIntegralOrientationData ℓ E f d n).val

lemma canonicalFiniteIntegralOrientationIso_map_hom (n : ℕ) :
    (finiteEtaleReading ℓ E.1 n X).map
        (canonicalFiniteIntegralOrientationIso ℓ E f d n).hom =
      (finiteEtaleReading ℓ E.1 n X).map
          (boundedConstructibleIntegersModPowReductionShiftIso ℓ E.1 n X.left _
            (2 * d : ℤ)).hom ≫
        ((finiteEtaleReading ℓ E.1 n X).commShiftIso (2 * d : ℤ)).hom.app _ ≫
          (etaleReductionSmoothOrientationIso ℓ E f d n).hom := by
  exact (canonicalFiniteIntegralOrientationData ℓ E f d n).property

end AlgebraicGeometry.ProEtale.CondensedRing
