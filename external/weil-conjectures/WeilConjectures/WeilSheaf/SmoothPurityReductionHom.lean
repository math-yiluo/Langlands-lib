/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SmoothPurity.OrientationCanonical

/-! # Finiteness of the finite orientation spaces -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)]
  {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]

/-- There are only finitely many candidate orientations at every finite coefficient level.
This does not require a canonical orientation or its compatibility with reduction. -/
theorem finite_hom_derivedReduction_integralOrientation (n : ℕ) :
    Finite
      ((Mod.extendScalars (integersModPowReduction X.left ℓ E n)).leftDerivedFunctor.obj
          ((shiftFunctor _ (2 * d : ℤ)).obj
            (integralTateTwistBoundedConstructible ℓ E X.hom d)).obj ⟶
        (Mod.extendScalars (integersModPowReduction X.left ℓ E n)).leftDerivedFunctor.obj
          ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f).obj (𝟙_ _)).obj) := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E n) X.left :=
    HasInvertibleExponent.of_hom X.hom
  let T := integralTateTwistBoundedConstructible ℓ E X.hom d
  let W := (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f).obj (𝟙_ _)
  let red := boundedConstructibleIntegersModPowReduction X.left ℓ E n
  let ιn := (boundedConstructible (condensedRingObj
    (Profinite.integersModPowRingObj ℓ E n) X.left)).ι
  obtain ⟨e⟩ := nonempty_shift_etaleReduction_integralTateTwist_iso_upperShriek
    (ℓ := ℓ) (E := E) n f d
  have hfin := Etale.finite_endomorphisms_tateObject (integersModPowCoeff.{u} ℓ E n) X.left d
  have h₁ : Finite ((shiftFunctor _ (2 * d : ℤ)).obj
      ((finiteEtaleReading ℓ E n X).obj (red.obj T)) ⟶
        (finiteEtaleReading ℓ E n X).obj (red.obj W)) := by
    let eT := (shiftFunctor _ (2 * d : ℤ)).mapIso
      (etaleReductionIntegralTateTwistIso ℓ E n X d).symm
    exact @Finite.of_equiv _ _ hfin
      ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor _ (2 * d : ℤ))).homEquiv.trans
        (eT.homCongr (eT ≪≫ e)))
  have h₂ := finite_shift_hom_of_finiteEtaleReading (2 * d : ℤ) h₁
  have h₃ : Finite (red.obj ((shiftFunctor _ (2 * d : ℤ)).obj T) ⟶ red.obj W) :=
    @Finite.of_equiv _ _ h₂
      ((boundedConstructibleIntegersModPowReductionShiftIso ℓ E n X.left T
        (2 * d : ℤ)).homCongr (Iso.refl _)).symm
  exact @Finite.of_equiv _ _ h₃
    ((ObjectProperty.fullyFaithfulι _).homEquiv.trans
      (((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app _).homCongr
        ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app W)))

end AlgebraicGeometry.ProEtale.CondensedRing
