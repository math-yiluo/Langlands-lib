/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityReductionHom
public import WeilConjectures.EtaleCohomology.TateTwist.AffineLine

/-! # The Milnor obstruction for maps out of the integral Tate orientation -/

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

/-- The groups controlling uniqueness of the integral orientation lift are finite:
after adjunction and étale reading they are negative extensions between Tate lines. -/
theorem finite_shift_hom_integralOrientation_reduction (n : ℕ) :
    Finite
      ((shiftFunctor _ (1 : ℤ)).obj
          ((shiftFunctor _ (2 * d : ℤ)).obj
            (integralTateTwistBoundedConstructible ℓ E X.hom d)).obj ⟶
        (Mod.comap (integersModPowReduction X.left ℓ E n)).mapDerivedCategory.obj
          ((Mod.extendScalars (integersModPowReduction X.left ℓ E n)).leftDerivedFunctor.obj
            ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f).obj (𝟙_ _)).obj)) := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have : HasInvertibleExponent (integersModPowCoeff.{u} ℓ E n) X.left :=
    HasInvertibleExponent.of_hom X.hom
  let T := integralTateTwistBoundedConstructible ℓ E X.hom d
  let S := (shiftFunctor _ (2 * d : ℤ)).obj T
  let W := (PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E f).obj (𝟙_ _)
  let red := boundedConstructibleIntegersModPowReduction X.left ℓ E n
  let ρ := finiteEtaleReading ℓ E n X
  let ιn := (boundedConstructible (condensedRingObj
    (Profinite.integersModPowRingObj ℓ E n) X.left)).ι
  let Lred := (Mod.extendScalars (integersModPowReduction X.left ℓ E n)).leftDerivedFunctor
  let eS : ρ.obj (red.obj S) ≅ (ρ.obj (red.obj T)) ⟦(2 * d : ℤ)⟧ :=
    ρ.mapIso (boundedConstructibleIntegersModPowReductionShiftIso ℓ E n X.left T _) ≪≫
      (ρ.commShiftIso (2 * d : ℤ)).app _
  obtain ⟨eW⟩ := nonempty_shift_etaleReduction_integralTateTwist_iso_upperShriek
    (ℓ := ℓ) (E := E) n f d
  have : (ρ.obj (red.obj T)).IsLE 0 :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (etaleReductionIntegralTateTwistIso ℓ E n X d).symm 0
  have : (ρ.obj (red.obj T)).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (etaleReductionIntegralTateTwistIso ℓ E n X d).symm 0
  have := DerivedCategory.TStructure.t.isLE_shift (ρ.obj (red.obj T)) 0
    (2 * d : ℤ) (-(2 * d : ℤ))
  have := DerivedCategory.TStructure.t.isGE_shift (ρ.obj (red.obj T)) 0
    (2 * d : ℤ) (-(2 * d : ℤ))
  have : (ρ.obj (red.obj S)).IsLE (-(2 * d : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_of_iso eS.symm _
  have : (ρ.obj (red.obj W)).IsGE (-(2 * d : ℤ)) :=
    DerivedCategory.TStructure.t.isGE_of_iso eW _
  have := DerivedCategory.TStructure.t.isLE_shift (ρ.obj (red.obj S))
    (-(2 * d : ℤ)) 1 (-(2 * d : ℤ) - 1) (by omega)
  have : Subsingleton ((ρ.obj (red.obj S)) ⟦(1 : ℤ)⟧ ⟶ ρ.obj (red.obj W)) :=
    ⟨fun a b ↦ (DerivedCategory.TStructure.t.zero a
      (-(2 * d : ℤ) - 1) (-(2 * d : ℤ)) (by omega)).trans
      (DerivedCategory.TStructure.t.zero b
        (-(2 * d : ℤ) - 1) (-(2 * d : ℤ)) (by omega)).symm⟩
  have h₁ : Finite ((ρ.obj (red.obj S)) ⟦(1 : ℤ)⟧ ⟶ ρ.obj (red.obj W)) := inferInstance
  have h₂ := finite_shift_hom_of_finiteEtaleReading (1 : ℤ) h₁
  let A : Lred.obj (S.obj⟦(1 : ℤ)⟧) ≅ ιn.obj ((red.obj S) ⟦(1 : ℤ)⟧) :=
    (Lred.commShiftIso (1 : ℤ)).app S.obj ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso
        ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app S).symm ≪≫
      ((ιn.commShiftIso (1 : ℤ)).app (red.obj S)).symm
  let B := ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app W).symm
  have h₃ : Finite (Lred.obj (S.obj⟦(1 : ℤ)⟧) ⟶ Lred.obj W.obj) :=
    @Finite.of_equiv _ _ h₂
      ((ObjectProperty.fullyFaithfulι _).homEquiv.trans (A.homCongr B).symm)
  exact @Finite.of_equiv _ _ h₃
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (integersModPowReduction X.left ℓ E n)).homEquiv _ _)

end AlgebraicGeometry.ProEtale.CondensedRing
