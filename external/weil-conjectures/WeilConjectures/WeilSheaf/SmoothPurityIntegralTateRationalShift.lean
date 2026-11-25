/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateShiftNormalization
import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientPullShift
public import WeilConjectures.WeilSheaf.SmoothPurityShiftDatumSquare
public import WeilConjectures.WeilSheaf.SmoothPurityDerivedFunctorShift

/-! # Rationalization of shifted integral Tate data -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [NeZero (ℓ : k)] {X X' : Scheme.{u}}

/-- Rationalization of the shifted integral Tate twist, with the canonical shift map. -/
noncomputable def purityExtendScalarsShiftIntegralTateIso
    (f : X ⟶ Spec (.of k)) (d : ℕ) (n : ℤ) :
    L(Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X)).obj
      (((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) ⟦n⟧) ≅
      (tateTwistDerived X ℓ d) ⟦n⟧ :=
  (L(Mod.extendScalars
    (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X)).commShiftIso n).app _ ≪≫
      (shiftFunctor _ n).mapIso (purityExtendScalarsIntegralTateIso ℓ E f d)

/-- The actual integral Tate datum, including the purity shift, rationalizes to the
canonical rational Tate datum under the nonflat coefficient/pullback comparison. -/
lemma upperStarShiftIntegralTateTwistDerivedIso_hom_comp_rationalization
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (d : ℕ) (n : ℤ) :
    (derivedUpperStarExtendScalarsIso (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) g).inv.app
          (((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) ⟦n⟧) ≫
        L(Mod.extendScalars
          (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X')).map
          (upperStarShiftIntegralTateTwistDerivedIso ℓ E g f d n).hom ≫
        (purityExtendScalarsShiftIntegralTateIso ℓ E (g ≫ f) d n).hom =
      L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          (purityExtendScalarsShiftIntegralTateIso ℓ E f d n).hom ≫
        (upperStarShiftTateTwistDerivedIso ℓ g f d n).hom := by
  have h := purity_shift_datum_square
    (purityDerivedPullback (Profinite.padicIntegersRingObj ℓ E) g)
    (purityDerivedCoefficientExtension (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X')
    (purityDerivedCoefficientExtension (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X)
    (purityDerivedPullback (Profinite.padicAlgClRingObj ℓ) g)
    (derivedUpperStarExtendScalarsIso (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) g).inv
    (upperStarIntegralTateTwistDerivedIso ℓ E g f d).hom
    (upperStarTateTwistDerivedIso ℓ g f d).hom
    (purityExtendScalarsIntegralTateIso ℓ E f d).hom
    (purityExtendScalarsIntegralTateIso ℓ E (g ≫ f) d).hom
    (upperStarIntegralTateTwistDerivedIso_hom_comp_rationalization ℓ E g f d) n
  simp only [upperStarShiftIntegralTateTwistDerivedIso_hom_eq,
    purityExtendScalarsShiftIntegralTateIso, upperStarShiftTateTwistDerivedIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h ⊢
  dsimp only [purityDerivedCoefficientExtension, purityDerivedPullback,
    purityDerivedCoefficientExtension_commShift, purityDerivedPullback_commShift,
    Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale
