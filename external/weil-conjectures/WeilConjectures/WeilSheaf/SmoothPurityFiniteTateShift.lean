/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteTateDerived
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateShiftNormalization
public import WeilConjectures.WeilSheaf.SmoothPurityDerivedFunctorShift
public import WeilConjectures.WeilSheaf.SmoothPurityShiftDatumSquare
import WeilConjectures.Tactic.ExactModProofs

/-! # Finite reduction of the shifted integral Tate datum -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  (n : ℕ) {k : Type u} [Field k] [NeZero (ℓ : k)] {X X' : Scheme.{u}}

/-- The finite Tate datum with a cohomological shift. -/
noncomputable def purityFiniteTateShiftPullbackIso
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (d : ℕ) (m : ℤ) :=
  ((purityDerivedPullback (Profinite.integersModPowRingObj ℓ E n) g).commShiftIso m).app
      ((DerivedCategory.singleFunctor _ 0).obj (purityFiniteTatePower ℓ E n X d)) ≪≫
    (shiftFunctor _ m).mapIso (purityFiniteTateDerivedPullbackIso ℓ E n g f d)

/-- Reduction of an integral Tate power with a cohomological shift. -/
noncomputable def purityReduceIntegralTateShiftIso
    (f : X ⟶ Spec (.of k)) (d : ℕ) (m : ℤ) :=
  ((purityDerivedCoefficientExtension
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) X).commShiftIso m).app
      ((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) ≪≫
    (shiftFunctor _ m).mapIso (purityReduceIntegralTateDerivedIso ℓ E n f d)

/-- The actual nonflat coefficient comparison carries the shifted integral Tate
pullback datum to the shifted finite root datum. -/
lemma upperStarShiftIntegralTateTwistDerivedIso_hom_comp_reduction
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (d : ℕ) (m : ℤ) :
    (derivedUpperStarExtendScalarsIso
          (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv.app
          (((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) ⟦m⟧) ≫
        (purityDerivedCoefficientExtension
          (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) X').map
          (upperStarShiftIntegralTateTwistDerivedIso ℓ E g f d m).hom ≫
        (purityReduceIntegralTateShiftIso ℓ E n (g ≫ f) d m).hom =
      (purityDerivedPullback (Profinite.integersModPowRingObj ℓ E n) g).map
          (purityReduceIntegralTateShiftIso ℓ E n f d m).hom ≫
        (purityFiniteTateShiftPullbackIso ℓ E n g f d m).hom := by
  have h := purity_shift_datum_square
    (purityDerivedPullback (Profinite.padicIntegersRingObj ℓ E) g)
    (purityDerivedCoefficientExtension (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) X')
    (purityDerivedCoefficientExtension (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) X)
    (purityDerivedPullback (Profinite.integersModPowRingObj ℓ E n) g)
    (derivedUpperStarExtendScalarsIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv
    (upperStarIntegralTateTwistDerivedIso ℓ E g f d).hom
    (purityFiniteTateDerivedPullbackIso ℓ E n g f d).hom
    (purityReduceIntegralTateDerivedIso ℓ E n f d).hom
    (purityReduceIntegralTateDerivedIso ℓ E n (g ≫ f) d).hom
    (upperStarIntegralTateTwistDerivedIso_hom_comp_reduction ℓ E n g f d) m
  simp only [upperStarShiftIntegralTateTwistDerivedIso_hom_eq,
    purityReduceIntegralTateShiftIso, purityFiniteTateShiftPullbackIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h ⊢
  dsimp only [purityDerivedCoefficientExtension, purityDerivedPullback,
    purityDerivedCoefficientExtension_commShift, purityDerivedPullback_commShift,
    Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale
