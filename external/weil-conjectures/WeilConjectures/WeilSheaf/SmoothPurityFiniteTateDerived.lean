/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteTatePowers
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateRationalDerived

/-! # The finite reduction of the derived integral Tate datum -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  (n : ℕ) {k : Type u} [Field k] [NeZero (ℓ : k)] {X X' : Scheme.{u}}

/-- The finite Tate power in degree zero, with its geometric pullback datum. -/
noncomputable def purityFiniteTateDerivedPullbackIso
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (d : ℕ) :=
  purityPullbackSingleIso (Profinite.integersModPowRingObj ℓ E n) g
      (purityFiniteTatePower ℓ E n X d) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (purityFiniteTatePowerPullbackIso ℓ E n g f d)

/-- Reduction of an integral Tate power in degree zero. -/
noncomputable def purityReduceIntegralTateDerivedIso (f : X ⟶ Spec (.of k)) (d : ℕ) :=
  purityExtendScalarsFlatSingleIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) X
      (isLocallyFree_integralTateTwistNat ℓ E f d).flat ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (purityReduceIntegralTatePowerIso ℓ E n f d)

/-- The actual nonflat derived reduction preserves the geometric datum of every
nonnegative integral Tate twist. -/
lemma upperStarIntegralTateTwistDerivedIso_hom_comp_reduction
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (d : ℕ) :
    (derivedUpperStarExtendScalarsIso
          (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv.app
          ((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) ≫
        (purityDerivedCoefficientExtension
          (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) X').map
          (upperStarIntegralTateTwistDerivedIso ℓ E g f d).hom ≫
        (purityReduceIntegralTateDerivedIso ℓ E n (g ≫ f) d).hom =
      (purityDerivedPullback (Profinite.integersModPowRingObj ℓ E n) g).map
          (purityReduceIntegralTateDerivedIso ℓ E n f d).hom ≫
        (purityFiniteTateDerivedPullbackIso ℓ E n g f d).hom := by
  have h := purity_derived_flat_datum_square
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g
    (isLocallyFree_integralTateTwistNat ℓ E f d).flat
    (isLocallyFree_integralTateTwistNat ℓ E (g ≫ f) d).flat
    (upperStarIntegralTateTwistNatIso ℓ E g f d).hom
    (purityFiniteTatePowerPullbackIso ℓ E n g f d).hom
    (purityReduceIntegralTatePowerIso ℓ E n f d).hom
    (purityReduceIntegralTatePowerIso ℓ E n (g ≫ f) d).hom
    (upperStarIntegralTateTwistNatIso_hom_comp_reduction ℓ E n g f d)
  simpa only [upperStarIntegralTateTwistDerivedIso, purityReduceIntegralTateDerivedIso,
    purityFiniteTateDerivedPullbackIso, purityPullbackSingleIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h

end AlgebraicGeometry.ProEtale
