/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDerivedDatumSquare
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateRationalPowers
public import WeilConjectures.SmoothPurity.IntegralTateTwistExtendScalars

/-! # Rationalization of the derived integral Tate datum -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [NeZero (ℓ : k)] {X X' : Scheme.{u}}

/-- The integral Tate pullback datum in degree zero. -/
noncomputable def upperStarIntegralTateTwistDerivedIso
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (d : ℕ) :
    L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj
      ((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X' ℓ E d) :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory _ g).app _ ≪≫
    ((CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E)
      g).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (upperStarIntegralTateTwistNatIso ℓ E g f d)

/-- Rationalization of the integral Tate twist in degree zero, using its flatness. -/
noncomputable def purityExtendScalarsIntegralTateIso (f : X ⟶ Spec (.of k)) (d : ℕ) :
    L(Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X)).obj
      ((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) ≅
      tateTwistDerived X ℓ d :=
  Functor.leftDerivedFunctorSingleFunctorIsoOfFlat _
      (isLocallyFree_integralTateTwistNat ℓ E f d).flat ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (extendScalarsIntegralTateTwistNatIso X ℓ E d)

/-- The actual derived coefficient comparison preserves the integral Tate datum
under rationalization. -/
lemma upperStarIntegralTateTwistDerivedIso_hom_comp_rationalization
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (d : ℕ) :
    (derivedUpperStarExtendScalarsIso (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) g).inv.app
          ((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) ≫
        L(Mod.extendScalars
          (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X')).map
          (upperStarIntegralTateTwistDerivedIso ℓ E g f d).hom ≫
        (purityExtendScalarsIntegralTateIso ℓ E (g ≫ f) d).hom =
      L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          (purityExtendScalarsIntegralTateIso ℓ E f d).hom ≫
        (upperStarTateTwistDerivedIso ℓ g f d).hom := by
  have h := purity_derived_flat_datum_square
    (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) g
    (isLocallyFree_integralTateTwistNat ℓ E f d).flat
    (isLocallyFree_integralTateTwistNat ℓ E (g ≫ f) d).flat
    (upperStarIntegralTateTwistNatIso ℓ E g f d).hom
    (upperStarTateTwistNatIso ℓ g f d).hom
    (extendScalarsIntegralTateTwistNatIso X ℓ E d).hom
    (extendScalarsIntegralTateTwistNatIso X' ℓ E d).hom
    (upperStarIntegralTateTwistNatIso_hom_comp_rationalization ℓ E g f d)
  simpa only [upperStarIntegralTateTwistDerivedIso, purityExtendScalarsIntegralTateIso,
    purityDerivedCoefficientExtension, purityDerivedPullback,
    purityExtendScalarsFlatSingleIso, purityPullbackSingleIso,
    upperStarTateTwistDerivedIso, upperStarTateTwistIso, tateTwistDerived, tateTwist,
    Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc] using h

end AlgebraicGeometry.ProEtale
