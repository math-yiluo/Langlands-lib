/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreeTowerDoubleReduction
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTatePullback
public import WeilConjectures.WeilSheaf.SmoothPurityTateModuleReductionPullback
public import WeilConjectures.TateTwist.IntegralReduction

/-! # The actual integral Tate datum after finite reduction -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  {k : Type u} [Field k] [NeZero (ℓ : k)] {X X' : Scheme.{u}}
  (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (n : ℕ)

/-- The canonical integral Tate pullback datum reduces to the canonical pullback
of finite roots of unity under the actual integral Tate reduction isomorphism. -/
lemma upperStarIntegralTateTwistOneIso_hom_comp_reduction :
    (pullIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv.app
          (integralTateTwistOne X ℓ E) ≫
        (Mod.extendScalars (integersModPowReduction X' ℓ E n)).map
          (upperStarIntegralTateTwistOneIso ℓ E g f).hom ≫
        (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n (g ≫ f)).hom =
      (CondensedRing.upperStar (Profinite.integersModPowRingObj ℓ E n) g).map
          (extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f).hom ≫
        (freeFunctorCompUpperStarIso (Profinite.integersModPowRingObj ℓ E n) g).hom.app
          (rootsOfUnitySheaf X (ℓ ^ n)) ≫
        (Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X')).map
          (purityTateRootPullbackIso ℓ g f n).hom := by
  have h := upperStarExtendScalarsLimitFreeTowerIso_hom_comp_doubleProjection
    (Profinite.continuousMapRingObj ℤ_[ℓ]) g
    (F := fun m ↦ rootsOfUnitySheaf X (ℓ ^ m))
    (F' := fun m ↦ rootsOfUnitySheaf X' (ℓ ^ m))
    (fun m ↦ eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' ℓ m)) ≫
      rootsOfUnitySheafPow X (ℓ ^ m) ℓ)
    (fun m ↦ eqToHom (congrArg (rootsOfUnitySheaf X') (pow_succ' ℓ m)) ≫
      rootsOfUnitySheafPow X' (ℓ ^ m) ℓ)
    (fun m ↦ have := NeZero.natCast_pow (R := k) ℓ m
      upperStarRootsOfUnitySheafIsoOfInvertible g f (ℓ ^ m))
    (upperStar_map_rootsOfUnityTransition_comp_upperStarRootsOfUnitySheafHom ℓ g)
    (preservesLimit_upperStar_tateModuleSystem ℓ g f)
    (Profinite.padicIntRingObjToPadicIntegers ℓ E)
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n)
    (Profinite.padicIntRingObjToIntegersModPow ℓ E n) rfl n
  simp only [upperStarIntegralTateTwistOneIso, integralTateTwistOne, tateModule,
    tateModuleSystem,
    integersModPowReduction, purityTateRootPullbackIso,
    extendScalarsIntegralTateTwistOneIntegersModPowIso,
    extendScalarsTateModuleIso, purityFreeTowerProjection, upperStarFreeTowerIsoApp,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom,
    Functor.map_comp, Category.assoc] at h ⊢
  delta tateModuleTransition
  exact h

end AlgebraicGeometry.ProEtale
