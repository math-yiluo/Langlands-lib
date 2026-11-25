/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreeTowerCoefficientComposition
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTatePullback

/-! # Rationalization of the actual integral Tate pullback datum -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [NeZero (ℓ : k)] {X X' : Scheme.{u}}
  (g : X' ⟶ X) (f : X ⟶ Spec (.of k))

/-- The integral-to-rational Tate comparison intertwines the canonical geometric
pullback data. -/
lemma upperStarIntegralTateTwistOneIso_hom_comp_rationalization :
    (pullIso (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) g).inv.app
          (integralTateTwistOne X ℓ E) ≫
        (Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X')).map
          (upperStarIntegralTateTwistOneIso ℓ E g f).hom ≫
        (extendScalarsIntegralTateTwistOneIso X' ℓ E).hom =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).map
          (extendScalarsIntegralTateTwistOneIso X ℓ E).hom ≫
        (upperStarTateTwistOneIso ℓ g f).hom := by
  have h := upperStarExtendScalarsLimitFreeTowerIso_comp
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
    (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E)
    (Profinite.padicIntRingObjToPadicAlgCl ℓ)
    (Profinite.padicIntRingObjToPadicIntegers_comp_padicIntegersRingObjToPadicAlgCl ℓ E)
  simp only [extendScalarsIntegralTateTwistOneIso, upperStarIntegralTateTwistOneIso,
    integralTateTwistOne,
    upperStarTateTwistOneIso, tateModule, tateModuleSystem, Iso.app_hom] at h ⊢
  delta tateModuleTransition
  exact h

end AlgebraicGeometry.ProEtale
