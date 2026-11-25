/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreeTowerCoefficientPullbackComp
public import WeilConjectures.WeilSheaf.TateFrobeniusPullbackNaturality

/-! # Composition of the canonical rational Tate pullback -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [NeZero (ℓ : k)]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : Z ⟶ Spec (.of k))

/-- The root-defined rational Tate comparison satisfies the pullback cocycle. -/
lemma purity_upperStarTateTwistOneIso_comp :
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ℓ) f g).hom.app
          (tateTwistOne Z ℓ) ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).map
          (upperStarTateTwistOneIso ℓ g a).hom ≫
        (upperStarTateTwistOneIso ℓ f (g ≫ a)).hom =
      (upperStarTateTwistOneIso ℓ (f ≫ g) a).hom := by
  have h := purity_upperStarExtendScalarsLimitFreeTowerIso_geometric_comp
    (Profinite.continuousMapRingObj ℤ_[ℓ]) f g
    (F := fun n ↦ rootsOfUnitySheaf Z (ℓ ^ n))
    (G := fun n ↦ rootsOfUnitySheaf Y (ℓ ^ n))
    (H := fun n ↦ rootsOfUnitySheaf X (ℓ ^ n))
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf Z) (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow Z (ℓ ^ n) ℓ)
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf Y) (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow Y (ℓ ^ n) ℓ)
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow X (ℓ ^ n) ℓ)
    (fun n ↦ have := NeZero.natCast_pow (R := k) ℓ n
      upperStarRootsOfUnitySheafIsoOfInvertible g a (ℓ ^ n))
    (fun n ↦ have := NeZero.natCast_pow (R := k) ℓ n
      upperStarRootsOfUnitySheafIsoOfInvertible f (g ≫ a) (ℓ ^ n))
    (fun n ↦ have := NeZero.natCast_pow (R := k) ℓ n
      upperStarRootsOfUnitySheafIsoOfInvertible (f ≫ g) a (ℓ ^ n))
    (upperStar_map_rootsOfUnityTransition_comp_upperStarRootsOfUnitySheafHom ℓ g)
    (upperStar_map_rootsOfUnityTransition_comp_upperStarRootsOfUnitySheafHom ℓ f)
    (upperStar_map_rootsOfUnityTransition_comp_upperStarRootsOfUnitySheafHom ℓ (f ≫ g))
    (preservesLimit_upperStar_tateModuleSystem ℓ g a)
    (preservesLimit_upperStar_tateModuleSystem ℓ f (g ≫ a))
    (preservesLimit_upperStar_tateModuleSystem ℓ (f ≫ g) a)
    (Profinite.padicIntRingObjToPadicAlgCl ℓ)
    (fun n ↦ by
      simp only [upperStarRootsOfUnitySheafIsoOfInvertible_hom]
      rw [upperStar_map_upperStarRootsOfUnitySheafHom_comp, Iso.hom_inv_id_app_assoc])
  simp only [upperStarTateTwistOneIso, tateTwistOne, tateModule, tateModuleSystem]
  delta tateModuleTransition
  exact h

end AlgebraicGeometry.ProEtale
