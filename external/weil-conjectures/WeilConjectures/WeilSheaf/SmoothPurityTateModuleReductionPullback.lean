/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreeTowerReduction
public import WeilConjectures.TateTwist.TateModuleReduction

/-! # The finite reduction of the canonical Tate pullback datum -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [NeZero (ℓ : k)]
  {X X' : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Spec (.of k))
  {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  (a : Profinite.continuousMapRingObj.{u} ℤ_[ℓ] ⟶ Λ) [IsMonHom a]

/-- The canonical root pullback comparison, with invertibility of `ℓⁿ` inferred from
invertibility of `ℓ` in the ground field. -/
noncomputable def purityTateRootPullbackIso (n : ℕ) :
    (g)^*[Ab.{u + 1}].obj (rootsOfUnitySheaf X (ℓ ^ n)) ≅
      rootsOfUnitySheaf X' (ℓ ^ n) :=
  have := NeZero.natCast_pow (R := k) ℓ n
  upperStarRootsOfUnitySheafIsoOfInvertible g f (ℓ ^ n)

/-- The canonical Tate pullback comparison after extension to any condensed coefficient
ring, including the integral rings and their finite quotients. -/
noncomputable def purityCoefficientTatePullbackIso :
    (CondensedRing.upperStar Λ g).obj
        ((Mod.extendScalars (coefficientMap a X)).obj (tateModule X ℓ)) ≅
      (Mod.extendScalars (coefficientMap a X')).obj (tateModule X' ℓ) :=
  upperStarExtendScalarsLimitFreeTowerIso (Profinite.continuousMapRingObj ℤ_[ℓ]) g
    (F := fun n ↦ rootsOfUnitySheaf X (ℓ ^ n))
    (F' := fun n ↦ rootsOfUnitySheaf X' (ℓ ^ n))
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow X (ℓ ^ n) ℓ)
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf X') (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow X' (ℓ ^ n) ℓ)
    (fun n ↦ have := NeZero.natCast_pow (R := k) ℓ n
      upperStarRootsOfUnitySheafIsoOfInvertible g f (ℓ ^ n)) a
    (upperStar_map_rootsOfUnityTransition_comp_upperStarRootsOfUnitySheafHom ℓ g)
    (preservesLimit_upperStar_tateModuleSystem ℓ g f)

/-- For coefficients killed by `ℓⁿ`, the Tate-module reduction intertwines its canonical
geometric pullback with pullback of the finite roots of unity. -/
lemma purityCoefficientTatePullbackIso_hom_comp_reduction
    (n : ℕ) (hΛ : ((ℓ ^ n : ℕ) : ℤ) • 𝟙 Λ = 0) :
    (purityCoefficientTatePullbackIso ℓ g f a).hom ≫
        (extendScalarsTateModuleIso (g ≫ f) ℓ a n hΛ).hom =
      (CondensedRing.upperStar Λ g).map (extendScalarsTateModuleIso f ℓ a n hΛ).hom ≫
        (CondensedRing.freeFunctorCompUpperStarIso Λ g).hom.app
          (rootsOfUnitySheaf X (ℓ ^ n)) ≫
        (Mod.freeFunctor (condensedRingObj Λ X')).map
          (purityTateRootPullbackIso ℓ g f n).hom := by
  exact upperStarExtendScalarsLimitFreeTowerIso_hom_comp_projection
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
    (preservesLimit_upperStar_tateModuleSystem ℓ g f) a n

end AlgebraicGeometry.ProEtale
