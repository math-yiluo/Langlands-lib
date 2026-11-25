/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.TateTwist.IntegralLocallyFree
public import WeilConjectures.TateTwist.Pullback

/-! # The geometric pullback datum on integral Tate twists -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  {k : Type u} [Field k] [NeZero (ℓ : k)] {X X' : Scheme.{u}}
  (g : X' ⟶ X) (f : X ⟶ Spec (.of k))

/-- Pullback of the integral Tate line, using the canonical root-of-unity comparisons
at every level of its defining tower. -/
noncomputable def upperStarIntegralTateTwistOneIso :
    (CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E) g).obj
      (integralTateTwistOne X ℓ E) ≅ integralTateTwistOne X' ℓ E :=
  upperStarExtendScalarsLimitFreeTowerIso (Profinite.continuousMapRingObj ℤ_[ℓ]) g
    (F := fun n ↦ rootsOfUnitySheaf X (ℓ ^ n))
    (F' := fun n ↦ rootsOfUnitySheaf X' (ℓ ^ n))
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf X) (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow X (ℓ ^ n) ℓ)
    (fun n ↦ eqToHom (congrArg (rootsOfUnitySheaf X') (pow_succ' ℓ n)) ≫
      rootsOfUnitySheafPow X' (ℓ ^ n) ℓ)
    (fun n ↦ have := NeZero.natCast_pow (R := k) ℓ n
      upperStarRootsOfUnitySheafIsoOfInvertible g f (ℓ ^ n))
    (Profinite.padicIntRingObjToPadicIntegers ℓ E)
    (upperStar_map_rootsOfUnityTransition_comp_upperStarRootsOfUnitySheafHom ℓ g)
    (preservesLimit_upperStar_tateModuleSystem ℓ g f)

/-- The integral Tate comparison for every nonnegative twist. -/
noncomputable def upperStarIntegralTateTwistNatIso :
    (d : ℕ) → (CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E) g).obj
      (integralTateTwistNat X ℓ E d) ≅ integralTateTwistNat X' ℓ E d
  | 0 => (Functor.Monoidal.εIso _).symm
  | d + 1 => (Functor.Monoidal.μIso _ _ _).symm ≪≫
      (upperStarIntegralTateTwistNatIso d ⊗ᵢ upperStarIntegralTateTwistOneIso ℓ E g f)

/-- The same integral comparison in the derived category, including the purity shift. -/
noncomputable def upperStarShiftIntegralTateTwistDerivedIso (d : ℕ) (n : ℤ) :
    L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj
      (((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) ⟦n⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X' ℓ E d)) ⟦n⟧ :=
  (L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).commShiftIso n).app _ ≪≫
    (shiftFunctor _ n).mapIso
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory _ g).app _ ≪≫
        ((CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E)
          g).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (upperStarIntegralTateTwistNatIso ℓ E g f d))

end AlgebraicGeometry.ProEtale
