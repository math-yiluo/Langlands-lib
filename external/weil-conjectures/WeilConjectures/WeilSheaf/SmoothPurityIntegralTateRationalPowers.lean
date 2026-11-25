/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateRationalPullback
public import WeilConjectures.WeilSheaf.SmoothPurityTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal

/-! # Rationalization of the geometric datum on nonnegative Tate powers -/

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

/-- Rationalizing any nonnegative integral Tate twist preserves its geometric
pullback datum. -/
lemma upperStarIntegralTateTwistNatIso_hom_comp_rationalization (d : ℕ) :
    (pullIso (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) g).inv.app
          (integralTateTwistNat X ℓ E d) ≫
        (Mod.extendScalars (coefficientMap (Profinite.padicIntegersRingObjToPadicAlgCl ℓ E) X')).map
          (upperStarIntegralTateTwistNatIso ℓ E g f d).hom ≫
        (extendScalarsIntegralTateTwistNatIso X' ℓ E d).hom =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).map
          (extendScalarsIntegralTateTwistNatIso X ℓ E d).hom ≫
        (upperStarTateTwistNatIso ℓ g f d).hom := by
  let a := Profinite.padicIntegersRingObjToPadicAlgCl ℓ E
  let := Mod.extendScalarsMonoidal (coefficientMap a X)
  let := Mod.extendScalarsMonoidal (coefficientMap a X')
  have : NatTrans.IsMonoidal (pullIso a g).hom := isMonoidal_pullIso_hom a g
  induction d with
  | zero =>
      exact purity_unit_comparison
        (CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E) g)
        (Mod.extendScalars (coefficientMap a X'))
        (Mod.extendScalars (coefficientMap a X))
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g) (pullIso a g).inv
  | succ d ih =>
      exact purity_tensor_comparison
        (CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E) g)
        (Mod.extendScalars (coefficientMap a X'))
        (Mod.extendScalars (coefficientMap a X))
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g) (pullIso a g).inv
        (upperStarIntegralTateTwistNatIso ℓ E g f d).hom
        (upperStarIntegralTateTwistOneIso ℓ E g f).hom
        (extendScalarsIntegralTateTwistNatIso X ℓ E d).hom
        (extendScalarsIntegralTateTwistOneIso X ℓ E).hom
        (upperStarTateTwistNatIso ℓ g f d).hom (upperStarTateTwistOneIso ℓ g f).hom
        (extendScalarsIntegralTateTwistNatIso X' ℓ E d).hom
        (extendScalarsIntegralTateTwistOneIso X' ℓ E).hom ih
        (upperStarIntegralTateTwistOneIso_hom_comp_rationalization ℓ E g f)

end AlgebraicGeometry.ProEtale
