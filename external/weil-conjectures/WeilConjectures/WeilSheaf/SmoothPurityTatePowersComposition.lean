/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePullbackComp
public import WeilConjectures.WeilSheaf.SmoothPurityTensorComposition
public import WeilConjectures.TateTwist.Pullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # Composition of the canonical Tate pullback in every nonnegative degree -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [NeZero (ℓ : k)]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : Z ⟶ Spec (.of k))

/-- The tensor-power Tate comparison satisfies the pullback cocycle. -/
lemma purity_upperStarTateTwistNatIso_comp (d : ℕ) :
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ℓ) f g).hom.app
          (tateTwistNat Z ℓ d) ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).map
          (upperStarTateTwistNatIso ℓ g a d).hom ≫
        (upperStarTateTwistNatIso ℓ f (g ≫ a) d).hom =
      (upperStarTateTwistNatIso ℓ (f ≫ g) a d).hom := by
  induction d with
  | zero => exact upperStarComp_hom_app_unit (Profinite.padicAlgClRingObj ℓ) f g
  | succ d ih =>
      exact purity_tensor_composition
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g)
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f)
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (f ≫ g))
        (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ℓ) f g).hom
        (upperStarTateTwistNatIso ℓ g a d).hom (upperStarTateTwistOneIso ℓ g a).hom
        (upperStarTateTwistNatIso ℓ f (g ≫ a) d).hom
        (upperStarTateTwistOneIso ℓ f (g ≫ a)).hom
        (upperStarTateTwistNatIso ℓ (f ≫ g) a d).hom
        (upperStarTateTwistOneIso ℓ (f ≫ g) a).hom
        (upperStarComp_hom_app_tensor_δ (Profinite.padicAlgClRingObj ℓ) f g
          (tateTwistNat Z ℓ d) (tateTwistOne Z ℓ)).symm
        ih (purity_upperStarTateTwistOneIso_comp ℓ f g a)

end AlgebraicGeometry.ProEtale
