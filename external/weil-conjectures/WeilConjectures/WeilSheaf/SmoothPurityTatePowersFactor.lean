/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePowersComposition
public import WeilConjectures.WeilSheaf.SmoothPurityTatePullbackFactor

/-! # The canonical Tate powers in descent coordinates -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [NeZero (ℓ : k)]

/-- The auxiliary ground-field map does not affect the canonical Tate power datum. -/
lemma purity_upperStarTateTwistNatIso_independent_base
    {k' : Type u} [Field k'] [NeZero (ℓ : k')]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (a : Y ⟶ Spec (.of k))
    (a' : Y ⟶ Spec (.of k')) (d : ℕ) :
    upperStarTateTwistNatIso ℓ g a d = upperStarTateTwistNatIso ℓ g a' d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [upperStarTateTwistNatIso, ih,
        purity_upperStarTateTwistOneIso_independent_base ℓ g a a']

/-- Equality of geometric maps preserves the canonical Tate power comparison. -/
lemma purity_upperStarTateTwistNatIso_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (a : Y ⟶ Spec (.of k)) (d : ℕ) :
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj ℓ) h).hom.app
          (tateTwistNat Y ℓ d) ≫ (upperStarTateTwistNatIso ℓ g a d).hom =
      (upperStarTateTwistNatIso ℓ f a d).hom := by
  subst g
  simp [CondensedRing.upperStarCongr]

/-- The root-defined Tate power datum agrees with the datum from the finite-base model. -/
lemma purity_upperStarTateTwistNatIso_factor
    {X U : Scheme.{u}} (p : U ⟶ X) (s : U ⟶ U) (hs : s ≫ p = p)
    (a : X ⟶ Spec (.of k)) (d : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) s).map
          (upperStarTateTwistNatIso ℓ p a d).hom ≫
        (upperStarTateTwistNatIso ℓ s (p ≫ a) d).hom =
      (purityModuleFactorIso (Profinite.padicAlgClRingObj ℓ) p s hs).hom.app
          (tateTwistNat X ℓ d) ≫ (upperStarTateTwistNatIso ℓ p a d).hom := by
  exact purity_factor_component
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) p)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) s)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (s ≫ p))
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ℓ) s p)
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj ℓ) hs)
    (purityModuleFactorIso (Profinite.padicAlgClRingObj ℓ) p s hs) rfl
    (tateTwistNat X ℓ d) _ _ _
    (purity_upperStarTateTwistNatIso_comp ℓ s p a d)
    (purity_upperStarTateTwistNatIso_congr ℓ hs a d)

end AlgebraicGeometry.ProEtale
