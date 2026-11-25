/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePullbackComp
public import WeilConjectures.WeilSheaf.SmoothPurityScalarComparison
public import WeilConjectures.WeilSheaf.SmoothPurityInverseSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # The canonical Tate and unit data in descent coordinates -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [NeZero (ℓ : k)]

/-- The auxiliary ground-field map only certifies invertibility of the root pullback;
the canonical Tate comparison itself is independent of this choice. -/
lemma purity_upperStarTateTwistOneIso_independent_base
    {k' : Type u} [Field k'] [NeZero (ℓ : k')]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (a : Y ⟶ Spec (.of k))
    (a' : Y ⟶ Spec (.of k')) :
    upperStarTateTwistOneIso ℓ g a = upperStarTateTwistOneIso ℓ g a' := by
  rfl

/-- Transport along an equality of geometric maps preserves the canonical root datum. -/
lemma purity_upperStarTateTwistOneIso_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (a : Y ⟶ Spec (.of k)) :
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj ℓ) h).hom.app
          (tateTwistOne Y ℓ) ≫ (upperStarTateTwistOneIso ℓ g a).hom =
      (upperStarTateTwistOneIso ℓ f a).hom := by
  subst g
  simp [CondensedRing.upperStarCongr]

/-- The canonical Tate datum agrees with the descent datum on a pulled-back Tate line. -/
lemma purity_upperStarTateTwistOneIso_factor
    {X U : Scheme.{u}} (p : U ⟶ X) (s : U ⟶ U) (hs : s ≫ p = p)
    (a : X ⟶ Spec (.of k)) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) s).map
        (upperStarTateTwistOneIso ℓ p a).hom ≫
        (upperStarTateTwistOneIso ℓ s (p ≫ a)).hom =
      (purityModuleFactorIso (Profinite.padicAlgClRingObj ℓ) p s hs).hom.app
          (tateTwistOne X ℓ) ≫ (upperStarTateTwistOneIso ℓ p a).hom := by
  exact purity_factor_component
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) p)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) s)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (s ≫ p))
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ℓ) s p)
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj ℓ) hs)
    (purityModuleFactorIso (Profinite.padicAlgClRingObj ℓ) p s hs) rfl
    (tateTwistOne X ℓ) _ _ _
    (purity_upperStarTateTwistOneIso_comp ℓ s p a)
    (purity_upperStarTateTwistOneIso_congr ℓ hs a)

section Unit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The unit comparison respects equality of the geometric pullback. -/
lemma purity_upperStar_unit_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (CondensedRing.upperStarCongr Λ h).hom.app (𝟙_ _) ≫
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ g)).inv =
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv := by
  subst g
  simp [CondensedRing.upperStarCongr]

/-- The canonical unit comparison carries the descent datum to the unit datum. -/
lemma purity_upperStar_unit_factor {X U : Scheme.{u}}
    (p : U ⟶ X) (s : U ⟶ U) (hs : s ≫ p = p) :
    (CondensedRing.upperStar Λ s).map (Functor.Monoidal.εIso (CondensedRing.upperStar Λ p)).inv ≫
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ s)).inv =
      (purityModuleFactorIso Λ p s hs).hom.app (𝟙_ _) ≫
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ p)).inv := by
  exact purity_factor_component (CondensedRing.upperStar Λ p) (CondensedRing.upperStar Λ s)
    (CondensedRing.upperStar Λ (s ≫ p)) (CondensedRing.upperStarComp Λ s p)
    (CondensedRing.upperStarCongr Λ hs) (purityModuleFactorIso Λ p s hs) rfl (𝟙_ _) _ _ _
    (upperStarComp_hom_app_unit Λ s p) (purity_upperStar_unit_congr Λ hs)

end Unit

end AlgebraicGeometry.ProEtale
