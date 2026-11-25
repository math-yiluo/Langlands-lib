/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Compactification.RefinementPullback
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.Defs

/-!

# The identity law for the comparison of derived lower shrieks

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison_id`: the
  comparison attached to the identity refinement of a compactification is the identity.

See `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison` for the implementation
notes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

section IdentityLaw

variable (c)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The composition isomorphism of pushforwards attached to the identity refinement cancels
the identity isomorphism `AlgebraicGeometry.Etale.lowerStarId`. -/
lemma refinementLowerStarComp_id :
    Functor.whiskerRight (Etale.lowerStarId A c.Z).inv ((c.g)_*[A]) ≫
        (refinementLowerStarComp A (Compactification.Refinement.id c)).hom =
      𝟙 ((c.g)_*[A]) := by
  have hgen : ∀ {W W' : Scheme.{u}} (h₁ : c.Z ⟶ W) (h₂ : W ⟶ W') (h₁₂ : c.Z ⟶ W')
      (hh₁₂ : h₁₂ = h₁ ≫ h₂),
      Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂ ≪≫
          eqToIso (congrArg (fun g => (g)_*[A]) hh₁₂) = Etale.lowerStarComp A h₁ h₂ := by
    intro W W' h₁ h₂ h₁₂ hh₁₂
    subst hh₁₂
    simp
  have hr : refinementLowerStarComp A (Compactification.Refinement.id c) =
      Etale.lowerStarComp A (𝟙 c.Z) c.g ≪≫
        eqToIso (congrArg (fun g => (g)_*[A]) (Category.id_comp c.g)) := rfl
  rw [hr, ← hgen (𝟙 c.Z) c.g c.g (Category.id_comp c.g).symm, Etale.lowerStarComp_id_left]
  ext G
  simp

/-- **The identity refinement has trivial base change**: the inverse of the base change
isomorphism attached to `Compactification.Refinement.id c` is the whiskering of the identity
isomorphism `AlgebraicGeometry.Etale.upperStarIdDerivedPlus`. -/
lemma refinementLowerShriekBaseChangeDerivedPlusIso_inv_id
    (hcart : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i) :
    (refinementLowerShriekBaseChangeDerivedPlusIso A
        (Compactification.Refinement.id c) hcart).inv =
      Functor.whiskerLeft ((c.i)_!open[A].mapDerivedCategoryPlus)
        (upperStarIdDerivedPlus A c.Z).hom := by
  rw [← cancel_epi (refinementLowerShriekBaseChangeDerivedPlusIso A
    (Compactification.Refinement.id c) hcart).hom, Iso.hom_inv_id]
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso _) (fun K => ?_)
  have hbc : (refinementLowerShriekBaseChangeDerivedPlusIso A
        (Compactification.Refinement.id c) hcart).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
      ((𝟙 c.Z)^*[A]).mapDerivedCategoryPlus.map
        (((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      ((𝟙 c.Z)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K) =
      ((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          ((Compactification.Refinement.id c).openImmersionLowerShriekBaseChange A)).app K) :=
    refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh A
      (Compactification.Refinement.id c) hcart K
  simp only [NatTrans.id_app, NatTrans.comp_app, Functor.whiskerLeft_app]
  symm
  rw [← cancel_mono (((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K),
    Category.assoc, Category.id_comp]
  have hnat := ((upperStarIdDerivedPlus A c.Z).hom.naturality
    (((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K))
  simp only [Functor.id_map, Functor.comp_obj] at hnat
  rw [← hnat, upperStarIdDerivedPlus_hom_app, reassoc_of% hbc]
  have hbcid : (Compactification.Refinement.id c).openImmersionLowerShriekBaseChange A =
      Functor.whiskerLeft (c.i)_!open[A] (Etale.upperStarId A c.Z).inv := by
    rw [Compactification.Refinement.openImmersionLowerShriekBaseChange_id]
    ext S
    simp
  have hbridge : (NatTrans.mapHomotopyCategoryPlus
        (Functor.whiskerLeft (c.i)_!open[A] (Etale.upperStarId A c.Z).inv)).app K =
      (NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A c.Z).inv).app
        (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K) := rfl
  have hcancel : (NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A c.Z).inv).app
        (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K) ≫
      (NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A c.Z).hom).app
        (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id,
      NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app]
  have hid : DerivedCategory.Plus.Qh.map (𝟙 ((𝟭 (Sheaf c.Z.smallEtaleTopology A)
        ).mapHomotopyCategoryPlus.obj (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K))) =
      𝟙 (DerivedCategory.Plus.Qh.obj ((𝟭 (Sheaf c.Z.smallEtaleTopology A)
        ).mapHomotopyCategoryPlus.obj (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K))) :=
    DerivedCategory.Plus.Qh.map_id _
  rw [hbcid, hbridge, ← DerivedCategory.Plus.Qh.map_comp, hcancel, hid]
  exact Category.comp_id _

/-- **The identity law for the comparison of derived lower shrieks**: the comparison
`Rf_!(c)[A]+ ⟶ Rf_!(c)[A]+` attached to the identity refinement of a compactification `c`
is the identity. (blueprint: `BA43-RHO`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusComparison_id
    (hcart : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i) :
    rightDerivedLowerShriekOfCompactificationPlusComparison A
      (Compactification.Refinement.id c) hcart = 𝟙 (Rf_!(c)[A]+) := by
  have : (((𝟙 c.Z)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A (𝟙 c.Z))
  have : (((Compactification.Refinement.id c).hom)_*[A]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A (Compactification.Refinement.id c).hom)
  ext W : 2
  have hB := NatTrans.congr_app (derivedPlus_unit_comp_upperStarIdDerivedPlus A c.Z)
    (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)
  have hC := NatTrans.congr_app
    (lowerStarIdDerivedPlus_inv_comp_rightDerivedFunctorPlusCompIso' A c.g
      (refinementLowerStarComp A (Compactification.Refinement.id c))
      (refinementLowerStarComp_id A c))
    (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)
  have hBC := NatTrans.congr_app
    (refinementLowerShriekBaseChangeDerivedPlusIso_inv_id A c hcart) W
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hB hC ⊢
  have hB' : (Etale.upperStarLowerStarAdjunction A
        (Compactification.Refinement.id c).hom).derivedPlus.unit.app
        (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
      (((Compactification.Refinement.id c).hom)_*[A]).rightDerivedFunctorPlus.map
        ((upperStarIdDerivedPlus A c.Z).hom.app
          (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)) =
      (lowerStarIdDerivedPlus A c.Z).inv.app
        (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W) := hB
  have hC' : ((c.g)_*[A]).rightDerivedFunctorPlus.map
        ((lowerStarIdDerivedPlus A c.Z).inv.app
          (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)) ≫
      (Functor.rightDerivedFunctorPlusCompIso' (((Compactification.Refinement.id c).hom)_*[A])
          ((c.g)_*[A])
          (refinementLowerStarComp A (Compactification.Refinement.id c))).hom.app
        (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W) =
      𝟙 (((c.g)_*[A]).rightDerivedFunctorPlus.obj
        (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)) := hC
  simp only [rightDerivedLowerShriekOfCompactificationPlusComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map]
  rw [hBC, Functor.whiskerLeft_app, ← Functor.map_comp_assoc, hB', hC']
  rfl

end IdentityLaw

end Etale

end AlgebraicGeometry
