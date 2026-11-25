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

# The composition law for the comparison of derived lower shrieks

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison_comp`:
  the comparison attached to a composite `r.comp s` of refinements is the composite of the
  two comparisons, in the reverse order.

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

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

section CompositionLaw

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The composition isomorphism of pushforwards attached to a refinement is the composition
isomorphism `AlgebraicGeometry.Etale.lowerStarComp` at the structure morphism of the
finer compactification. -/
lemma refinementLowerStarComp_eq {c d : Compactification f} (r : c.Refinement d) :
    refinementLowerStarComp A r = Etale.lowerStarComp A r.hom d.g c.g r.hom_g.symm := by
  have h : refinementLowerStarComp A r =
      Etale.lowerStarComp A r.hom d.g ≪≫
        eqToIso (congrArg (fun g => (g)_*[A]) r.hom_g) := rfl
  rw [h, Etale.lowerStarComp_trans_eqToIso A r.hom d.g c.g r.hom_g]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- **Cocycle law for the composition isomorphism of pushforwards along a refinement**. -/
lemma refinementLowerStarComp_comp {c d e : Compactification f}
    (r : c.Refinement d) (s : d.Refinement e) :
    Functor.whiskerRight
          (Etale.lowerStarComp A r.hom s.hom ((r.comp s).hom) rfl).hom ((e.g)_*[A]) ≫
        (refinementLowerStarComp A (r.comp s)).hom =
      Functor.whiskerLeft ((r.hom)_*[A]) (refinementLowerStarComp A s).hom ≫
        (refinementLowerStarComp A r).hom := by
  rw [Etale.refinementLowerStarComp_eq, Etale.refinementLowerStarComp_eq,
    Etale.refinementLowerStarComp_eq]
  exact Etale.lowerStarComp_assoc' A r.hom s.hom e.g ((r.comp s).hom) d.g c.g rfl
    s.hom_g.symm ((r.comp s).hom_g).symm

/-- **Cocycle law for the base change isomorphism on the bounded below derived
categories**. -/
lemma refinementLowerShriekBaseChangeDerivedPlusIso_hom_comp
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A (r.comp s)
          (Compactification.Refinement.isPullback_comp r s hr hs)).hom ≫
        Functor.whiskerLeft ((e.i)_!open[A]).mapDerivedCategoryPlus
          (Etale.upperStarCompDerivedPlus A r.hom s.hom ((r.comp s).hom) rfl).hom =
      (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).hom ≫
        Functor.whiskerRight
          (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).hom
          (((r.hom)^*[A]).mapDerivedCategoryPlus) := by
  have hcocycle : (r.comp s).openImmersionLowerShriekBaseChange A ≫
      Functor.whiskerLeft ((e.i)_!open[A])
        (Etale.upperStarComp A r.hom s.hom ((r.comp s).hom) rfl).hom =
      r.openImmersionLowerShriekBaseChange A ≫
        Functor.whiskerRight (s.openImmersionLowerShriekBaseChange A)
          ((r.hom)^*[A]) := by
    have h : (r.comp s).openImmersionLowerShriekBaseChange A =
        r.openImmersionLowerShriekBaseChange A ≫
          Functor.whiskerRight (s.openImmersionLowerShriekBaseChange A) ((r.hom)^*[A]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft ((e.i)_!open[A])
            (Etale.upperStarComp A r.hom s.hom ((r.comp s).hom) rfl).inv :=
      Compactification.Refinement.openImmersionLowerShriekBaseChange_comp A r s
    rw [h]
    ext W
    simp
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso _) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← cancel_mono (((r.hom)^*[A]).mapDerivedCategoryPlus.map
      (((s.hom)^*[A]).mapDerivedCategoryPlus.map
        (((e.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
    ((r.hom)^*[A]).mapDerivedCategoryPlus.map
      (((s.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((e.i)_!open[A]).mapHomotopyCategoryPlus.obj K)) ≫
    ((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
      (((s.hom)^*[A]).mapHomotopyCategoryPlus.obj
        (((e.i)_!open[A]).mapHomotopyCategoryPlus.obj K)))]
  simp only [Category.assoc]
  have hnatPhi := (Etale.upperStarCompDerivedPlus A r.hom s.hom ((r.comp s).hom)
      rfl).hom.naturality (((e.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatPhi
  have hBs := congrArg (((r.hom)^*[A]).mapDerivedCategoryPlus.map)
    (Etale.refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh A s hs K)
  simp only [Functor.map_comp] at hBs
  have hnatF1 : ((r.hom)^*[A]).mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus
          (s.openImmersionLowerShriekBaseChange A)).app K)) ≫
      ((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((s.hom)^*[A]).mapHomotopyCategoryPlus.obj
          (((e.i)_!open[A]).mapHomotopyCategoryPlus.obj K)) =
      ((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((d.i)_!open[A]).mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map (((r.hom)^*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus
            (s.openImmersionLowerShriekBaseChange A)).app K)) :=
    ((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.naturality _
  have hbrL : (NatTrans.mapHomotopyCategoryPlus
        (Etale.upperStarComp A r.hom s.hom ((r.comp s).hom) rfl).hom).app
        (((e.i)_!open[A]).mapHomotopyCategoryPlus.obj K) =
      (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft ((e.i)_!open[A])
        (Etale.upperStarComp A r.hom s.hom ((r.comp s).hom) rfl).hom)).app K := rfl
  have hbrR : ((r.hom)^*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus
          (s.openImmersionLowerShriekBaseChange A)).app K) =
      (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight
        (s.openImmersionLowerShriekBaseChange A) ((r.hom)^*[A]))).app K := rfl
  trans ((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
      (r.openImmersionLowerShriekBaseChange A ≫ Functor.whiskerRight
        (s.openImmersionLowerShriekBaseChange A) ((r.hom)^*[A]))).app K)
  · rw [← reassoc_of% hnatPhi, Etale.upperStarCompDerivedPlus_hom_app_factorsh A r.hom
        s.hom ((r.comp s).hom) rfl (((e.i)_!open[A]).mapHomotopyCategoryPlus.obj K),
      Etale.refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh_assoc,
      hbrL, ← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategoryPlus_comp, hcocycle]
  · rw [reassoc_of% hBs, hnatF1,
      Etale.refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh_assoc,
      hbrR, ← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategoryPlus_comp]

/-- The inverse form of
`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso_hom_comp`. -/
lemma refinementLowerShriekBaseChangeDerivedPlusIso_inv_comp
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A (r.comp s)
          (Compactification.Refinement.isPullback_comp r s hr hs)).inv =
      Functor.whiskerLeft ((e.i)_!open[A]).mapDerivedCategoryPlus
          (Etale.upperStarCompDerivedPlus A r.hom s.hom ((r.comp s).hom) rfl).hom ≫
        Functor.whiskerRight
            (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv
            (((r.hom)^*[A]).mapDerivedCategoryPlus) ≫
          (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv := by
  rw [← cancel_epi (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A (r.comp s)
      (Compactification.Refinement.isPullback_comp r s hr hs)).hom, Iso.hom_inv_id,
    ← Category.assoc,
    Etale.refinementLowerShriekBaseChangeDerivedPlusIso_hom_comp A r s hr hs]
  have h1 : Functor.whiskerRight
        (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).hom
        (((r.hom)^*[A]).mapDerivedCategoryPlus) ≫
      Functor.whiskerRight
        (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv
        (((r.hom)^*[A]).mapDerivedCategoryPlus) = 𝟙 _ :=
    (Functor.isoWhiskerRight
      (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs)
      (((r.hom)^*[A]).mapDerivedCategoryPlus)).hom_inv_id
  rw [Category.assoc, reassoc_of% h1, Iso.hom_inv_id]

/-- **The composition law for the comparison of derived lower shrieks**: the comparison
attached to a composite `r.comp s` of refinements is the composite of the two comparisons.
Note that, the comparison running from the coarser to the finer compactification, the order
of the composite is reversed. (blueprint: `BA43-RHO`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusComparison_comp
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    Etale.rightDerivedLowerShriekOfCompactificationPlusComparison A (r.comp s)
        (Compactification.Refinement.isPullback_comp r s hr hs) =
      Etale.rightDerivedLowerShriekOfCompactificationPlusComparison A s hs ≫
        Etale.rightDerivedLowerShriekOfCompactificationPlusComparison A r hr := by
  have hI1 : (((r.hom)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A r.hom)
  have hI2 : (((s.hom)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A s.hom)
  have hI : ((((r.comp s).hom)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A (r.comp s).hom)
  ext W : 2
  have hBCinv := NatTrans.congr_app
    (Etale.refinementLowerShriekBaseChangeDerivedPlusIso_inv_comp A r s hr hs) W
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hBCinv
  have hstep2 := Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus A r.hom s.hom
    ((r.comp s).hom) rfl (((e.i)_!open[A]).mapDerivedCategoryPlus.obj W)
  have hstep3 := NatTrans.congr_app
    (Functor.rightDerivedFunctorPlusCompIso'_assoc ((r.hom)_*[A]) ((s.hom)_*[A])
      ((e.g)_*[A]) (((r.comp s).hom)_*[A]) ((d.g)_*[A]) ((c.g)_*[A])
      (Etale.lowerStarComp A r.hom s.hom ((r.comp s).hom) rfl)
      (refinementLowerStarComp A s) (refinementLowerStarComp A (r.comp s))
      (refinementLowerStarComp A r) (Etale.refinementLowerStarComp_comp A r s))
    (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hstep3
  have hnatXi := (Functor.rightDerivedFunctorPlusCompIso' ((r.hom)_*[A]) ((s.hom)_*[A])
      (Etale.lowerStarComp A r.hom s.hom ((r.comp s).hom) rfl)).hom.naturality
    (((r.hom)^*[A]).mapDerivedCategoryPlus.map
        ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W) ≫
      (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatXi
  have hnatEta1 := (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.naturality
    ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hnatEta1
  have hnatTs := (Functor.rightDerivedFunctorPlusCompIso' ((s.hom)_*[A]) ((e.g)_*[A])
      (refinementLowerStarComp A s)).hom.naturality
    ((Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.app
        (((d.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
      ((r.hom)_*[A]).rightDerivedFunctorPlus.map
        ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W))
  simp only [Functor.comp_obj, Functor.comp_map] at hnatTs
  have hinner : (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.app
        (((s.hom)^*[A]).mapDerivedCategoryPlus.obj
          (((e.i)_!open[A]).mapDerivedCategoryPlus.obj W)) ≫
      ((r.hom)_*[A]).rightDerivedFunctorPlus.map
        (((r.hom)^*[A]).mapDerivedCategoryPlus.map
            ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W) ≫
          (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W) =
      (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W ≫
        (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.app
          (((d.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
        ((r.hom)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W) := by
    rw [Functor.map_comp, ← reassoc_of% hnatEta1]
  have hcore : (Etale.upperStarLowerStarAdjunction A (r.comp s).hom).derivedPlus.unit.app
        (((e.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
      ((((r.comp s).hom)_*[A])).rightDerivedFunctorPlus.map
        ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A (r.comp s)
          (Compactification.Refinement.isPullback_comp r s hr hs)).inv.app W) =
      (Etale.upperStarLowerStarAdjunction A s.hom).derivedPlus.unit.app
          (((e.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
        ((s.hom)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W) ≫
        ((s.hom)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.app
              (((d.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
            ((r.hom)_*[A]).rightDerivedFunctorPlus.map
              ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W)) ≫
        (Functor.rightDerivedFunctorPlusCompIso' ((r.hom)_*[A]) ((s.hom)_*[A])
            (Etale.lowerStarComp A r.hom s.hom ((r.comp s).hom) rfl)).hom.app
          (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W) := by
    rw [hBCinv, Functor.map_comp, ← Category.assoc, hstep2, Category.assoc, Category.assoc,
      ← hnatXi, ← Functor.map_comp_assoc, hinner, Functor.map_comp, Category.assoc]
  simp only [Etale.rightDerivedLowerShriekOfCompactificationPlusComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map]
  rw [← Functor.map_comp_assoc, hcore, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hstep3]
  conv_rhs =>
    rw [← Functor.map_comp_assoc (((d.g)_*[A]).rightDerivedFunctorPlus),
      ← reassoc_of% hnatTs]

end CompositionLaw

end Etale

end AlgebraicGeometry
