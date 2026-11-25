/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExchangeMono
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import all Mathlib.Algebra.Homology.CochainComplexPlus
import all Mathlib.Data.Int.Interval
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import all WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import all Mathlib.Algebra.Homology.TotalComplex
import all Mathlib.CategoryTheory.Abelian.Basic
import all WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import all WeilConjectures.CategoryTheory.Triangulated.Recollement
import all Mathlib.Algebra.Category.Grp.Zero
import all Mathlib.Algebra.Category.Ring.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import all Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.AlgebraicGeometry.Pullbacks
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.CategoryTheory.Adjunction.Triple
import all Mathlib.CategoryTheory.EffectiveEpi.Comp
import all Mathlib.CategoryTheory.Extensive
import all Mathlib.CategoryTheory.GradedObject.Bifunctor
import all Mathlib.CategoryTheory.GradedObject.Monoidal
import all Mathlib.CategoryTheory.GradedObject.Trifunctor
import all Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import all Mathlib.CategoryTheory.Limits.Preserves.Filtered
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import all Mathlib.CategoryTheory.Monad.Adjunction
import all Mathlib.CategoryTheory.Monoidal.Action.Basic
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.CommMon_
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all Mathlib.CategoryTheory.Monoidal.Mod
import all Mathlib.CategoryTheory.Monoidal.Mon
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.CategoryTheory.Sites.Coherent.Basic
import all Mathlib.CategoryTheory.Sites.Coherent.Comparison
import all Mathlib.CategoryTheory.Sites.ConcreteSheafification
import all Mathlib.CategoryTheory.Sites.Grothendieck
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.Combinatorics.Quiver.ReflQuiver
import all Mathlib.Order.Int.ConditionallyCompleteOrder
import all Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import all Mathlib.Geometry.RingedSpace.PresheafedSpace
import all Mathlib.Geometry.RingedSpace.SheafedSpace
import all Mathlib.Topology.Category.CompHausLike.Basic
import all Mathlib.Topology.Category.CompHausLike.Limits
import all Mathlib.Topology.Category.Profinite.Basic
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all Mathlib.Topology.Category.Profinite.Limits
import all Mathlib.Topology.Category.TopCat.Basic
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Mathlib.Topology.ContinuousMap.Defs
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Compactification refinement on the ambient localizing category

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
proposition-construction-independence-rf-shriek--7; Stacks Project, Tags 09AH, 08BJ, 015F and 0D6E
(blueprint: proposition-construction-independence-rf-shriek--7).

The restriction comparison is the canonical counit mate of pullback composition.
Its inverse, followed by the open adjunction, defines the refinement map on the entire
unbounded module-object derived category. Only its invertibility is restricted to Loc(Dctf).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian
open scoped CategoryTheory.Obj ZeroObject

namespace RefinementUnit
variable {C D : Type u} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [HasKInjectiveResolutions C]
private noncomputable def did : (𝟭 C).rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso C
private theorem did_fac (K : HomotopyCategory C (.up ℤ)) :
    (𝟭 C).rightDerivedFunctorUnit.app K ≫ (did (C := C)).hom.app
        (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom.app K) := by
  have h := congrArg (fun e ↦ e.hom.app K) (Functor.mapDerivedCategoryIdIso_factorsh C)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app] at h
  dsimp only [did, Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc]
  have hh := NatTrans.congr_app (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hh
  erw [Category.comp_id, Category.comp_id] at h
  rw [hh, h, Iso.inv_hom_id_app_assoc]

private noncomputable def derivedId (F : C ⥤ C) [F.Additive] (e : F ≅ 𝟭 C) :
    F.rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  Functor.rightDerivedFunctorNatIso e ≪≫ did

private theorem derivedId_fac (F : C ⥤ C) [F.Additive] (e : F ≅ 𝟭 C)
    (K : HomotopyCategory C (.up ℤ)) :
    F.rightDerivedFunctorUnit.app K ≫ (derivedId F e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  have h := NatTrans.congr_app (Functor.rightDerivedNatTrans_fac
    F.rightDerivedFunctor (𝟭 C).rightDerivedFunctor
    F.rightDerivedFunctorUnit (𝟭 C).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
      DerivedCategory.Qh)) K
  dsimp only [derivedId, Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc]
  change _ ≫ (did (C := C)).hom.app _ = _
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  change F.rightDerivedFunctorUnit.app K ≫
    (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj K) = _ at h
  erw [h, Category.assoc, did_fac, Functor.mapHomotopyCategoryIdIso_hom_app_eq_id,
    DerivedCategory.Qh.map_id, Category.comp_id]

private theorem derivedId_inv_app (F : C ⥤ C) [F.Additive] (e : F ≅ 𝟭 C)
    (K : HomotopyCategory C (.up ℤ)) :
    (derivedId F e).inv.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app K) ≫
        F.rightDerivedFunctorUnit.app K := by
  rw [← cancel_mono ((derivedId F e).hom.app (DerivedCategory.Qh.obj K)),
    Iso.inv_hom_id_app, Category.assoc, derivedId_fac,
    ← DerivedCategory.Qh.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  exact (DerivedCategory.Qh.map_id _).symm

private theorem derivedId_comp (F : C ⥤ C) (G : C ⥤ D) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes]
    (i : F ≅ 𝟭 C) (e : F ⋙ G ≅ G)
    (he : Functor.whiskerRight i.inv G ≫ e.hom = 𝟙 G) :
    Functor.whiskerRight (derivedId F i).inv G.rightDerivedFunctor ≫
        (Functor.rightDerivedFunctorCompIso' F G e).hom =
      𝟙 G.rightDerivedFunctor := by
  refine Functor.rightDerived_ext G.rightDerivedFunctor G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ)) _ _ _ ?_
  ext K : 2
  have hnat := G.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory i.inv (.up ℤ)).app K)
  have hfac : Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
        DerivedCategory.Qh ≫ G.rightDerivedFunctorUnit := by
    have hcomp : (F ⋙ G).rightDerivedFunctorUnit ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.rightDerivedFunctorCompIso F G).hom =
        Functor.rightDerivedFunctorCompUnit F G := by
      simp [Functor.rightDerivedFunctorCompIso]
    rw [← hcomp, Category.assoc, ← Functor.whiskerLeft_comp]
    simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
    rw [Iso.hom_inv_id_assoc]
    exact Functor.rightDerivedNatTrans_fac _ _ _ _
      (HomotopyCategory.quasiIso C (.up ℤ)) _
  have hfac2 := NatTrans.congr_app hfac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hfac2 ⊢
  rw [derivedId_inv_app, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_map] at hnat
  erw [← reassoc_of% hnat]
  dsimp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hfac2
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hfac2
  have hid : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) K
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  erw [hid, DerivedCategory.Qh.map_id] at hfac2
  erw [Category.id_comp] at hfac2
  erw [hfac2, ← DerivedCategory.Qh.map_comp_assoc]
  have hcomp : (G.mapHomotopyCategory (.up ℤ)).map
      ((NatTrans.mapHomotopyCategory i.inv (.up ℤ)).app K) ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K = 𝟙 _ := by
    change (NatTrans.mapHomotopyCategory (Functor.whiskerRight i.inv G) (.up ℤ)).app K ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K = _
    erw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, he,
      NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
    rfl
  erw [hcomp, DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id]

private theorem derive_trans {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (e : F ≅ G) (e' : G ≅ H) :
    (Functor.rightDerivedFunctorNatIso (e ≪≫ e')).hom =
      (Functor.rightDerivedFunctorNatIso e).hom ≫
        (Functor.rightDerivedFunctorNatIso e').hom := by
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    ← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp]

private theorem derive_eqToIso {α : Type*} (κ : α → C ⥤ D)
    [∀ a, (κ a).Additive] {a b : α} (h : a = b) :
    (Functor.rightDerivedFunctorNatIso (eqToIso (congrArg κ h))).hom =
      (eqToIso (congrArg (fun a ↦ (κ a).rightDerivedFunctor) h)).hom := by
  cases h
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]

end RefinementUnit

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionMate_isIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    {J : A ⥤ B} {U : B ⥤ A} {H : B ⥤ C} {R : C ⥤ B}
    {J' : A ⥤ C} {U' : C ⥤ A}
    (a : J ⊣ U) (b : H ⊣ R) (c : J' ⊣ U')
    (e : U ≅ H ⋙ U') [IsIso a.unit]
    (hc : ∀ K : A, IsIso (c.counit.app (H.obj (J.obj K)))) :
    IsIso (Functor.whiskerLeft R e.hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight b.counit U' ≫ (Functor.leftUnitor _).hom) := by
  let ρ : R ⋙ U ⟶ U' := Functor.whiskerLeft R e.hom ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight b.counit U' ≫
    (Functor.leftUnitor _).hom
  have hcomp (K : A) :
      ((conjugateEquiv (a.comp b) c).symm ρ).app K =
        J'.map (a.unit.app K ≫ e.hom.app (J.obj K)) ≫
          c.counit.app (H.obj (J.obj K)) := by
    have hinner : U.map (b.unit.app (J.obj K)) ≫
        e.hom.app (R.obj (H.obj (J.obj K))) ≫
          U'.map (b.counit.app (H.obj (J.obj K))) = e.hom.app (J.obj K) := by
      have hn := e.hom.naturality (b.unit.app (J.obj K))
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [← Category.assoc, hn, Category.assoc]
      simp only [← U'.map_comp, b.left_triangle_components,
        Functor.map_id, Category.comp_id]
    simp only [conjugateEquiv_symm_apply_app, Adjunction.comp_unit_app,
      ρ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.comp_obj, Category.id_comp,
      Functor.map_comp, Category.assoc]
    erw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ J'.map (a.unit.app K) ≫ J'.map z ≫
        c.counit.app (H.obj (J.obj K))) hinner
  have hσ : IsIso ((conjugateEquiv (a.comp b) c).symm ρ) := by
    have hσapp (K : A) : IsIso (((conjugateEquiv (a.comp b) c).symm ρ).app K) := by
      rw [hcomp]
      have := hc K
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact conjugateEquiv_symm_of_iso (a.comp b) c ρ

/-- Zero objects are closed under isomorphisms; the instance making functor kernels
closed under isomorphisms is no longer in the imported library. -/
local instance isZero_isClosedUnderIsomorphisms_local {C : Type*} [Category C] :
    ObjectProperty.IsClosedUnderIsomorphisms (IsZero (C := C)) :=
  ⟨fun e h ↦ h.of_iso e.symm⟩

private theorem kernelTriangulated
    {C : Type v} {D : Type w} [Category C] [Category D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] :
    F.kernel.IsTriangulated := by
  let hshift (n : ℤ) : F.kernel.IsStableUnderShiftBy n := ⟨fun M hM ↦
    (Functor.map_isZero (shiftFunctor D n) hM).of_iso ((F.commShiftIso n).app M)⟩
  let : F.kernel.IsStableUnderShift ℤ := ⟨hshift⟩
  let : F.kernel.ContainsZero := ⟨0, isZero_zero C,
    Functor.map_isZero F (isZero_zero C)⟩
  let : F.kernel.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦
    Pretriangulated.Triangle.isZero₂_of_isZero₁₃ _ (F.map_distinguished T hT) h₁ h₃)
  exact {}

private theorem extend_zero
    {C : Type v} {D : Type w} [Category.{v₁} C] [Category D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (S : ObjectProperty C) (hloc : IsLocalizingSubcategory (localizingClosure S))
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (hsums : ∀ (I : Type v₁) (J : Discrete I ⥤ C),
      (∀ i, localizingClosure S (J.obj (Discrete.mk i))) → PreservesColimit J F)
    (hS : ∀ K, S K → IsZero (F.obj K)) :
    ∀ K, localizingClosure S K → IsZero (F.obj K) := by
  let L := localizingClosure S
  let P : ObjectProperty C := L ⊓ F.kernel
  let : L.IsTriangulated := hloc.1
  let : L.IsClosedUnderIsomorphisms := hloc.2.1
  let := kernelTriangulated F
  have hP : IsLocalizingSubcategory P := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I J hJ hK
    let := hJ
    let := hsums I J (fun i ↦ (hK i).1)
    refine ⟨hloc.2.2 J hJ (fun i ↦ (hK i).1), ?_⟩
    have hF : IsZero (J ⋙ F) := (Functor.isZero_iff _).mpr (fun j ↦ (hK j.as).2)
    exact (isColimitOfPreserves F (colimit.isColimit J)).isZero_pt hF
  intro K hK
  exact (hK P hP (fun M hM ↦ ⟨fun Q hQ hSQ ↦ hSQ M hM, hS M hM⟩)).2

private theorem adjoint_normalization_iff
    {A B : Type*} [Category A] [Category B]
    {J : A ⥤ B} {U : B ⥤ A} (a : J ⊣ U)
    (K : A) (M : B) (θ : U.obj M ≅ K) (b : J.obj K ⟶ M) :
    a.unit.app K ≫ U.map b ≫ θ.hom = 𝟙 K ↔
      b = (a.homEquiv K M).symm θ.inv := by
  rw [← Category.assoc, ← a.homEquiv_unit K M b]
  constructor
  · intro hb
    apply (a.homEquiv K M).injective
    rw [Equiv.apply_symm_apply]
    calc
      (a.homEquiv K M) b = ((a.homEquiv K M) b ≫ θ.hom) ≫ θ.inv := by simp
      _ = θ.inv := by rw [hb, Category.id_comp]
  · intro hb
    rw [hb, Equiv.apply_symm_apply, θ.inv_hom_id]

private theorem isIso_adjoint_inverse
    {A B : Type*} [Category A] [Category B]
    {J : A ⥤ B} {U : B ⥤ A} (a : J ⊣ U)
    (K : A) (M : B) (θ : U.obj M ≅ K)
    [IsIso (a.counit.app M)] :
    IsIso ((a.homEquiv K M).symm θ.inv) := by
  rw [a.homEquiv_counit]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_mate_pasting
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {U₀ : A ⥤ D} {U₁ : B ⥤ D} {U₂ : C ⥤ D}
    {H : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
    {L : A ⥤ C} {T : C ⥤ A}
    (a : H ⊣ R) (b : G ⊣ S) (c : L ⊣ T)
    (e : U₀ ⟶ H ⋙ U₁) (d : U₁ ⟶ G ⋙ U₂) (v : U₀ ⟶ L ⋙ U₂)
    (q : H ⋙ G ⟶ L) (κ : T ⟶ S ⋙ R)
    (hq : ∀ M, v.app M = e.app M ≫ d.app (H.obj M) ≫ U₂.map (q.app M))
    (hκ : ∀ N, (H ⋙ G).map (κ.app N) ≫ (a.comp b).counit.app N =
      q.app (T.obj N) ≫ c.counit.app N) (N : C) :
    v.app (T.obj N) ≫ U₂.map (c.counit.app N) =
      U₀.map (κ.app N) ≫ e.app (R.obj (S.obj N)) ≫
        U₁.map (a.counit.app (S.obj N)) ≫ d.app (S.obj N) ≫
          U₂.map (b.counit.app N) := by
  have he := e.naturality (κ.app N)
  have hd := d.naturality (a.counit.app (S.obj N))
  dsimp only [Functor.comp_map, Functor.comp_obj] at he hd
  rw [reassoc_of% he, reassoc_of% hd]
  have hdκ := d.naturality (H.map (κ.app N))
  dsimp only [Functor.comp_map] at hdκ
  rw [reassoc_of% hdκ, ← U₂.map_comp_assoc, ← U₂.map_comp]
  have hε := hκ N
  simp only [Adjunction.comp_counit_app, Functor.comp_map] at hε
  rw [Category.assoc, hε, Functor.map_comp]
  rw [hq]
  simp only [Category.assoc]

private theorem triangle_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {I J K : Type*} (f : J → I) (g : K → J) (h : K → I)
    (ass : ∀ x, f (g x) = h x)
    (U : I → A ⥤ D) (V : J → B ⥤ D) (W : K → C ⥤ D)
    (H : A ⥤ B) (G : B ⥤ C) (L : A ⥤ C) (q : L ≅ H ⋙ G)
    (c₁ : ∀ x, U (f x) ≅ H ⋙ V x) (c₂ : ∀ x, V (g x) ≅ G ⋙ W x)
    (c₃ : ∀ x, U (h x) ≅ L ⋙ W x)
    (hc : ∀ x, c₃ x ≪≫ Functor.isoWhiskerRight q (W x) ≪≫
      Functor.associator H G (W x) =
        eqToIso (congrArg U (ass x).symm) ≪≫ c₁ (g x) ≪≫
          Functor.isoWhiskerLeft H (c₂ x))
    (x : I) (y : J) (z : K) (eh : f y = x) (ea : g z = y) (eah : h z = x) :
    (eqToIso (congrArg U eh.symm) ≪≫ c₁ y) ≪≫
        Functor.isoWhiskerLeft H (eqToIso (congrArg V ea.symm) ≪≫ c₂ z) =
      (eqToIso (congrArg U eah.symm) ≪≫ c₃ z) ≪≫
        Functor.isoWhiskerRight q (W z) ≪≫ Functor.associator H G (W z) := by
  subst x
  subst y
  have hh := congrArg
    (fun t ↦ (eqToIso (congrArg U (ass z).symm)).symm ≪≫ t) (hc z)
  simp only [Iso.symm_self_id_assoc] at hh
  have heq : (eqToIso (congrArg U (ass z).symm)).symm =
      eqToIso (congrArg U eah.symm) := by
    apply Iso.ext
    rfl
  rw [heq] at hh
  simpa only [eqToIso_refl, Iso.refl_trans, Functor.isoWhiskerLeft_refl,
    Iso.trans_refl, Iso.trans_assoc] using hh.symm

set_option backward.isDefEq.respectTransparency false in
private theorem derivedTriangle_pasting
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {H : A ⥤ B} {G : B ⥤ C} {F : C ⥤ D}
    {FG : B ⥤ D} {GH : A ⥤ C} {V : A ⥤ D}
    [H.Additive] [G.Additive] [F.Additive] [FG.Additive] [GH.Additive] [V.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e₁ : V ≅ H ⋙ FG) (eFG : FG ≅ G ⋙ F)
    (e₂ : V ≅ GH ⋙ F) (eGH : GH ≅ H ⋙ G)
    (h : e₁ ≪≫ Functor.isoWhiskerLeft H eFG =
      e₂ ≪≫ Functor.isoWhiskerRight eGH F ≪≫ (Functor.associator H G F)) :
    (Functor.mapDerivedCategoryTriangleIso e₁).hom ≫
        Functor.whiskerLeft H.mapDerivedCategory
          (Functor.mapDerivedCategoryTriangleIso eFG).hom =
      (Functor.mapDerivedCategoryTriangleIso e₂).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eGH).hom
          F.mapDerivedCategory := by
  have hassoc : Functor.associator H G F = Iso.refl _ := by ext; rfl
  rw [hassoc, Iso.trans_refl] at h
  ext K
  have hh := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app K) h
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hh
  have hwl := NatTrans.congr_app
    (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft H eFG) K
  have hwr := NatTrans.congr_app
    (Functor.mapDerivedCategoryNatIso_isoWhiskerRight eGH F) K
  have ha := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_assoc H G F) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at hwl hwr ha
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    Iso.symm_hom]
  rw [← reassoc_of% hwl, ha, ← reassoc_of% hwr]
  rw [← Category.assoc, ← Category.assoc, hh]
  simp only [Category.assoc]

section

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ X : C, PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ X : C, PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]

private theorem normalizedDerivedAdjunction (adj : f ⊣ g) :
    adj.derivedAdjunction.ofNatIsoLeft f.leftDerivedFunctorIsoMapDerivedCategory =
      adj.mapDerivedCategoryRightDerivedAdjunction := by
  apply Adjunction.ext_counit
  apply (g.rightDerivedFunctor ⋙
    f.mapDerivedCategory).rightDerived_ext
      (Functor.whiskerRight g.rightDerivedFunctorUnit
        f.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso _ (.up ℤ))
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id, Adjunction.ofNatIsoLeft_counit]
  let e := f.leftDerivedFunctorIsoMapDerivedCategory
  have hn := e.inv.naturality (g.rightDerivedFunctorUnit.app K)
  have hε := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ))
    f.leftDerivedFunctorCounit g.rightDerivedFunctorUnit K
  have hε' := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ))
    f.mapDerivedCategoryFactorsh.hom g.rightDerivedFunctorUnit K
  dsimp only [e, Functor.comp_obj] at hn
  erw [← Category.assoc, hn, Category.assoc]
  erw [hε, hε']
  have hf := NatTrans.congr_app
    f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((g.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  rw [← hf]
  simp only [Category.assoc,
    Iso.inv_hom_id_app_assoc]

end

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Reuse the canonical module and graded-tensor structures in the derived adjunctions.
attribute [local instance 3000] projectionDerivedMonoidal
attribute [local instance 4000] projectionModuleAbelian projectionModuleMonoidal
  projectionModuleHasDerived
attribute [local instance 5000] projectionSheafMonoidal projectionCoefficientMonObj
  projectionModuleCategory
attribute [local instance 2000] CategoryTheory.scalarTensor4 CategoryTheory.scalarTensor12
  CategoryTheory.scalarTensor23 CategoryTheory.scalarTensorColimits
  CategoryTheory.scalarFlipTensorColimits

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct upperStarFromPoint

attribute [local instance 2000] CategoryTheory.Mod.hasFunctorialFlatResolution
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

set_option backward.isDefEq.respectTransparency false in
private theorem refinementAdjunction_eq {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction Λ h).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ h) =
      (upperStarLowerStarAdjunction Λ h).mapDerivedCategoryRightDerivedAdjunction :=
  CategoryTheory.normalizedDerivedAdjunction (upperStarLowerStarAdjunction Λ h)

/-- The identity direct-image identification is linear for the pulled-back coefficient ring.
Source: blueprint refinement clause (3), canonical identity identifications
(blueprint: proposition-construction-independence-rf-shriek--7).
Proof: expand the action on lowerStar; condensedPushforwardHom_id is the inverse identity
identification on the coefficient ring. Naturality and the tensor identity of the abelian
identity compositor cancel this inverse, leaving exactly the action of M. -/
theorem refinementLowerStarId_linear (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.act (((lowerStar Λ (𝟙 X)).obj M).X) ≫
        (ProEtale.lowerStarId Ab.{u + 1} X).hom.app M.X =
      (condensedRingObj Λ X) ◁ (ProEtale.lowerStarId Ab.{u + 1} X).hom.app M.X ≫
        Mod.act M.X := by
  have _ := (inferInstance : IsCommMonObj Λ)
  have h := Mod.act_hom ((lowerStarId Λ X).hom.app M)
  rw [lowerStarId_hom_app_hom] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The linear identity components are natural.
Source: blueprint refinement clause (3), canonical identity identifications
(blueprint: proposition-construction-independence-rf-shriek--7).
Proof: apply the faithful module forgetful functor. Both sides become the naturality
square of ProEtale.lowerStarId on the underlying abelian-sheaf morphism. -/
theorem refinementLowerStarId_naturality (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (v : M ⟶ N) :
    (lowerStar Λ (𝟙 X)).map v ≫
        (Mod.isoMk (M := (lowerStar Λ (𝟙 X)).obj N) (N := N)
          ((ProEtale.lowerStarId Ab.{u + 1} X).app N.X)
          (refinementLowerStarId_linear Λ X N)).hom =
      (Mod.isoMk (M := (lowerStar Λ (𝟙 X)).obj M) (N := M)
          ((ProEtale.lowerStarId Ab.{u + 1} X).app M.X)
          (refinementLowerStarId_linear Λ X M)).hom ≫ v := by
  apply Mod.hom_ext
  simpa only [Mod.comp_hom', Mod.isoMk_hom_hom, Iso.app_hom, Functor.id_map,
    lowerStar_map_hom] using
    (ProEtale.lowerStarId Ab.{u + 1} X).hom.naturality v.hom

/-- The canonical identity direct-image isomorphism, with its actual abelian-sheaf components.
Source: blueprint refinement clause (3)
(blueprint: proposition-construction-independence-rf-shriek--7). -/
def refinementLowerStarId (X : Scheme.{u}) : lowerStar Λ (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk (M := (lowerStar Λ (𝟙 X)).obj M) (N := M)
          ((ProEtale.lowerStarId Ab.{u + 1} X).app M.X)
      (refinementLowerStarId_linear Λ X M))
    (fun v ↦ refinementLowerStarId_naturality Λ X v)

/-- The canonical derived identity identification, obtained by deriving the identity
identification on module sheaves. Source: blueprint refinement clause (3)
(blueprint: proposition-construction-independence-rf-shriek--7). -/
def refinementDerivedLowerStarId (X : Scheme.{u}) :
    (lowerStar Λ (𝟙 X)).rightDerivedFunctor ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorNatIso (refinementLowerStarId Λ X) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The canonical unbounded derived direct-image compositor, normalized by the underived
module compositor and the K-injective derived-functor units. Source: blueprint refinement
clause (3); Stacks Tag 0D6E (blueprint: proposition-construction-independence-rf-shriek--7). -/
def refinementDerivedLowerStarComp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (h : Y ⟶ Z) :
    (lowerStar Λ (a ≫ h)).rightDerivedFunctor ≅
      (lowerStar Λ a).rightDerivedFunctor ⋙ (lowerStar Λ h).rightDerivedFunctor :=
  letI := (upperStarLowerStarAdjunction Λ a).preservesKInjectiveComplexes
  Functor.rightDerivedFunctorNatIso (lowerStarComp Λ a h).symm ≪≫
    Functor.rightDerivedFunctorCompIso (lowerStar Λ a) (lowerStar Λ h)

set_option backward.isDefEq.respectTransparency false in
private theorem refinementComp_conjugate {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (h : Y ⟶ Z) :
    (refinementDerivedLowerStarComp Λ a h).inv =
      conjugateEquiv
        ((upperStarLowerStarAdjunction Λ h).mapDerivedCategoryRightDerivedAdjunction.comp
          (upperStarLowerStarAdjunction Λ a).mapDerivedCategoryRightDerivedAdjunction)
        (upperStarLowerStarAdjunction Λ (a ≫ h)).mapDerivedCategoryRightDerivedAdjunction
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ a h)).hom := by
  let := (upperStarLowerStarAdjunction Λ a).preservesKInjectiveComplexes
  exact Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction Λ a) (upperStarLowerStarAdjunction Λ h)
    (upperStarLowerStarAdjunction Λ (a ≫ h)) (lowerStarComp Λ a h)
    (upperStarComp Λ a h)
    (congrArg Iso.hom (conjugateIsoEquiv_upperStarComp Λ a h)).symm

attribute [local irreducible] upperStar upperStarComp lowerStar openImmersionLowerShriek

set_option backward.isDefEq.respectTransparency false in
private theorem refinementPullback_triangle {W X Y Z : Scheme.{u}}
    (j₀ : W ⟶ Z) (j₁ : W ⟶ Y) (j₂ : W ⟶ X) (a : X ⟶ Y) (h : Y ⟶ Z)
    (eh : j₁ ≫ h = j₀) (ea : j₂ ≫ a = j₁) (eah : j₂ ≫ (a ≫ h) = j₀) :
    (eqToIso (congrArg (upperStar Λ) eh.symm) ≪≫ upperStarComp Λ j₁ h) ≪≫
        Functor.isoWhiskerLeft (upperStar Λ h)
          (eqToIso (congrArg (upperStar Λ) ea.symm) ≪≫ upperStarComp Λ j₂ a) =
      (eqToIso (congrArg (upperStar Λ) eah.symm) ≪≫ upperStarComp Λ j₂ (a ≫ h)) ≪≫
        Functor.isoWhiskerRight (upperStarComp Λ a h) (upperStar Λ j₂) ≪≫
          Functor.associator (upperStar Λ h) (upperStar Λ a) (upperStar Λ j₂) := by
  exact CategoryTheory.triangle_transport
    (fun j ↦ j ≫ h) (fun j ↦ j ≫ a) (fun j ↦ j ≫ (a ≫ h))
    (fun j ↦ Category.assoc j a h)
    (upperStar Λ) (upperStar Λ) (upperStar Λ)
    (upperStar Λ h) (upperStar Λ a) (upperStar Λ (a ≫ h)) (upperStarComp Λ a h)
    (fun j ↦ upperStarComp Λ j h) (fun j ↦ upperStarComp Λ j a)
    (fun j ↦ upperStarComp Λ j (a ≫ h))
    (fun j ↦ upperStarComp_assoc Λ j a h) j₀ j₁ j₂ eh ea eah

/-- Open extension followed by open restriction has its invertible canonical unit, also on
unbounded complexes. Source: blueprint refinement proof step 1; Stacks Tags 09AH and 015F
(blueprint: proposition-construction-independence-rf-shriek--7).
Proof: the sheaf open adjunction has invertible unit, since restriction of extension by
zero is the original module with the same action. Both functors are exact. Descend their
termwise unit and counit through quasi-isomorphisms; the triangle identities and inverse
unit descend too. This is the derived adjunction used here. -/
theorem refinementOpenUnit_isIso {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  have := openUnitIsIso Λ j
  exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit
    (openImmersionLowerShriekUpperStarAdjunction Λ j)

attribute [local irreducible] derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  upperStarLowerStarAdjunction

attribute [instance] refinementOpenUnit_isIso

/-- The canonical restriction map j* Rh* M → j'* M: pullback composition, followed by the
counit of Lh* ⊣ Rh*. The commuting open triangle fixes every coefficient identification.
Source: blueprint refinement, The restriction to X, proof steps 1--2
(blueprint: proposition-construction-independence-rf-shriek--7). -/
def refinementOpenRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : d.Refinement c) :
    (lowerStar Λ r.hom).rightDerivedFunctor ⋙ (upperStar Λ c.i).mapDerivedCategory ⟶
      (upperStar Λ d.i).mapDerivedCategory :=
  Functor.whiskerLeft (lowerStar Λ r.hom).rightDerivedFunctor
      (Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (upperStar Λ) r.i_hom.symm) ≪≫ upperStarComp Λ d.i r.hom) ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar Λ r.hom) (upperStar Λ d.i)).symm).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (lowerStar Λ r.hom).rightDerivedFunctor
          (leftDerivedUpperStarIsoMapDerivedCategory Λ r.hom).inv ≫
        (derivedUpperStarLowerStarAdjunction Λ r.hom).counit)
      (upperStar Λ d.i).mapDerivedCategory ≫
    (Functor.leftUnitor _).hom

set_option backward.isDefEq.respectTransparency false in
/-- For a boundary-preserving refinement the specified restriction map is invertible on
all unbounded complexes; no proper base change for arbitrary complexes is assumed.
Source: blueprint refinement, The restriction to X, proof step 2
(blueprint: proposition-construction-independence-rf-shriek--7).
Proof: choose a K-injective resolution I of M. Over V → X, the inverse-image-open equality
identifies V ×_Z Z' with V, hence j* h* I = j'* I sectionwise, including the coefficient
action. The counit mate defining refinementOpenRestriction is exactly this identification.
Restriction is exact, and j'* preserves K-injectives because j'! is its exact left adjoint.
Thus the sectionwise identity represents the stated map in the unbounded derived category,
and is invertible. Functorial resolutions give naturality and independence of I. -/
theorem refinementOpenRestriction_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c) :
    IsIso (refinementOpenRestriction Λ r.hom.hom) := by
  have sq : IsPullback (𝟙 X) d.obj.obj.i c.obj.obj.i r.hom.hom.hom :=
    IsOpenImmersion.isPullback _ _ _ _
      (by simpa only [Category.id_comp] using r.hom.hom.i_hom) r.property
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i
  let b := (derivedUpperStarLowerStarAdjunction Λ r.hom.hom.hom).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ r.hom.hom.hom)
  let a' := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i
  let e := Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (upperStar Λ) r.hom.hom.i_hom.symm) ≪≫
        upperStarComp Λ d.obj.obj.i r.hom.hom.hom) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar Λ r.hom.hom.hom)
      (upperStar Λ d.obj.obj.i)).symm
  have : IsIso a.unit := refinementOpenUnit_isIso Λ c.obj.obj.i
  have hc (K) : IsIso (a'.counit.app
      ((upperStar Λ r.hom.hom.hom).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K))) := by
    have hbase := cartesianDerivedCounit Λ sq K
    let eK := (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek Λ c.obj.obj.i) (upperStar Λ r.hom.hom.hom)).symm.app K
    exact (NatTrans.isIso_app_iff_of_iso _ eK).mp hbase
  have hi := CategoryTheory.restrictionMate_isIso a b a' e hc
  simpa only [refinementOpenRestriction, e, b, Adjunction.ofNatIsoLeft_counit] using hi

set_option backward.isDefEq.respectTransparency false in
private theorem refinementRestriction_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification.BoundaryCompactification f} (r : d ⟶ c) (s : e ⟶ d)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology e.obj.obj.Z) Ab.{u + 1})
        (condensedRingObj Λ e.obj.obj.Z))) :
    (refinementOpenRestriction Λ (s ≫ r).hom.hom).app M =
      (upperStar Λ c.obj.obj.i).mapDerivedCategory.map
          ((refinementDerivedLowerStarComp Λ s.hom.hom.hom r.hom.hom.hom).hom.app M) ≫
        (refinementOpenRestriction Λ r.hom.hom).app
          ((lowerStar Λ s.hom.hom.hom).rightDerivedFunctor.obj M) ≫
        (refinementOpenRestriction Λ s.hom.hom).app M := by
  let A := (upperStarLowerStarAdjunction Λ r.hom.hom.hom).mapDerivedCategoryRightDerivedAdjunction
  let B := (upperStarLowerStarAdjunction Λ s.hom.hom.hom).mapDerivedCategoryRightDerivedAdjunction
  let C := Adjunction.mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ (s.hom.hom.hom ≫ r.hom.hom.hom))
  let E := fun {P Q : Scheme.{u}} (j : X ⟶ P) (j' : X ⟶ Q) (t : Q ⟶ P)
    (et : j' ≫ t = j) ↦ Functor.mapDerivedCategoryTriangleIso
      (eqToIso (congrArg (upperStar Λ) et.symm) ≪≫ upperStarComp Λ j' t)
  let q := Functor.mapDerivedCategoryTriangleIso
    (upperStarComp Λ s.hom.hom.hom r.hom.hom.hom)
  let κ := refinementDerivedLowerStarComp Λ s.hom.hom.hom r.hom.hom.hom
  have hκ : κ.hom = conjugateEquiv C (A.comp B) q.inv := by
    have hi := refinementComp_conjugate Λ s.hom.hom.hom r.hom.hom.hom
    have he : κ.symm = conjugateIsoEquiv (A.comp B) C q := Iso.ext hi
    have hv := congrArg (fun z ↦ z.symm.hom) he
    exact hv
  have hc (N) := conjugateEquiv_counit C (A.comp B) q.inv N
  rw [← hκ] at hc
  have hp := CategoryTheory.derivedTriangle_pasting
    (eqToIso (congrArg (upperStar Λ) r.hom.hom.i_hom.symm) ≪≫
      upperStarComp Λ d.obj.obj.i r.hom.hom.hom)
    (eqToIso (congrArg (upperStar Λ) s.hom.hom.i_hom.symm) ≪≫
      upperStarComp Λ e.obj.obj.i s.hom.hom.hom)
    (eqToIso (congrArg (upperStar Λ) (s ≫ r).hom.hom.i_hom.symm) ≪≫
      upperStarComp Λ e.obj.obj.i (s.hom.hom.hom ≫ r.hom.hom.hom))
    (upperStarComp Λ s.hom.hom.hom r.hom.hom.hom)
    (refinementPullback_triangle Λ c.obj.obj.i d.obj.obj.i e.obj.obj.i
      s.hom.hom.hom r.hom.hom.hom r.hom.hom.i_hom s.hom.hom.i_hom
      (s ≫ r).hom.hom.i_hom)
  have ht (N) : (E c.obj.obj.i e.obj.obj.i _ (s ≫ r).hom.hom.i_hom).hom.app N =
      (E c.obj.obj.i d.obj.obj.i _ r.hom.hom.i_hom).hom.app N ≫
        (E d.obj.obj.i e.obj.obj.i _ s.hom.hom.i_hom).hom.app
          ((upperStar Λ r.hom.hom.hom).mapDerivedCategory.obj N) ≫
        (upperStar Λ e.obj.obj.i).mapDerivedCategory.map (q.inv.app N) := by
    have hn := NatTrans.congr_app hp N
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hn
    dsimp only [E]
    simpa only [Category.assoc, WideSubcategory.comp_def,
      ObjectProperty.FullSubcategory.comp_hom, Compactification.comp_hom,
      Functor.mapIso_inv, Iso.app_inv] using
      (Iso.eq_comp_inv ((upperStar Λ e.obj.obj.i).mapDerivedCategory.mapIso
        (q.app N))).2 hn.symm
  have hz := CategoryTheory.restriction_mate_pasting A B C
    (E _ _ _ r.hom.hom.i_hom).hom (E _ _ _ s.hom.hom.i_hom).hom
    (E _ _ _ (s ≫ r).hom.hom.i_hom).hom q.inv κ.hom ht hc M
  simp only [refinementOpenRestriction, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  simpa only [E, A, B, C, κ, Adjunction.comp_counit_app, Functor.map_comp,
    ← refinementAdjunction_eq, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc, Category.comp_id,
    Functor.mapDerivedCategoryTriangleIso, Functor.comp_obj, Functor.id_obj,
    WideSubcategory.comp_def, ObjectProperty.FullSubcategory.comp_hom,
    Compactification.comp_hom] using hz

/-- The canonical θ_h,K: restriction of Rh*j'!K to X, then the inverse open unit.
Source: blueprint refinement, displayed θ (blueprint:
proposition-construction-independence-rf-shriek--7). -/
def refinementTheta {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (upperStar Λ c.obj.obj.i).mapDerivedCategory.obj
        ((lowerStar Λ r.hom.hom.hom).rightDerivedFunctor.obj
          ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K)) ≅ K :=
  letI := refinementOpenRestriction_isIso Λ r
  asIso ((refinementOpenRestriction Λ r.hom.hom).app
      ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K)) ≪≫
    (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i).unit.app K)).symm

/-- The refinement map is the adjoint of θ⁻¹, with no choice of an arbitrary isomorphism.
Source: blueprint refinement, displayed e and clause (1)
(blueprint: proposition-construction-independence-rf-shriek--7). -/
def localizingRefinementMap {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K ⟶
      (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).homEquiv _ _).symm
    (refinementTheta Λ r K).inv

set_option backward.isDefEq.respectTransparency false in
private theorem localizingRefinementMap_normalized
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).unit.app K ≫
        (upperStar Λ c.obj.obj.i).mapDerivedCategory.map (localizingRefinementMap Λ r K) ≫
        (refinementOpenRestriction Λ r.hom.hom).app
          ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ d.obj.obj.i).unit.app K := by
  let := refinementOpenRestriction_isIso Λ r
  erw [← Category.assoc, ← Adjunction.homEquiv_unit]
  simp only [localizingRefinementMap, Functor.id_obj, Equiv.apply_symm_apply, refinementTheta,
    Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc, asIso_inv,
    IsIso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem localizingRefinementMap_comp
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification.BoundaryCompactification f} (r : d ⟶ c) (s : e ⟶ d)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    localizingRefinementMap Λ (s ≫ r) K ≫
        (refinementDerivedLowerStarComp Λ s.hom.hom.hom r.hom.hom.hom).hom.app
          ((openImmersionLowerShriek Λ e.obj.obj.i).mapDerivedCategory.obj K) =
      localizingRefinementMap Λ r K ≫
        (lowerStar Λ r.hom.hom.hom).rightDerivedFunctor.map
          (localizingRefinementMap Λ s K) := by
  let := refinementOpenRestriction_isIso Λ r
  let := refinementOpenRestriction_isIso Λ s
  apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  apply (cancel_mono
    ((refinementOpenRestriction Λ r.hom.hom).app
      ((lowerStar Λ s.hom.hom.hom).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ e.obj.obj.i).mapDerivedCategory.obj K)) ≫
      (refinementOpenRestriction Λ s.hom.hom).app
        ((openImmersionLowerShriek Λ e.obj.obj.i).mapDerivedCategory.obj K))).1
  simp only [Category.assoc]
  rw [← refinementRestriction_comp]
  have hn := (refinementOpenRestriction Λ r.hom.hom).naturality
    (localizingRefinementMap Λ s K)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, localizingRefinementMap_normalized,
    reassoc_of% (localizingRefinementMap_normalized Λ r K),
    localizingRefinementMap_normalized]

private theorem refinement_compositor_unit (S T : Scheme.{u}) (g : S ⟶ T) :
    Functor.whiskerRight (refinementDerivedLowerStarId Λ S).inv
        (lowerStar Λ g).rightDerivedFunctor ≫
      (refinementDerivedLowerStarComp Λ (𝟙 S) g).inv ≫
      (eqToIso (congrArg (fun g ↦ (lowerStar Λ g).rightDerivedFunctor)
        (Category.id_comp g))).hom = 𝟙 (lowerStar Λ g).rightDerivedFunctor := by
  let F := lowerStar Λ (𝟙 S)
  let G := lowerStar Λ g
  let e : F ⋙ G ≅ G := lowerStarComp Λ (𝟙 S) g ≪≫ lowerStarCongr Λ (Category.id_comp g)
  have hi : refinementLowerStarId Λ S = lowerStarId Λ S := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply Mod.hom_ext
    rw [lowerStarId_hom_app_hom]
    rfl
  have he : Functor.whiskerRight (refinementLowerStarId Λ S).inv G ≫ e.hom = 𝟙 G := by
    dsimp only [e]
    rw [hi, lowerStarComp_id_left]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Category.assoc]
    rw [← Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id]
    ext M
    simp [G, lowerStarCongr]
    rfl
  let := (upperStarLowerStarAdjunction Λ (𝟙 S)).preservesKInjectiveComplexes
  have h := RefinementUnit.derivedId_comp F G (refinementLowerStarId Λ S) e he
  have htrans := RefinementUnit.derive_trans (lowerStarComp Λ (𝟙 S) g)
    (lowerStarCongr Λ (Category.id_comp g))
  have heq : (Functor.rightDerivedFunctorNatIso
      (lowerStarCongr Λ (Category.id_comp g))).hom =
      (eqToIso (congrArg (fun g ↦ (lowerStar Λ g).rightDerivedFunctor)
        (Category.id_comp g))).hom := by
    exact RefinementUnit.derive_eqToIso (lowerStar Λ) (Category.id_comp g)
  dsimp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom] at h
  dsimp only [e] at h
  rw [htrans, heq] at h
  simpa only [RefinementUnit.derivedId, RefinementUnit.did, refinementDerivedLowerStarId,
    refinementDerivedLowerStarComp, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
    Functor.rightDerivedFunctorNatIso, Functor.whiskerRight_comp, Category.assoc,
    Iso.symm_hom, F, G] using h

private theorem localizingRefinementMap_isIso_of_counit
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hc : IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).counit.app
      ((lowerStar Λ r.hom.hom.hom).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K)))) :
    IsIso (localizingRefinementMap Λ r K) :=
  CategoryTheory.isIso_adjoint_inverse
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)
    K _ (refinementTheta Λ r K)

set_option backward.isDefEq.respectTransparency false in
private theorem localizingRefinementMap_id_isIso
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso (localizingRefinementMap Λ (𝟙 c) K) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i
  let J := (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K
  have hleft : IsIso (a.counit.app J) := by
    have : IsIso ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.map
        (a.unit.app K) ≫ a.counit.app J) := by
      erw [a.left_triangle_components]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.map (a.unit.app K)) _
  have hc := (NatTrans.isIso_app_iff_of_iso a.counit
    ((refinementDerivedLowerStarId Λ c.obj.obj.Z).app J)).mpr hleft
  exact localizingRefinementMap_isIso_of_counit Λ (𝟙 c) K hc

set_option backward.isDefEq.respectTransparency false in
private theorem localizingRefinementMap_id
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    localizingRefinementMap Λ (𝟙 c) K ≫
        (refinementDerivedLowerStarId Λ c.obj.obj.Z).hom.app
          ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K) = 𝟙 _ := by
  let R := (lowerStar Λ (𝟙 c.obj.obj.Z)).rightDerivedFunctor
  let d := refinementDerivedLowerStarId Λ c.obj.obj.Z
  let J := (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K
  let κ₀ := refinementDerivedLowerStarComp Λ (𝟙 c.obj.obj.Z) (𝟙 c.obj.obj.Z)
  let τ := eqToIso (congrArg (fun g ↦ (lowerStar Λ g).rightDerivedFunctor)
    (Category.id_comp (𝟙 c.obj.obj.Z)))
  let κ := τ.symm ≪≫ κ₀
  let e := localizingRefinementMap Λ (𝟙 c) K
  have : IsIso e := localizingRefinementMap_id_isIso Λ c K
  have hcomp := localizingRefinementMap_comp Λ (𝟙 c) (𝟙 c) K
  have ht : localizingRefinementMap Λ (𝟙 c ≫ 𝟙 c) K ≫ τ.hom.app J = e := by
    have hn := eqToHom_naturality (fun r : c ⟶ c ↦ localizingRefinementMap Λ r K)
      (Category.id_comp (𝟙 c))
    simpa only [τ, e, J, eqToHom_refl, Category.id_comp, eqToIso_refl,
      Iso.refl_hom, NatTrans.id_app, WideSubcategory.id_def,
      ObjectProperty.FullSubcategory.id_hom, Compactification.id_hom,
      WideSubcategory.comp_def, ObjectProperty.FullSubcategory.comp_hom,
      Compactification.comp_hom] using hn
  have hh : e ≫ κ.hom.app J = e ≫ R.map e := by
    calc
      e ≫ κ.hom.app J =
          (localizingRefinementMap Λ (𝟙 c ≫ 𝟙 c) K ≫ τ.hom.app J) ≫ κ.hom.app J :=
        congrArg (fun t ↦ t ≫ κ.hom.app J) ht.symm
      _ = localizingRefinementMap Λ (𝟙 c ≫ 𝟙 c) K ≫ κ₀.hom.app J := by
        simp only [κ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
          Category.assoc, Iso.hom_inv_id_app_assoc]
      _ = e ≫ R.map e := by
        simpa only [e, κ₀, R, J, WideSubcategory.id_def,
          ObjectProperty.FullSubcategory.id_hom, Compactification.id_hom] using hcomp
  have hm : κ.hom.app J = R.map e := (cancel_epi e).1 hh
  have hu := NatTrans.congr_app
    (refinement_compositor_unit Λ c.obj.obj.Z c.obj.obj.Z (𝟙 c.obj.obj.Z)) J
  have hu' : R.map (d.inv.app J) ≫ κ.inv.app J = 𝟙 _ := by
    simpa only [R, d, κ, κ₀, τ, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.comp_obj, Functor.id_obj, NatTrans.id_app,
      Category.assoc] using hu
  have hk : R.map (d.inv.app J) = κ.hom.app J := (Iso.comp_inv_eq_id (κ.app J)).1 hu'
  let : R.Faithful := Functor.Faithful.of_iso d.symm
  have he : e = d.inv.app J := R.map_injective (hm.symm.trans hk.symm)
  change e ≫ d.hom.app J = 𝟙 _
  rw [he, Iso.inv_hom_id_app]
  rfl

omit Λ in
private def StandardCoefficient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
(∃ (A : Type u) (_ : CommRing A) (_ : Finite A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        (∃ n : ℕ, (ℓ ^ n : A) = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
              (Profinite.padicSubfieldCondensedRing ℓ E.1)))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj Opposite
  Functor.LaxMonoidal Functor.OplaxMonoidal in
private noncomputable def liftCoefficientIso (A : Type) [TopologicalSpace A] [Ring A]
    [IsTopologicalRing A] :
    Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) where
  hom := ⟨{
    app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((ULift.ringEquiv.symm : A ≃+* ULift.{u} A).toRingHom.compLeftContinuous
        S.unop continuous_uliftUp).comp ULift.ringEquiv.toRingHom))
    naturality _ _ _ := by ext; rfl }⟩
  inv := ⟨{
    app S := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (((ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom.compLeftContinuous
        S.unop continuous_uliftDown).comp ULift.ringEquiv.toRingHom))
    naturality _ _ _ := by ext; rfl }⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

private theorem admissible_standard
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    StandardCoefficient Λ ℓ := by
  rcases hΛ with hA | hZ | hQ | hE | hO | hbar
  · rcases hA with ⟨A, hring, htop, hdisc, htopring, hfin, ⟨n, hn⟩, ⟨e⟩⟩
    let A' := ULift.{u} A
    let er := liftCoefficientIso.{u} A
    let er' := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
    have : IsMonHom er'.hom :=
      Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) er.hom
    refine Or.inl ⟨A', inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ⟨n, ?_⟩, ⟨e ≪≫ Mon.mkIso' er'⟩⟩
    apply ULift.ext
    change (ℓ ^ n : A) = 0
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hn (1 : A)
  · exact Or.inr (Or.inl hZ)
  · exact Or.inr (Or.inr (Or.inl hQ))
  · rcases hE with ⟨E, hE⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, Or.inr hE⟩)))
  · rcases hO with ⟨E, hE⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, Or.inl hE⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hbar)))

private theorem standardBoundaryVanishing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (hΛ : StandardCoefficient Λ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K ∧
      _root_.DerivedCategory.finiteTorAmplitude _ K) :
    IsZero ((upperStar Λ c.obj.obj.obj.i.closedComplement).mapDerivedCategory.obj
      ((lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory.obj K))) := by
  have hchar : ringChar k = p := ringChar.eq k p
  have : Fact (ringChar k).Prime := ⟨by
    rw [hchar]
    exact CharP.char_prime_of_ne_zero k (ne_of_gt hp)⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by rwa [hchar]⟩
  have : QuasiCompact c.obj.obj.obj.i := c.obj.obj.property
  have : QuasiCompact d.obj.obj.obj.i := d.obj.obj.property
  have : IsSchemeTheoreticallyDominant d.obj.obj.obj.i := d.property
  let cr : Compactification (𝟙 X ≫ c.obj.obj.obj.i) :=
    { Z := d.obj.obj.obj.Z
      i := d.obj.obj.obj.i
      g := r.hom.hom.hom.hom
      comm := by simpa only [Category.id_comp] using r.hom.hom.hom.i_hom.symm
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let bc : Compactification.BoundaryCompactification (𝟙 X ≫ c.obj.obj.obj.i) :=
    ⟨⟨cr, inferInstance⟩⟩
  have : bc.obj.obj.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hcomp := properOpenInterchange Λ (𝟙 X) c.obj.obj.obj.i bc ℓ k hΛ
  obtain ⟨m, hm, huniq, hmiso⟩ := hcomp.2 K
  have : IsIso m := hmiso (fun P hP hSP ↦ hSP K hK)
  let i := c.obj.obj.obj.i.closedComplement
  have hdis : Disjoint (Set.range c.obj.obj.obj.i.base) (Set.range i.base) := by
    dsimp only [i]
    rw [Scheme.Hom.range_closedComplement]
    exact disjoint_compl_right
  have hz := isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
    Λ c.obj.obj.obj.i i hdis ((lowerStar Λ (𝟙 X)).rightDerivedFunctor.obj K)
  have hz' := hz.of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm.app _)
  exact hz'.of_iso (((upperStar Λ i).mapDerivedCategory.mapIso (asIso m)).symm)

/-- Uniqueness, invertibility on Loc(Dctf), and identity/composition for the canonical
refinement maps. Uniqueness and coherence hold for arbitrary unbounded K.
Source: blueprint main-20261015, proposition-construction-independence-rf-shriek--7, clauses
(1)--(3) (blueprint: proposition-construction-independence-rf-shriek--7).

Lean realization: the standard coefficient cases of the closed-support calculation use the
existing proper/open interchange theorem. Only the all-continuous-map algebraic-closure
compatibility case on constructible sheaves in degree zero is retained separately. Bounded
truncation dévissage proves the remaining generator argument. A triangulated vanishing kernel
extends closed support to the localizing closure; open-closed detection then proves
invertibility. Identity and composition use explicit normalization of the canonical derived
compositor and hold independently of this generator lemma.

Proof, realizing the source's restriction, generator and coherence arguments:
1. The existing module direct-image identity supplies linearity and naturality of the
specified identity components. The proved open unit is invertible, and exact derived
adjunction gives its derived counterpart.
2. The cartesian derived counit for the open square gives an invertible mate. The
explicit adjunction comparison identifies this mate with refinementOpenRestriction.
Composing with the inverse open unit gives the specified theta on every unbounded K.
3. The open adjunction identifies the normalization equation with the assertion that
the adjoint of the comparison is theta inverse. Injectivity proves the uniqueness iff.
4. Apply compactification_localizing to j with compactification (jprime,h). It supplies
preservation of ambient sums whose vertices lie in Loc(Dctf). Closed inverse image is
a derived left adjoint, so its composite with Rh_*jprime_! preserves these sums as well.
5. For the standard coefficient cases, properOpenInterchange with p = identity and
compactification (jprime,h) is invertible on generators. Its source has zero closed
restriction by disjoint-support vanishing, so its target does too. For the separate
all-continuous-map algebraic-closure coefficient, use the named boundary lemma on
constructible sheaves in degree zero. The proved bounded truncation theorem extends
this to bounded constructible complexes by applying it to the triangulated kernel.
6. Intersect Loc(Dctf) with that kernel. The intersection contains the generators,
is replete, triangulated and closed under the required sums. The defining intersection
of all localizing subcategories containing Dctf therefore lies in this kernel.
7. Both source and target of the refinement map now have zero closed restriction.
Its open restriction is invertible by the normalization equation and the invertible
open units. The source-library derived open-closed detection theorem makes it invertible.
8. Normalize the canonical derived compositor by comparing derived counits through
rightDerived_ext. Derived exact whiskering and upperStarComp_assoc give restriction
mate pasting, including the equality transports in the specified compactification triangle.
9. The adjunction homEquiv and restriction pasting prove the canonical composition law.
For identity, the open counit on j_!K is invertible. Transporting it along the derived
identity makes the identity refinement invertible. Specializing composition to two
identity refinements and using the canonical derived compositor unit law gives the
required identity equation by cancellation and faithfulness of the identity direct image.
The last two steps require no boundedness or localizing-closure membership. -/
theorem localizingRefinement_coherence
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      ∀ b : (openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.obj K ⟶
        (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.obj
          ((openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory.obj K),
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.obj.i).unit.app K ≫
            (upperStar Λ c.obj.obj.obj.i).mapDerivedCategory.map b ≫
              (refinementTheta Λ r.hom K).hom = 𝟙 K ↔
          b = localizingRefinementMap Λ r.hom K) ∧
    (∀ (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingClosureProEtale Λ X K → IsIso (localizingRefinementMap Λ r.hom K)) ∧
    (∀ (c : Compactification.DenseBoundaryCompactification f)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingRefinementMap Λ (𝟙 c.obj) K ≫
          (refinementDerivedLowerStarId Λ c.obj.obj.obj.Z).hom.app
            ((openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.obj K) = 𝟙 _) ∧
    (∀ (c d e : Compactification.DenseBoundaryCompactification f)
      (r : d ⟶ c) (s : e ⟶ d)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingRefinementMap Λ (s ≫ r).hom K ≫
          (refinementDerivedLowerStarComp Λ s.hom.hom.hom.hom r.hom.hom.hom.hom).hom.app
            ((openImmersionLowerShriek Λ e.obj.obj.obj.i).mapDerivedCategory.obj K) =
        localizingRefinementMap Λ r.hom K ≫
          (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.map
            (localizingRefinementMap Λ s.hom K)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c d r K b
    exact CategoryTheory.adjoint_normalization_iff
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.obj.i)
      K _ (refinementTheta Λ r.hom K) b
  · intro c d r K hK
    have hchar : ringChar k = p := ringChar.eq k p
    have : Fact (ringChar k).Prime := ⟨by
      rw [hchar]
      exact CharP.char_prime_of_ne_zero k (ne_of_gt _hp)⟩
    have : Fact (ringChar k ≠ ℓ) := ⟨by rwa [hchar]⟩
    have : QuasiCompact c.obj.obj.obj.i := c.obj.obj.property
    have : QuasiCompact d.obj.obj.obj.i := d.obj.obj.property
    let i := c.obj.obj.obj.i.closedComplement
    let J := (openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory
    let R := (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor
    let V := (upperStar Λ i).mapDerivedCategory
    let F := J ⋙ R ⋙ V
    let : F.Additive := inferInstance
    let : F.CommShift ℤ := inferInstance
    let : F.IsTriangulated := inferInstance
    let S : ObjectProperty (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
      constantModelBoundedConstructible Λ X ⊓ fun L ↦ _root_.DerivedCategory.finiteTorAmplitude _ L
    have hloc := (ProEtale.localizingClosure_exists Λ X S).2.2.2.1
    let cr : Compactification c.obj.obj.obj.i :=
      { Z := d.obj.obj.obj.Z
        i := d.obj.obj.obj.i
        g := r.hom.hom.hom.hom
        comm := r.hom.hom.hom.i_hom.symm
        isProper := inferInstance
        isOpenImmersion := inferInstance }
    let bc : Compactification.BoundaryCompactification c.obj.obj.obj.i :=
      ⟨⟨cr, inferInstance⟩⟩
    have : CompactSpace c.obj.obj.obj.Z :=
      QuasiCompact.compactSpace_of_compactSpace (c.obj.obj.obj.Z ↘ Spec (.of k))
    have : QuasiSeparatedSpace c.obj.obj.obj.Z :=
      quasiSeparatedSpace_of_quasiSeparated (c.obj.obj.obj.Z ↘ Spec (.of k))
    have hsums := (compactification_localizing Λ ℓ k c.obj.obj.obj.i bc _hΛ).2.2.1
    let adj := (upperStarLowerStarAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction
    let : V.IsLeftAdjoint := adj.isLeftAdjoint
    have hz : IsZero (F.obj K) := by
      apply CategoryTheory.extend_zero S hloc F _ _ K hK
      · intro I L hL
        -- the sum is indexed by the morphism universe: lift its index to the universe of `hsums`
        have : PreservesColimit L (J ⋙ R) := by
          let e := Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I)
          have h' : PreservesColimit (e.functor ⋙ L) (J ⋙ R) :=
            hsums (ULift.{u + 2} I) (e.functor ⋙ L) (fun i ↦ hL (Equiv.ulift i))
          exact Functor.Final.preservesColimit_of_comp (F := e.functor)
        change PreservesColimit L ((J ⋙ R) ⋙ V)
        have : PreservesColimit (L ⋙ J ⋙ R) V :=
          adj.leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
        exact comp_preservesColimit (J ⋙ R) V
      · intro L hL
        exact standardBoundaryVanishing Λ ℓ k p _hp _hpℓ (admissible_standard Λ ℓ _hΛ)
          f c d r L hL
    have hij : IsCompl (Set.range i.base) (Set.range c.obj.obj.obj.i.base) := by
      dsimp only [i]
      rw [Scheme.Hom.range_closedComplement]
      exact isCompl_compl.symm
    apply (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl Λ i
      c.obj.obj.obj.i hij).isIso_of_pairFunctor (localizingRefinementMap Λ r.hom K)
    · apply (NatIso.isIso_map_iff
        (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.obj.i) _).2
      let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.obj.i
      let ρ := (refinementOpenRestriction Λ r.hom.hom.hom).app (J.obj K)
      have : IsIso ρ := by
        have := refinementOpenRestriction_isIso Λ r.hom
        dsimp only [ρ]
        infer_instance
      have he := localizingRefinementMap_normalized Λ r.hom K
      have : IsIso (a.unit.app K ≫
          (upperStar Λ c.obj.obj.obj.i).mapDerivedCategory.map
            (localizingRefinementMap Λ r.hom K) ≫ ρ) := by
        rw [he]
        infer_instance
      have : IsIso ((upperStar Λ c.obj.obj.obj.i).mapDerivedCategory.map
          (localizingRefinementMap Λ r.hom K) ≫ ρ) :=
        IsIso.of_isIso_comp_left (a.unit.app K) _
      exact IsIso.of_isIso_comp_right _ ρ
    · have hzsrc := isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
        Λ c.obj.obj.obj.i i hij.symm.disjoint K
      have hztgt := hz.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ i).app _)
      exact hzsrc.isIso hztgt _
  · intro c K
    exact localizingRefinementMap_id Λ c.obj K
  · intro c d e r s K
    exact localizingRefinementMap_comp Λ r.hom s.hom K

end AlgebraicGeometry.ProEtale.CondensedRing
