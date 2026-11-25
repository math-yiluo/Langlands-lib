/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.Algebra.Homology.RestrictedTowerResolution.RestrictedTowerResolutionAcyclicity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Resolution-normalized comparison for the quotient sequence projection

Source: Stacks 0D6E, 070I, 070K and 070Y; the coefficient-comparison paragraph of
`fix-prop-coherence.proof.md`
(blueprint: lem-pur-sequence-kinjective-comparison-shifts).

The constant-ring factorization has exact direct image `coefficientSequenceRestriction`
and second direct image `lim`. Thus the direct image of the supplied ringed projection
is their composite `push`. All module categories below are the recorded actual coefficient
categories, retaining the independent scheme and coefficient universes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.sequenceSmall WeilConjectures.SemilinearSections.sliceSmall
attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionDerivedExistence SheafOfModules.monoidalCategory
  HasDerivedCategory.standard
attribute [local instance high] HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceRestriction
  SheafOfModules.strictRingSystemAbelian

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [-instance] CategoryTheory.ringedToposCommRingForgetCompose
  CategoryTheory.ringedToposRingForgetCompose CategoryTheory.ringedToposAbelianForgetCompose

namespace WeilConjectures.SequenceKInjectiveComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : AlgebraicGeometry.Scheme.{t})

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def derivedUnit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
    (DerivedCategory.quotientCompQhIso _)).inv ≫
  (Functor.associator _ _ _).inv ≫
  (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
    DerivedCategory.Qh).inv ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (HomotopyCategory.quotient _ _) F.rightDerivedFunctorUnit ≫
  (Functor.associator _ _ _).inv ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
    F.rightDerivedFunctor).hom

private theorem derivedUnit_app
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    (derivedUnit F).app K = coefficientRightDerivedComparison F K := by
  dsimp only [derivedUnit, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app]
  change _ = coefficientRightDerivedComparison F K
  simp only [Category.id_comp]
  change (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
      DerivedCategory.Qh.map (𝟙 _) ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
          F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app K) = _
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  rfl

private theorem derivedUnit_commShift
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] : NatTrans.CommShift (derivedUnit F) ℤ := by
  have := CategoryTheory.canonical_unit_commShift F
  have : NatTrans.CommShift (DerivedCategory.quotientCompQhIso B).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift (F.mapHomotopyCategoryFactors (.up ℤ)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  dsimp only [derivedUnit]
  simp only [Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom]
  infer_instance

private def unitQNat
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app K := F.rightDerivedFunctorUnitQ K
  naturality _ _ f := Functor.rightDerivedFunctorUnitQ_naturality F f

private theorem unitQNat_shift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift (unitQNat F) ℤ := by
  have he : unitQNat F = derivedUnit F := by
    ext K
    exact (derivedUnit_app F K).symm
  rw [he]
  exact derivedUnit_commShift F

private theorem model_shift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (J : CochainComplex C ℤ) [J.IsKInjective] (r : ℤ) :
    (F.rightDerivedFunctorObjQIso (J⟦r⟧)).hom ≫
        DerivedCategory.Q.map (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app J) ≫
          (DerivedCategory.Q.commShiftIso r).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      F.rightDerivedFunctor.map ((DerivedCategory.Q.commShiftIso r).hom.app J) ≫
        (F.rightDerivedFunctor.commShiftIso r).hom.app (DerivedCategory.Q.obj J) ≫
          (F.rightDerivedFunctorObjQIso J).hom⟦r⟧' := by
  have : NatTrans.CommShift (unitQNat F) ℤ := unitQNat_shift F
  have h := NatTrans.shift_app_comm (unitQNat F) r J
  simp only [Functor.commShiftIso_comp_hom_app, unitQNat,
    Functor.rightDerivedFunctorUnitQ_eq] at h
  apply (cancel_epi (F.rightDerivedFunctorObjQIso (J⟦r⟧)).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  have hc : (F.rightDerivedFunctorObjQIso J).inv⟦r⟧' ≫
      (F.rightDerivedFunctorObjQIso J).hom⟦r⟧' = 𝟙 _ :=
    ((shiftFunctor (DerivedCategory D) r).mapIso (F.rightDerivedFunctorObjQIso J)).inv_hom_id
  have hx := congrArg (fun f ↦ f ≫ (F.rightDerivedFunctorObjQIso J).hom⟦r⟧') h
  simp only [Category.assoc, hc] at hx
  erw [Category.comp_id] at hx
  exact hx

section GenericComparison
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Localization, followed by the supplied replacement and its K-injective limit model.
Source: Stacks 070K and 070Y
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def comparisonIso (N : CochainComplex A ℤ)
    (J : CochainComplex B ℤ) [J.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v] :
    (F.mapDerivedCategory ⋙ G.rightDerivedFunctor).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj J) :=
  G.rightDerivedFunctor.mapIso (F.mapDerivedCategoryFactors.app N) ≪≫
    G.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map v)) ≪≫
      G.rightDerivedFunctorObjQIso J

/-- Supplied-replacement shift equation for exact restriction followed by an additive functor.
Source: Stacks 070K and 070Y
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def ReplacementShiftsFor : Prop :=
  ∀ (N : CochainComplex A ℤ) (J : CochainComplex B ℤ) [J.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v] (r : ℤ),
    (comparisonIso F G (N⟦r⟧) (J⟦r⟧)
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app N ≫ v⟦r⟧')).hom ≫
      DerivedCategory.Q.map (((G.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app J) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj J) =
    (F.mapDerivedCategory ⋙ G.rightDerivedFunctor).map
        ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
      ((F.mapDerivedCategory ⋙ G.rightDerivedFunctor).commShiftIso r).hom.app
        (DerivedCategory.Q.obj N) ≫ (comparisonIso F G N J v).hom⟦r⟧'

private theorem comparisonIso_shifts : ReplacementShiftsFor F G := by
  intro N J _ v _ r
  have hR := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom r N
  have hm := model_shift G J r
  dsimp only [comparisonIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, asIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [hm]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, Category.assoc] at hR ⊢
  rw [← G.rightDerivedFunctor.map_comp_assoc,
    ← G.rightDerivedFunctor.map_comp_assoc,
    ← G.rightDerivedFunctor.map_comp_assoc]
  have hs : F.mapDerivedCategoryFactors.hom.app (N⟦r⟧) ≫
      DerivedCategory.Q.map (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app N) ≫
      DerivedCategory.Q.map (v⟦r⟧') ≫ (DerivedCategory.Q.commShiftIso r).hom.app J =
    F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
      (F.mapDerivedCategory.commShiftIso r).hom.app (DerivedCategory.Q.obj N) ≫
      F.mapDerivedCategoryFactors.hom.app N⟦r⟧' ≫ (DerivedCategory.Q.map v)⟦r⟧' := by
    rw [DerivedCategory.Q.commShiftIso_hom_naturality]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ (DerivedCategory.Q.map v)⟦r⟧') hR.symm
  simp only [Category.assoc]
  rw [hs]
  simp only [Functor.map_comp, Functor.commShiftIso_hom_naturality_assoc, Category.assoc]

end GenericComparison

attribute [local irreducible] ReplacementShiftsFor comparisonIso
/-- Representative shift identities for two additive termwise functors.
Source: Stacks 070H, 070I, 070K
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def RepresentativeShiftsFor
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] : Prop :=
    (∀ (J J' : CochainComplex B ℤ)
    (j : J ⟶ J') (r i : ℤ),
      ((G.mapHomologicalComplex (.up ℤ)).map (j⟦r⟧')).f i =
        ((G.mapHomologicalComplex (.up ℤ)).map j).f (i + r)) ∧
  (∀ (J : CochainComplex B ℤ) (r i j : ℤ),
    ((G.mapHomologicalComplex (.up ℤ)).obj (J⟦r⟧)).d i j =
      r.negOnePow • ((G.mapHomologicalComplex (.up ℤ)).obj J).d (i + r) (j + r)) ∧
  (∀ (N : CochainComplex A ℤ)
    (J : CochainComplex B ℤ) [J.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v] (r : ℤ),
    (J⟦r⟧).IsKInjective ∧
      QuasiIso (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app N ≫ v⟦r⟧')) ∧
  ∀ (N I : CochainComplex A ℤ) [I.IsKInjective]
    (i : N ⟶ I) [QuasiIso i]
    (J : CochainComplex B ℤ) [J.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v]
    (β : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J),
    Nonempty (Homotopy ((F.mapHomologicalComplex (.up ℤ)).map i ≫ β) v) → ∀ r : ℤ,
    (I⟦r⟧).IsKInjective ∧ QuasiIso (i⟦r⟧') ∧
      Nonempty (Homotopy
        ((F.mapHomologicalComplex (.up ℤ)).map (i⟦r⟧') ≫
          ((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app I ≫ β⟦r⟧')
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app N ≫ v⟦r⟧'))

section GenericProperties
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Transport a localized morphism through exact restriction.
Source: Stacks 05RU
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def restrictedMapFor {N N' : CochainComplex A ℤ}
    (f : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N') :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj N) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj N') :=
  F.mapDerivedCategoryFactors.inv.app N ≫ F.mapDerivedCategory.map f ≫
    F.mapDerivedCategoryFactors.hom.app N'

/-- Generic Normalization predicate for an exact additive first factor.
Source: Stacks 070I, 070K, 070Y and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def NormalizationFor
    (RP : DerivedCategory A ⥤ DerivedCategory (C))
    (η : (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP) (κ : RP ≅ (F.mapDerivedCategory ⋙ G.rightDerivedFunctor)) : Prop :=
  (∀ N : CochainComplex (A) ℤ,
    η.app N ≫ κ.hom.app (DerivedCategory.Q.obj N) =
      coefficientRightDerivedComparison G ((F.mapHomologicalComplex (.up ℤ)).obj N) ≫
        (G.rightDerivedFunctor).map ((F.mapDerivedCategoryFactors).inv.app N)) ∧
  ∀ (I : CochainComplex (A) ℤ) [I.IsKInjective]
    (J : CochainComplex B ℤ) [J.IsKInjective]
    (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j],
    QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) ∧
      η.app I ≫ κ.hom.app (DerivedCategory.Q.obj I) ≫
        (comparisonIso F G I J j).hom =
          DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j)

/-- Generic DerivedNaturality predicate for an exact additive first factor.
Source: Stacks 070I, 070K, 070Y and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def DerivedNaturalityFor : Prop :=
  ∀ (N N' I I' : CochainComplex (A) ℤ)
    [I.IsKInjective] [I'.IsKInjective]
    (i : N ⟶ I) [QuasiIso i] (i' : N' ⟶ I') [QuasiIso i']
    (J J' : CochainComplex B ℤ)
    [J.IsKInjective] [J'.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v]
    (v' : (F.mapHomologicalComplex (.up ℤ)).obj N' ⟶ J') [QuasiIso v']
    (f : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N')
    (t : I ⟶ I') (s : J ⟶ J')
    (β : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    (β' : (F.mapHomologicalComplex (.up ℤ)).obj I' ⟶ J'),
    DerivedCategory.Q.map i ≫ DerivedCategory.Q.map t = f ≫ DerivedCategory.Q.map i' →
    DerivedCategory.Q.map v ≫ DerivedCategory.Q.map s =
      restrictedMapFor F f ≫ DerivedCategory.Q.map v' →
    Nonempty (Homotopy ((F.mapHomologicalComplex (.up ℤ)).map i ≫ β) v) →
    Nonempty (Homotopy ((F.mapHomologicalComplex (.up ℤ)).map i' ≫ β') v') →
    Nonempty (Homotopy (β ≫ s) ((F.mapHomologicalComplex (.up ℤ)).map t ≫ β')) ∧
      ((F.mapDerivedCategory ⋙ G.rightDerivedFunctor)).map f ≫ (comparisonIso F G N' J' v').hom =
        (comparisonIso F G N J v).hom ≫
          DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s)

/-- Generic ResolutionCocycle predicate for an exact additive first factor.
Source: Stacks 070I, 070K, 070Y and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def ResolutionCocycleFor : Prop :=
  ∀ (N : CochainComplex (A) ℤ)
    (J₀ J₁ J₂ : CochainComplex B ℤ)
    [J₀.IsKInjective] [J₁.IsKInjective] [J₂.IsKInjective]
    (v₀ : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J₀) [QuasiIso v₀]
    (v₁ : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J₁) [QuasiIso v₁]
    (v₂ : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J₂) [QuasiIso v₂]
    (s₀₁ : J₀ ⟶ J₁) (s₁₂ : J₁ ⟶ J₂) (s₀₂ : J₀ ⟶ J₂) (s₀₀ : J₀ ⟶ J₀),
    Nonempty (Homotopy (v₀ ≫ s₀₁) v₁) →
    Nonempty (Homotopy (v₁ ≫ s₁₂) v₂) →
    Nonempty (Homotopy (v₀ ≫ s₀₂) v₂) →
    Nonempty (Homotopy (v₀ ≫ s₀₀) v₀) →
    Nonempty (Homotopy (s₀₁ ≫ s₁₂) s₀₂) ∧ Nonempty (Homotopy s₀₀ (𝟙 J₀)) ∧
      (comparisonIso F G N J₀ v₀).hom ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s₀₁) =
          (comparisonIso F G N J₁ v₁).hom ∧
      DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s₀₁) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s₁₂) =
          DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s₀₂) ∧
      DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s₀₀) = 𝟙 _

/-- Generic SystemResolutionCocycle predicate for an exact additive first factor.
Source: Stacks 070I, 070K, 070Y and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def SystemResolutionCocycleFor : Prop :=
  ∀ (N I₀ I₁ I₂ : CochainComplex (A) ℤ)
    [I₀.IsKInjective] [I₁.IsKInjective] [I₂.IsKInjective]
    (i₀ : N ⟶ I₀) [QuasiIso i₀] (i₁ : N ⟶ I₁) [QuasiIso i₁]
    (i₂ : N ⟶ I₂) [QuasiIso i₂]
    (t₀₁ : I₀ ⟶ I₁) (t₁₂ : I₁ ⟶ I₂) (t₀₂ : I₀ ⟶ I₂) (t₀₀ : I₀ ⟶ I₀),
    Nonempty (Homotopy (i₀ ≫ t₀₁) i₁) → Nonempty (Homotopy (i₁ ≫ t₁₂) i₂) →
    Nonempty (Homotopy (i₀ ≫ t₀₂) i₂) → Nonempty (Homotopy (i₀ ≫ t₀₀) i₀) →
    Nonempty (Homotopy (t₀₁ ≫ t₁₂) t₀₂) ∧ Nonempty (Homotopy t₀₀ (𝟙 I₀)) ∧
      DerivedCategory.Q.map (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map t₀₁) ≫
        DerivedCategory.Q.map (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map t₁₂) =
          DerivedCategory.Q.map (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map t₀₂) ∧
      DerivedCategory.Q.map (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map t₀₀) = 𝟙 _

variable [Abelian.HasKInjectiveResolutions A]

end GenericProperties

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The actual termwise scalar restriction on cochain complexes.
Source: Stacks 0941 (blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def restrict : CochainComplex (coefficientSequenceModules l E W) ℤ ⥤
    CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ :=
  (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)

/-- Termwise inverse limit of the recorded constant-coefficient towers.
Source: Stacks 0941 (blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def limitComplex : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ ⥤
    CochainComplex (scalarReductionSource l E W) ℤ :=
  Functor.mapHomologicalComplex
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) (.up ℤ)

/-- The ordinary module direct image of the quotient projection, factored through `cA`.
Its first factor changes only scalars along the completion projections; the second
forms the actual limit cone. This fixes `a_* = U`, `g_* = lim`, and `p_* = g_* a_*`.
Source: Stacks 0D6E, 0941
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def push : coefficientSequenceModules l E W ⥤ scalarReductionSource l E W :=
  coefficientSequenceRestriction l E W ⋙
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)

/-- The factored direct image is additive.
Source: Stacks 0941
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
instance push_additive : (push l E W).Additive :=
  inferInstanceAs ((coefficientSequenceRestriction l E W ⋙
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)).Additive)

/-- The fixed exact-localization comparison for restriction, without choosing resolutions.
Source: Stacks 05RU, 0941
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def restrictionFactors :
    DerivedCategory.Q ⋙ coefficientSequenceDerivedRestriction l E W ≅
      restrict l E W ⋙ DerivedCategory.Q :=
  (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors

/-- The canonical comparison to total inverse limit on every tower complex.
Source: Stacks 070K, 070Y
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def limitUnit (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    DerivedCategory.Q.obj ((limitComplex l E W).obj J) ⟶
      (coefficientConstantTowerLimit l E W).obj (DerivedCategory.Q.obj J) :=
  coefficientRightDerivedComparison
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) J

attribute [local irreducible] restrictionFactors limitUnit

/-- Transport an arbitrary derived morphism through the exact localization comparison.
Source: Stacks 05RU (blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def restrictedMap {N N' : CochainComplex (coefficientSequenceModules l E W) ℤ}
    (f : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N') :
    DerivedCategory.Q.obj ((restrict l E W).obj N) ⟶
      DerivedCategory.Q.obj ((restrict l E W).obj N') :=
  (restrictionFactors l E W).inv.app N ≫
    (coefficientSequenceDerivedRestriction l E W).map f ≫
      (restrictionFactors l E W).hom.app N'

attribute [local irreducible] restrictedMap

/-- The composite total limit has the standard coherent cochain shifts.
Source: Stacks 070K (blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
instance totalLimitCommShift : (coefficientSequenceLimit l E W).CommShift ℤ :=
  inferInstanceAs (((coefficientSequenceRestriction l E W).mapDerivedCategory ⋙
    Functor.rightDerivedFunctor
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)).CommShift ℤ)

attribute [local irreducible] NormalizationFor
  DerivedNaturalityFor ResolutionCocycleFor SystemResolutionCocycleFor

/-- The normalization of the natural comparison at every K-injective system.
Source: Stacks 0D6E and 070Y
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def Normalization
    (RP : coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W))
    (η : (push l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP) (κ : RP ≅ coefficientSequenceLimit l E W) : Prop :=
  NormalizationFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) RP η κ

attribute [local irreducible] RepresentativeShiftsFor

attribute [local semireducible] coefficientSequenceCommRingSheaf

set_option backward.isDefEq.respectTransparency true in
open SheafOfModules in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def coefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l E W :=
  NatTrans.ofOpSequence (fun n ↦ completedIntegralCommRingProjectionUnrestricted l E W n)
    (by
      intro n
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map,
        coefficientSequenceCommRingSystem, Functor.ofOpSequence_obj]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map_injective
      change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app V =
        (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app V ≫
          (integralCoefficientSheafTransition l E W n).hom.app V
      have h := congrArg (fun k ↦ k.hom.app V)
        (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_add_right n 1)).op)
      simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
      exact h.symm)

private abbrev strictEquivalence :=
  (SheafOfModules.strictSystemSequenceEquivalence (coefficientSequenceCommRingSystem l E W)).symm

attribute [local irreducible] coefficientSequenceCommRingSheaf

end WeilConjectures.SequenceKInjectiveComparison
