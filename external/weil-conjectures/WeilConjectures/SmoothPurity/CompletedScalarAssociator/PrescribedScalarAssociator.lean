/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData

/-! # Associativity for prescribed scalar presentations

Source: Stacks Tags 06YY and 07A6; blueprint Proof (3).
(blueprint: lem-pur-prescribed-scalar-associator).

The presentations are supplied, so the comparison retains their actual universal counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open SheafOfModules.SuccessiveDerivedQuotient
namespace WeilConjectures.CompletedScalarAssociator

private def chosenPresentation
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    (h : type_of% (SheafOfModules.derivedChangeOfRingsIndependentCoefficients a)) :
    Presentation a :=
  { ordinary := h.choose
    obj_eq := h.choose_spec.choose
    map_eq := h.choose_spec.choose_spec.choose
    additive := h.choose_spec.choose_spec.choose_spec.choose
    derived := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose
    counit := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose
    universal := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.1 }

private def scalarPresentation
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) : Presentation a :=
  chosenPresentation a (SheafOfModules.derivedChangeOfRingsIndependentCoefficients a)

attribute [local irreducible] chosenPresentation

private theorem scalarCompData
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), Presentation a)
    {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (hc : a ≫ b = c) :
    ∃ (o : (p a).ordinary ⋙ (p b).ordinary ≅ (p c).ordinary)
      (d : (p a).derived ⋙ (p b).derived ≅ (p c).derived),
      (∀ M U s t x, (o.hom.app M).val.app U
        (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
        sectionTensor (p c) M U (t * b.hom.app U s) x) ∧
      (∀ P : CochainComplex (Modules R) ℤ,
        d.hom.app (DerivedCategory.Q.obj P) ≫
            (p c).counit.app ((HomotopyCategory.quotient _ _).obj P) =
          (p b).derived.map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
            (p b).counit.app ((HomotopyCategory.quotient _ _).obj
              (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app P)) := by
  subst c
  let D := fun {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) ↦
    Classical.choice (adjData_exists (p a))
  let A := fun {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) ↦ (D a).ordinary
  refine ⟨ordinaryComp p A a b, derivedComp p D a b, ?_, ?_⟩
  · intro M U s t x
    simpa only [mul_comm] using
      ordinaryComp_hom p A (fun a ↦ (D a).ordinary_unit) a b M U x s t
  · intro P
    exact derivedComp_representative p D a b ((HomotopyCategory.quotient _ _).obj P)

private theorem scalarComp_unique
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), Presentation a)
    {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T)
    (o o' : (p a).ordinary ⋙ (p b).ordinary ≅ (p c).ordinary)
    (ho : ∀ M U s t x, (o.hom.app M).val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
      sectionTensor (p c) M U (t * b.hom.app U s) x)
    (ho' : ∀ M U s t x, (o'.hom.app M).val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
      sectionTensor (p c) M U (t * b.hom.app U s) x) : o = o' := by
  let D := fun {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) ↦
    Classical.choice (adjData_exists (p a))
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((D b).ordinary.homEquiv _ _).injective
  apply ((D a).ordinary.homEquiv _ _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (o.hom.app M).val.app U
      (((D b).ordinary.unit.app _).val.app U
        (((D a).ordinary.unit.app M).val.app U x)) =
    (o'.hom.app M).val.app U
      (((D b).ordinary.unit.app _).val.app U
        (((D a).ordinary.unit.app M).val.app U x))
  simp only [(D a).ordinary_unit, (D b).ordinary_unit]
  exact (ho M U 1 1 x).trans (ho' M U 1 1 x).symm

private structure ScalarComposition
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    {R S T : Sheaf J CommRingCat.{u}} {a : R ⟶ S} {b : S ⟶ T} {c : R ⟶ T}
    (pa : Presentation a) (pb : Presentation b) (pc : Presentation c) where
  ordinary : pa.ordinary ⋙ pb.ordinary ≅ pc.ordinary
  derived : pa.derived ⋙ pb.derived ≅ pc.derived
  tensor : ∀ M U s t x, (ordinary.hom.app M).val.app U
    (sectionTensor pb (pa.ordinary.obj M) U t (sectionTensor pa M U s x)) =
    sectionTensor pc M U (t * b.hom.app U s) x
  representative : ∀ P : CochainComplex (Modules R) ℤ,
    @Eq ((pb.derived.obj (pa.derived.obj (DerivedCategory.Q.obj P))) ⟶
      DerivedCategory.Q.obj ((pc.ordinary.mapHomologicalComplex (.up ℤ)).obj P))
      (pb.derived.map (pa.counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
        pb.counit.app ((HomotopyCategory.quotient _ _).obj
          ((pa.ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P))
      (derived.hom.app (DerivedCategory.Q.obj P) ≫
        pc.counit.app ((HomotopyCategory.quotient _ _).obj P))
  unique : ∀ (o : pa.ordinary ⋙ pb.ordinary ≅ pc.ordinary),
    (∀ M U s t x, (o.hom.app M).val.app U
      (sectionTensor pb (pa.ordinary.obj M) U t (sectionTensor pa M U s x)) =
      sectionTensor pc M U (t * b.hom.app U s) x) → o = ordinary

private theorem scalarCompositionData
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), Presentation a)
    {R S T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T)
    (hc : a ≫ b = c) : Nonempty (ScalarComposition (p a) (p b) (p c)) := by
  obtain ⟨o, d, ho, hd⟩ := scalarCompData p a b c hc
  exact ⟨{
    ordinary := o
    derived := d
    tensor := ho
    representative := fun P ↦ (hd P).symm
    unique := fun o' ho' ↦ scalarComp_unique p a b c o' o ho' ho }⟩

/-- Prescribed ordinary and derived presentations admit their normalized associator.
Source: Stacks Tags 06YY and 07A6 (blueprint: lem-pur-prescribed-scalar-associator).
Proof: take the extension-restriction adjunction for each prescribed presentation.
Compose the ordinary adjunctions and their derived adjunctions, then use uniqueness
of left adjoints. The ordinary units insert one, so their comparison multiplies the
two scalar factors. The derived adjunction hom-comparison gives the displayed
universal-counit equation. Finally apply the two injective ordinary hom-equivalences:
the tensor formula at the two units determines every component uniquely. -/
theorem presentation_associator_exists
    {C : Type*} [Category C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    [∀ R : Sheaf J CommRingCat.{u}, HasDerivedCategory (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S), Presentation a)
    {R S T : Sheaf J CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T)
    (hc : a ≫ b = c) :
    ∃ (o : (p a).ordinary ⋙ (p b).ordinary ≅ (p c).ordinary)
      (d : (p a).derived ⋙ (p b).derived ≅ (p c).derived),
      (∀ M U s t x, (o.hom.app M).val.app U
        (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
        sectionTensor (p c) M U (t * b.hom.app U s) x) ∧
      (∀ P : CochainComplex (Modules R) ℤ,
        ((p a).derived ⋙ (p b).derived).map
            ((DerivedCategory.quotientCompQhIso (Modules R)).inv.app P) ≫
          (p b).derived.map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          (p b).counit.app ((HomotopyCategory.quotient _ _).obj
            (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          (DerivedCategory.quotientCompQhIso (Modules T)).hom.app
            (((p b).ordinary.mapHomologicalComplex (.up ℤ)).obj
              (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso o (.up ℤ)).hom.app P) =
        d.hom.app (DerivedCategory.Q.obj P) ≫
          (p c).derived.map ((DerivedCategory.quotientCompQhIso (Modules R)).inv.app P) ≫
          (p c).counit.app ((HomotopyCategory.quotient _ _).obj P) ≫
          (DerivedCategory.quotientCompQhIso (Modules T)).hom.app
            (((p c).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ (o' : (p a).ordinary ⋙ (p b).ordinary ≅ (p c).ordinary),
        (∀ M U s t x, (o'.hom.app M).val.app U
          (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
          sectionTensor (p c) M U (t * b.hom.app U s) x) → o' = o) := by
  obtain ⟨v⟩ := scalarCompositionData p a b c hc
  refine ⟨v.ordinary, v.derived, v.tensor, ?_, v.unique⟩
  intro P
  change ((p a).derived ⋙ (p b).derived).map (𝟙 _) ≫ _ ≫ _ ≫ 𝟙 _ ≫ _ =
    _ ≫ (p c).derived.map (𝟙 _) ≫ _ ≫ 𝟙 _
  erw [((p a).derived ⋙ (p b).derived).map_id, (p c).derived.map_id,
    Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id]
  exact v.representative P

end WeilConjectures.CompletedScalarAssociator
