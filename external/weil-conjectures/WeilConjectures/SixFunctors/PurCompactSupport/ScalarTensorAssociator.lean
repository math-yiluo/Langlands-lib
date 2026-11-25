/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportScalarTensor
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarAssociatorConjugate
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
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement

/-! # Binary tensor compatibility of the scalar associator

Source: lem-coef-integral-finite-extension.proof.md, final paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

section AssociatorProof
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
open scoped MonoidalCategory
attribute [local instance 100000] coefficientSiteSmall coefficientRingSheafify
  coefficientAbSheafify coefficientAbLocallyBijective
attribute [local implicit_reducible]
  Functor.map₂HomologicalComplex pbcDerivedRestrict
attribute [local irreducible] scalarTensor scalarOrdinaryTensor scalarTensorTotal
  tensorComposition pbcComplexCounit pbcDerivedScalarAdjunction pbcScalarAdjunction
  CategoryTheory.presheafToSheaf CategoryTheory.Functor.leftAdjoint
  SheafOfModules.monoidalCategory SheafOfModules.tensorObjIsoSheafification
  AlgebraicGeometry.Scheme.reductionDerivedChange HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory

open SheafOfModules.SuccessiveDerivedQuotient
open AlgebraicGeometry.ProEtale in
private def ordinaryComposition {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ T) :
    pbcExtend φ ⋙ pbcExtend ψ ≅ pbcExtend (φ ≫ ψ) :=
  ordinaryComp (publishedPresentation X) (fun a ↦ (publishedData X a).ordinary) φ ψ

open AlgebraicGeometry.ProEtale in
private theorem ordinaryComposition_pure {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (M : pbcModules X R)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((ordinaryComposition φ ψ).hom.app M).val.app U
      (pbcTensorSection ψ _ U 1 (pbcTensorSection φ M U 1 x)) =
      pbcTensorSection (φ ≫ ψ) M U 1 x := by
  have h := ordinaryComp_hom (publishedPresentation X)
    (fun a ↦ (publishedData X a).ordinary)
    (fun a ↦ (publishedData X a).ordinary_unit) φ ψ M U x 1 1
  simp only [publishedTensor, map_one, one_mul] at h
  dsimp only [ordinaryComposition, publishedPresentation] at h ⊢
  with_unfolding_all exact h

open AlgebraicGeometry.ProEtale in
private theorem derivedComposition_eq {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ T) :
    tensorComposition φ ψ (φ ≫ ψ) rfl =
      publishedComp X φ ψ (φ ≫ ψ) rfl := by
  rw [publishedComp_eq]
  simp only [eqToIso_refl, Iso.trans_refl]
  unfold derivedComp
  rw [(publishedAdjData X φ (publishedData X φ)).2,
    (publishedAdjData X ψ (publishedData X ψ)).2,
    (publishedAdjData X (φ ≫ ψ) (publishedData X (φ ≫ ψ))).2,
    publishedRightComp X φ ψ]
  unfold tensorComposition
  rfl

open AlgebraicGeometry.ProEtale in
private theorem derivedComposition_representative {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (P : CochainComplex (pbcModules X R) ℤ) :
    (tensorComposition φ ψ (φ ≫ ψ) rfl).hom.app (DerivedCategory.Q.obj P) ≫
        pbcComplexCounit (φ ≫ ψ) P =
      (pbcDerivedExtend ψ).map (pbcComplexCounit φ P) ≫
        pbcComplexCounit ψ (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (ordinaryComposition φ ψ) (.up ℤ)).hom.app
            P) := by
  rw [derivedComposition_eq]
  have h := publishedRepresentative X φ ψ (φ ≫ ψ) rfl P
  have he : (Functor.mapHomologicalComplexCompIso (ordinaryComposition φ ψ) (.up ℤ)).hom.app
      P = reductionBalance X φ ψ (φ ≫ ψ) rfl P := by
    apply (reductionBalance_exists X φ ψ (φ ≫ ψ) rfl P).unique
    · refine ⟨by infer_instance, ?_⟩
      intro n U s r x
      have hh := ordinaryComp_hom (publishedPresentation X)
        (fun a ↦ (publishedData X a).ordinary)
        (fun a ↦ (publishedData X a).ordinary_unit) φ ψ (P.X n) U x r s
      rw [mul_comm] at hh
      simp only [publishedTensor] at hh
      dsimp only [ordinaryComposition, reductionTensorSection]
      with_unfolding_all exact hh
    · exact (reductionBalance_exists X φ ψ (φ ≫ ψ) rfl P).exists.choose_spec
  rw [he]
  unfold pbcComplexCounit
  exact h

private theorem scalarOrdinaryTensor_composition {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (M N : pbcModules X R) :
    (pbcExtend ψ).map (scalarOrdinaryTensor φ M N).hom ≫
        (scalarOrdinaryTensor ψ _ _).hom ≫
        ((proEtaleOrdinaryTensor X T).map ((ordinaryComposition φ ψ).hom.app M)).app _ ≫
        ((proEtaleOrdinaryTensor X T).obj _).map
          ((ordinaryComposition φ ψ).hom.app N) =
      (ordinaryComposition φ ψ).hom.app
          (((proEtaleOrdinaryTensor X R).obj M).obj N) ≫
        (scalarOrdinaryTensor (φ ≫ ψ) M N).hom := by
  apply ((pbcScalarAdjunction ψ).homEquiv _ _).injective
  apply ((pbcScalarAdjunction φ).homEquiv _ _).injective
  apply tensorPair_ext R M N
  intro U x y
  simp only [Adjunction.homEquiv_unit]
  change ((((proEtaleOrdinaryTensor X T).map
      ((ordinaryComposition φ ψ).hom.app M)).app _ ≫
      ((proEtaleOrdinaryTensor X T).obj _).map
        ((ordinaryComposition φ ψ).hom.app N)).val.app U)
    ((scalarOrdinaryTensor ψ _ _).hom.val.app U
      (((pbcExtend ψ).map (scalarOrdinaryTensor φ M N).hom).val.app U
        (((pbcScalarAdjunction ψ).unit.app _).val.app U
          (((pbcScalarAdjunction φ).unit.app _).val.app U
            (proEtaleTensorPair X R M N U x y))))) =
    (scalarOrdinaryTensor (φ ≫ ψ) M N).hom.val.app U
      (((ordinaryComposition φ ψ).hom.app _).val.app U
        (((pbcScalarAdjunction ψ).unit.app _).val.app U
          (((pbcScalarAdjunction φ).unit.app _).val.app U
            (proEtaleTensorPair X R M N U x y))))
  have hη (A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
      (a : A ⟶ B) (L : pbcModules X A) (V : X.ProEtᵒᵖ) (z : L.val.obj V) :
      ((pbcScalarAdjunction a).unit.app L).val.app V z =
        pbcTensorSection a L V 1 z :=
    by
      unfold pbcScalarAdjunction
      exact (pbcScalarAdjunction_exists a).exists.choose_spec L V z
  have hu {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
      (a : A ⟶ B) {L L' : pbcModules X A} (v : L ⟶ L')
      (V : X.ProEtᵒᵖ) (z : L.val.obj V) :
      ((pbcExtend a).map v).val.app V (pbcTensorSection a L V 1 z) =
        pbcTensorSection a L' V 1 (v.val.app V z) := by
    exact reductionTensor_map X a v V 1 z
  have hμ {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
      (a : A ⟶ B) (L H : pbcModules X A) (V : X.ProEtᵒᵖ)
      (z : L.val.obj V) (w : H.val.obj V) :
      (scalarOrdinaryTensor a L H).hom.val.app V
          (pbcTensorSection a _ V 1 (proEtaleTensorPair X A L H V z w)) =
        proEtaleTensorPair X B _ _ V
          (pbcTensorSection a L V 1 z) (pbcTensorSection a H V 1 w) := by
    unfold scalarOrdinaryTensor
    exact (scalarOrdinaryTensor_existsUnique a).exists.choose_spec L H V 1 z w
  with_unfolding_all
    rw [hη, hη, hu, hμ, hμ]
    have hm := tensorPair_map T ((ordinaryComposition φ ψ).hom.app M)
      ((ordinaryComposition φ ψ).hom.app N) U
      (pbcTensorSection ψ _ U 1 (pbcTensorSection φ M U 1 x))
      (pbcTensorSection ψ _ U 1 (pbcTensorSection φ N U 1 y))
    erw [hm]
    rw [ordinaryComposition_pure, ordinaryComposition_pure, ordinaryComposition_pure, hμ]

set_option linter.style.haveILetI false in
private theorem scalarTensorTotal_summand {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P Q : CochainComplex (pbcModules X R) ℤ) (a b n : ℤ) (h : a + b = n) :
    CochainComplex.ιMapBifunctor
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q)
        (proEtaleOrdinaryTensor X S) a b n h ≫ (scalarTensorTotal φ P Q).f n =
      (scalarOrdinaryTensor φ (P.X a) (Q.X b)).inv ≫
        (pbcExtend φ).map
          (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor X R) a b n h) := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  letI := proEtaleTensorPreadditive X R
  letI := proEtaleTensorPreadditive X S
  simp only [scalarTensorTotal, tensorPullbackTotal, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc]

private theorem scalarTensorTotal_composition {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (P Q : CochainComplex (pbcModules X R) ℤ) :
    HomologicalComplex.mapBifunctorMap
        ((Functor.mapHomologicalComplexCompIso (ordinaryComposition φ ψ) (.up ℤ)).hom.app P)
        ((Functor.mapHomologicalComplexCompIso (ordinaryComposition φ ψ) (.up ℤ)).hom.app Q)
        (proEtaleOrdinaryTensor X T) (.up ℤ) ≫ scalarTensorTotal (φ ≫ ψ) P Q =
      scalarTensorTotal ψ
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        ((pbcExtend ψ).mapHomologicalComplex (.up ℤ)).map (scalarTensorTotal φ P Q) ≫
        (Functor.mapHomologicalComplexCompIso (ordinaryComposition φ ψ) (.up ℤ)).hom.app
          (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor X R)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.monoidalCategory T
  let := proEtaleTensorPreadditive X R
  let := proEtaleTensorPreadditive X S
  let := proEtaleTensorPreadditive X T
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, Functor.comp_obj]
  rw [scalarTensorTotal_summand (φ ≫ ψ) P Q a b n hab,
    reassoc_of% scalarTensorTotal_summand ψ
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj Q) a b n hab]
  have hs := congrArg (pbcExtend ψ).map (scalarTensorTotal_summand φ P Q a b n hab)
  rw [Functor.map_comp, Functor.map_comp] at hs
  rw [reassoc_of% hs]
  have hn := (ordinaryComposition φ ψ).hom.naturality
    (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor X R) a b n hab)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.mapHomologicalComplexCompIso_hom_app_f]
  rw [hn]
  let e := (pbcExtend ψ).mapIso (scalarOrdinaryTensor φ (P.X a) (Q.X b)) ≪≫
    scalarOrdinaryTensor ψ ((pbcExtend φ).obj (P.X a)) ((pbcExtend φ).obj (Q.X b))
  let w := scalarOrdinaryTensor (φ ≫ ψ) (P.X a) (Q.X b)
  have hi : e.inv ≫ (ordinaryComposition φ ψ).hom.app
      (((proEtaleOrdinaryTensor X R).obj (P.X a)).obj (Q.X b)) =
      (((proEtaleOrdinaryTensor X T).map
        ((ordinaryComposition φ ψ).hom.app (P.X a))).app _ ≫
        ((proEtaleOrdinaryTensor X T).obj _).map
          ((ordinaryComposition φ ψ).hom.app (Q.X b))) ≫ w.inv := by
    apply (Iso.inv_comp_eq e).2
    rw [← Category.assoc]
    apply (Iso.eq_comp_inv w).2
    exact (scalarOrdinaryTensor_composition φ ψ (P.X a) (Q.X b)).symm
  simpa only [e, w, Iso.trans_inv, Functor.mapIso_inv, Category.assoc,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplex_obj_X, Functor.comp_obj] using
    congrArg (fun z ↦ z ≫ (pbcExtend (φ ≫ ψ)).map
      (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor X R) a b n hab)) hi.symm

private theorem scalarTensor_inverse_representative {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (r : ProEtaleTensorModel X R) (s : ProEtaleTensorModel X S)
    (P Q : CochainComplex (pbcModules X R) ℤ)
    (hp : proEtaleFlatRepresentatives X R P) (hq : proEtaleFlatRepresentatives X R Q) :
    (scalarTensor φ r s).inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (pbcDerivedExtend φ).map (r.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
        pbcComplexCounit φ (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor X R)) =
      s.tensor.map (Prod.mkHom (pbcComplexCounit φ P) (pbcComplexCounit φ Q)) ≫
        s.representative.inv.app
          (⟨_, scalar_preservesFlatRepresentatives φ P hp⟩,
            ⟨_, scalar_preservesFlatRepresentatives φ Q hq⟩) ≫
        DerivedCategory.Q.map (scalarTensorTotal φ P Q) := by
  have ht := scalarTensorTotal_isIso φ P Q
  have hm := (scalarTensor_existsUnique φ r s).exists.choose_spec P Q hp hq
  obtain ⟨hp', hq', hm⟩ := hm
  with_unfolding_all
    change (pbcDerivedExtend φ).map (r.representative.hom.app
        (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      (scalarTensor φ r s).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      s.tensor.map (Prod.mkHom (pbcComplexCounit φ P) (pbcComplexCounit φ Q)) = _ at hm
  apply (cancel_epi ((pbcDerivedExtend φ).map (r.representative.hom.app
    (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ (scalarTensor φ r s).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))).1
  dsimp only [Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app]
  rw [reassoc_of% hm]
  simp only [Iso.hom_inv_id_app_assoc, ← DerivedCategory.Q.map_comp,
    IsIso.inv_hom_id, DerivedCategory.Q.map_id, Category.comp_id]
  change (pbcDerivedExtend φ).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem scalarTensor_composite_inverse_representative {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ T)
    (r : ProEtaleTensorModel X R) (s : ProEtaleTensorModel X S)
    (t : ProEtaleTensorModel X T)
    (P Q : CochainComplex (pbcModules X R) ℤ)
    (hp : proEtaleFlatRepresentatives X R P) (hq : proEtaleFlatRepresentatives X R Q) :
    let F := (pbcExtend φ).mapHomologicalComplex (.up ℤ)
    let G := (pbcExtend ψ).mapHomologicalComplex (.up ℤ)
    let Tot := CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor X R)
    (scalarTensor ψ s t).inv.app
        ((pbcDerivedExtend φ).obj (DerivedCategory.Q.obj P),
          (pbcDerivedExtend φ).obj (DerivedCategory.Q.obj Q)) ≫
      (pbcDerivedExtend ψ).map ((scalarTensor φ r s).inv.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (pbcDerivedExtend ψ).map
        ((pbcDerivedExtend φ).map (r.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩))) ≫
      (pbcDerivedExtend ψ).map (pbcComplexCounit φ Tot) ≫
      pbcComplexCounit ψ (F.obj Tot) =
    t.tensor.map (Prod.mkHom
        ((pbcDerivedExtend ψ).map (pbcComplexCounit φ P) ≫ pbcComplexCounit ψ (F.obj P))
        ((pbcDerivedExtend ψ).map (pbcComplexCounit φ Q) ≫ pbcComplexCounit ψ (F.obj Q))) ≫
      t.representative.inv.app
        (⟨G.obj (F.obj P), scalar_preservesFlatRepresentatives ψ _
          (scalar_preservesFlatRepresentatives φ P hp)⟩,
         ⟨G.obj (F.obj Q), scalar_preservesFlatRepresentatives ψ _
          (scalar_preservesFlatRepresentatives φ Q hq)⟩) ≫
      DerivedCategory.Q.map (scalarTensorTotal ψ (F.obj P) (F.obj Q) ≫
        G.map (scalarTensorTotal φ P Q)) := by
  dsimp only
  let F : CochainComplex (pbcModules X R) ℤ ⥤ CochainComplex (pbcModules X S) ℤ :=
    (pbcExtend φ).mapHomologicalComplex (.up ℤ)
  let G : CochainComplex (pbcModules X S) ℤ ⥤ CochainComplex (pbcModules X T) ℤ :=
    (pbcExtend ψ).mapHomologicalComplex (.up ℤ)
  let Tot : CochainComplex (pbcModules X R) ℤ :=
    CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor X R)
  let ε := complexCounitNat (pbcExtend ψ) (pbcDerivedExtend ψ) (pbcExtensionCounit ψ)
  have hε (A : CochainComplex (pbcModules X S) ℤ) :
      ε.app A = pbcComplexCounit ψ A := by
    unfold pbcComplexCounit
    exact complexCounitNat_app _ _ _ A
  have hn := (scalarTensor ψ s t).inv.naturality
    (Prod.mkHom (pbcComplexCounit φ P) (pbcComplexCounit φ Q))
  change t.tensor.map (Prod.mkHom ((pbcDerivedExtend ψ).map (pbcComplexCounit φ P))
      ((pbcDerivedExtend ψ).map (pbcComplexCounit φ Q))) ≫
      (scalarTensor ψ s t).inv.app (DerivedCategory.Q.obj (F.obj P),
        DerivedCategory.Q.obj (F.obj Q)) =
    (scalarTensor ψ s t).inv.app _ ≫ (pbcDerivedExtend ψ).map
      (s.tensor.map (Prod.mkHom (pbcComplexCounit φ P) (pbcComplexCounit φ Q))) at hn
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [scalarTensor_inverse_representative φ r s P Q hp hq]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  have hnε := ε.naturality (scalarTensorTotal φ P Q)
  simp only [hε] at hnε
  change (pbcDerivedExtend ψ).map (DerivedCategory.Q.map (scalarTensorTotal φ P Q)) ≫
      pbcComplexCounit ψ (F.obj Tot) =
    pbcComplexCounit ψ (CochainComplex.mapBifunctor (F.obj P) (F.obj Q)
      (proEtaleOrdinaryTensor X S)) ≫
      DerivedCategory.Q.map (G.map (scalarTensorTotal φ P Q)) at hnε
  rw [hnε, reassoc_of% scalarTensor_inverse_representative ψ s t (F.obj P) (F.obj Q)
      (scalar_preservesFlatRepresentatives φ P hp)
      (scalar_preservesFlatRepresentatives φ Q hq)]
  rw [← t.tensor.map_comp_assoc]
  rfl

private theorem scalarTensor_associator_representatives {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ T)
    (r : ProEtaleTensorModel X R) (s : ProEtaleTensorModel X S)
    (t : ProEtaleTensorModel X T)
    (P Q : CochainComplex (pbcModules X R) ℤ)
    (hp : proEtaleFlatRepresentatives X R P) (hq : proEtaleFlatRepresentatives X R Q) :
    t.tensor.map (Prod.mkHom
        ((tensorComposition φ ψ (φ ≫ ψ) rfl).hom.app (DerivedCategory.Q.obj P))
        ((tensorComposition φ ψ (φ ≫ ψ) rfl).hom.app (DerivedCategory.Q.obj Q))) ≫
      (scalarTensor (φ ≫ ψ) r t).inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
    (scalarTensor ψ s t).inv.app
        ((pbcDerivedExtend φ).obj (DerivedCategory.Q.obj P),
          (pbcDerivedExtend φ).obj (DerivedCategory.Q.obj Q)) ≫
      (pbcDerivedExtend ψ).map ((scalarTensor φ r s).inv.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (tensorComposition φ ψ (φ ≫ ψ) rfl).hom.app
        (r.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  let F : CochainComplex (pbcModules X R) ℤ ⥤ CochainComplex (pbcModules X S) ℤ :=
    (pbcExtend φ).mapHomologicalComplex (.up ℤ)
  let G : CochainComplex (pbcModules X S) ℤ ⥤ CochainComplex (pbcModules X T) ℤ :=
    (pbcExtend ψ).mapHomologicalComplex (.up ℤ)
  let H : CochainComplex (pbcModules X R) ℤ ⥤ CochainComplex (pbcModules X T) ℤ :=
    (pbcExtend (φ ≫ ψ)).mapHomologicalComplex (.up ℤ)
  let δ := tensorComposition φ ψ (φ ≫ ψ) rfl
  let d := (Functor.mapHomologicalComplexCompIso (ordinaryComposition φ ψ) (.up ℤ)).hom
  let Tot : CochainComplex (pbcModules X R) ℤ :=
    CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor X R)
  let b (L : CochainComplex (pbcModules X R) ℤ) :=
    (pbcDerivedExtend ψ).map (pbcComplexCounit φ L) ≫ pbcComplexCounit ψ (F.obj L)
  let rGF := t.representative.app
    (⟨G.obj (F.obj P), scalar_preservesFlatRepresentatives ψ _
      (scalar_preservesFlatRepresentatives φ P hp)⟩,
     ⟨G.obj (F.obj Q), scalar_preservesFlatRepresentatives ψ _
      (scalar_preservesFlatRepresentatives φ Q hq)⟩)
  let rH := t.representative.app
    (⟨H.obj P, scalar_preservesFlatRepresentatives (φ ≫ ψ) P hp⟩,
     ⟨H.obj Q, scalar_preservesFlatRepresentatives (φ ≫ ψ) Q hq⟩)
  have hn := t.representative.inv.naturality
    (Prod.mkHom
      (ObjectProperty.homMk
        (X := ⟨G.obj (F.obj P), scalar_preservesFlatRepresentatives ψ _
          (scalar_preservesFlatRepresentatives φ P hp)⟩)
        (Y := ⟨H.obj P, scalar_preservesFlatRepresentatives (φ ≫ ψ) P hp⟩) (d.app P))
      (ObjectProperty.homMk
        (X := ⟨G.obj (F.obj Q), scalar_preservesFlatRepresentatives ψ _
          (scalar_preservesFlatRepresentatives φ Q hq)⟩)
        (Y := ⟨H.obj Q, scalar_preservesFlatRepresentatives (φ ≫ ψ) Q hq⟩) (d.app Q)))
  simp only [Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
    Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
    SheafOfModules.CanonicalTensorPullbackProof.tensorMap_factor] at hn
  change t.tensor.map (Prod.mkHom (DerivedCategory.Q.map (d.app P))
      (DerivedCategory.Q.map (d.app Q))) ≫ rH.inv =
    rGF.inv ≫ DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      (d.app P) (d.app Q) (proEtaleOrdinaryTensor X T) (.up ℤ)) at hn
  have hδ := δ.hom.naturality (r.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩))
  change (pbcDerivedExtend ψ).map ((pbcDerivedExtend φ).map
      (r.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩))) ≫
      δ.hom.app (DerivedCategory.Q.obj Tot) =
    δ.hom.app (r.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (pbcDerivedExtend (φ ≫ ψ)).map
        (r.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩)) at hδ
  have ht := scalarComplexCounit_isIso (φ ≫ ψ) Tot
    (tensorTotal_flatRepresentatives R P Q hp hq)
  let z := (pbcDerivedExtend (φ ≫ ψ)).mapIso
    (r.representative.app (⟨P, hp⟩, ⟨Q, hq⟩)).symm ≪≫
      @asIso _ _ _ _ (pbcComplexCounit (φ ≫ ψ) Tot) ht
  apply (cancel_mono z.hom).1
  simp only [z, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Category.assoc, asIso_hom]
  rw [← reassoc_of% hδ, derivedComposition_representative φ ψ Tot]
  rw [reassoc_of% scalarTensor_composite_inverse_representative φ ψ r s t P Q hp hq]
  rw [scalarTensor_inverse_representative (φ ≫ ψ) r t P Q hp hq]
  rw [← t.tensor.map_comp_assoc]
  change t.tensor.map (Prod.mkHom
      (δ.hom.app (DerivedCategory.Q.obj P) ≫ pbcComplexCounit (φ ≫ ψ) P)
      (δ.hom.app (DerivedCategory.Q.obj Q) ≫ pbcComplexCounit (φ ≫ ψ) Q)) ≫
      rH.inv ≫ DerivedCategory.Q.map (scalarTensorTotal (φ ≫ ψ) P Q) =
    t.tensor.map (Prod.mkHom (b P) (b Q)) ≫ rGF.inv ≫
      DerivedCategory.Q.map (scalarTensorTotal ψ (F.obj P) (F.obj Q) ≫
        G.map (scalarTensorTotal φ P Q)) ≫ DerivedCategory.Q.map (d.app Tot)
  rw [derivedComposition_representative φ ψ P, derivedComposition_representative φ ψ Q]
  simp only [← Category.assoc]
  change (t.tensor.map
      (Prod.mkHom (b P) (b Q) ≫
        Prod.mkHom (DerivedCategory.Q.map (d.app P))
          (DerivedCategory.Q.map (d.app Q))) ≫ rH.inv) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← DerivedCategory.Q.map_comp]
  exact congrArg (fun v ↦ t.tensor.map (Prod.mkHom (b P) (b Q)) ≫
    rGF.inv ≫ DerivedCategory.Q.map v) (scalarTensorTotal_composition φ ψ P Q)

private theorem scalarTensor_associator_aux {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (χ : R ⟶ T) (h : φ ≫ ψ = χ)
    (r : ProEtaleTensorModel X R) (s : ProEtaleTensorModel X S)
    (t : ProEtaleTensorModel X T) (K M : DerivedCategory (pbcModules X R)) :
    (pbcDerivedExtend ψ).map ((scalarTensor φ r s).hom.app (K, M)) ≫
        (scalarTensor ψ s t).hom.app
          ((pbcDerivedExtend φ).obj K, (pbcDerivedExtend φ).obj M) ≫
        t.tensor.map (Prod.mkHom ((tensorComposition φ ψ χ h).hom.app K)
          ((tensorComposition φ ψ χ h).hom.app M)) =
      (tensorComposition φ ψ χ h).hom.app (r.tensor.obj (K, M)) ≫
        (scalarTensor χ r t).hom.app (K, M) := by
  subst χ
  let δ := tensorComposition φ ψ (φ ≫ ψ) rfl
  let U : ((pbcDerivedExtend φ).prod (pbcDerivedExtend φ)) ⋙
      ((pbcDerivedExtend ψ).prod (pbcDerivedExtend ψ)) ⋙ t.tensor ⟶
      r.tensor ⋙ pbcDerivedExtend (φ ≫ ψ) :=
    Functor.whiskerRight (δ.hom.prod δ.hom) t.tensor ≫ (scalarTensor (φ ≫ ψ) r t).inv
  let V : ((pbcDerivedExtend φ).prod (pbcDerivedExtend φ)) ⋙
      ((pbcDerivedExtend ψ).prod (pbcDerivedExtend ψ)) ⋙ t.tensor ⟶
      r.tensor ⋙ pbcDerivedExtend (φ ≫ ψ) :=
    Functor.whiskerLeft ((pbcDerivedExtend φ).prod (pbcDerivedExtend φ))
      (scalarTensor ψ s t).inv ≫
      Functor.whiskerRight (scalarTensor φ r s).inv (pbcDerivedExtend ψ) ≫
      Functor.whiskerLeft r.tensor δ.hom
  have he : U = V := by
    obtain ⟨ff⟩ := tensorRepresentatives_fullyFaithful R T
    apply ff.map_injective
    apply NatTrans.ext
    funext Z
    obtain ⟨⟨P, hp⟩, ⟨Q, hq⟩⟩ := Z
    exact scalarTensor_associator_representatives φ ψ r s t P Q hp hq
  have hi := congrArg (fun z ↦ z.app (K, M)) he
  change t.tensor.map (Prod.mkHom (δ.hom.app K) (δ.hom.app M)) ≫
      (scalarTensor (φ ≫ ψ) r t).inv.app (K, M) =
    (scalarTensor ψ s t).inv.app ((pbcDerivedExtend φ).obj K, (pbcDerivedExtend φ).obj M) ≫
      (pbcDerivedExtend ψ).map ((scalarTensor φ r s).inv.app (K, M)) ≫
      δ.hom.app (r.tensor.obj (K, M)) at hi
  let e := (pbcDerivedExtend ψ).mapIso ((scalarTensor φ r s).app (K, M)) ≪≫
    (scalarTensor ψ s t).app ((pbcDerivedExtend φ).obj K, (pbcDerivedExtend φ).obj M)
  let w := (scalarTensor (φ ≫ ψ) r t).app (K, M)
  have hi' : t.tensor.map (Prod.mkHom (δ.hom.app K) (δ.hom.app M)) ≫ w.inv =
      e.inv ≫ δ.hom.app (r.tensor.obj (K, M)) := by
    simpa only [e, w, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hi
  have hf : e.hom ≫ t.tensor.map (Prod.mkHom (δ.hom.app K) (δ.hom.app M)) =
      δ.hom.app (r.tensor.obj (K, M)) ≫ w.hom := by
    apply (Iso.comp_inv_eq w).1
    rw [Category.assoc, hi', Iso.hom_inv_id_assoc]
  simpa only [e, w, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hf

end AssociatorProof

/-- The adjunction-normalized scalar associator respects the normalized binary
scalar/tensor comparisons. No internal Hom, completion, or dualizing objects occur.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-integral-finite-extension.proof.md, final paragraph.
(blueprint: lem-sf-scalar-tensor-associator)

Proof: choose flat-term K-flat representatives P and Q for K and M. Scalar extension
preserves these representatives. The scalarTensor normalization identifies its
map with the balanced tensor map on each total summand. The scalar associator is
normalized by the identity composition of restriction of scalars. Thus both sides
send a homogeneous coefficient tensor t tensor (s tensor (p tensor q)) to the same
balanced tensor over T. Balancing gives equality before sheafification, and the
signed total maps preserve bidegrees, hence introduce the same signs. Apply
sheafification and localization and the representative isomorphisms in r, s, t.
Naturality along the resolving isomorphisms gives the equation on K and M. The
argument includes zero objects, empty schemes and identity coefficient maps;
no flatness of the coefficient maps is required. -/
theorem scalarTensor_associator {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (χ : R ⟶ T) (h : φ ≫ ψ = χ)
    (r : ProEtaleTensorModel X R) (s : ProEtaleTensorModel X S)
    (t : ProEtaleTensorModel X T) (K M : DerivedCategory (pbcModules X R)) :
    (pbcDerivedExtend ψ).map ((scalarTensor φ r s).hom.app (K, M)) ≫
        (scalarTensor ψ s t).hom.app
          ((pbcDerivedExtend φ).obj K, (pbcDerivedExtend φ).obj M) ≫
        t.tensor.map (Prod.mkHom ((tensorComposition φ ψ χ h).hom.app K)
          ((tensorComposition φ ψ χ h).hom.app M)) =
      (tensorComposition φ ψ χ h).hom.app (r.tensor.obj (K, M)) ≫
        (scalarTensor χ r t).hom.app (K, M) :=
  scalarTensor_associator_aux φ ψ χ h r s t K M

end WeilConjectures.PurCompactSupport
