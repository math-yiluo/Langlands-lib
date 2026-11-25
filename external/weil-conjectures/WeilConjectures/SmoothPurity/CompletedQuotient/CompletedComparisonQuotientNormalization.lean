/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
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
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientNormalizationModels

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] pullbackTensorCalculus pullbackTensorIntegralTensorModel
  pullbackTensorIntegralPullbackModel pullbackTensorReductionModel
  tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] pullbackTensorReferenceTensor
  pullbackTensorReferencePullback integralOperationsGoodLocalization
  value expression IntegralCoherence.value coefficientSequenceInternalHom Pi.eval
attribute [local implicit_reducible] substituteInputs strictMap

private local instance (priority := 10000) sequenceMonoidal (W : Scheme.{u}) :
    MonoidalCategory (coefficientSequenceModules l E W) :=
  SheafOfModules.monoidalCategory (coefficientSequenceCommRingSheaf l E W)

private local instance (priority := 10000) complexMonoidal (W : Scheme.{u}) :
    MonoidalCategory (StrictQuotient.Complex l E W) :=
  HomologicalComplex.monoidalCategory (coefficientSequenceModules l E W) (.up ℤ)

private theorem reduction_naturality {W : Scheme.{u}}
    {K K' : DerivedCategory (scalarReductionSource l E W)}
    {A A' : coefficientSequenceDerived l E W}
    (β : K ⟶ (coefficientSequenceLimit l E W).obj A)
    (β' : K' ⟶ (coefficientSequenceLimit l E W).obj A')
    (k : K ⟶ K') (a : A ⟶ A')
    (hc : k ≫ β' = β ≫ (coefficientSequenceLimit l E W).map a) :
    (pullbackTensorCalculus l E W).reduction.map k ≫ reduction l E β' =
      reduction l E β ≫ a := by
  unfold reduction
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
    congrArg ((pullbackTensorCalculus l E W).reduction.map β ≫ ·)
      ((pullbackTensorCalculus l E W).adjunction.counit.naturality a)

private theorem tensor_substitution_naturality {W : Scheme.{u}}
    {K K' H H' : DerivedCategory (scalarReductionSource l E W)}
    {A A' B B' : StrictQuotient.Complex l E W}
    (hA : StrictQuotient.SystemGood l E A) (hA' : StrictQuotient.SystemGood l E A')
    (hB : StrictQuotient.SystemGood l E B) (hB' : StrictQuotient.SystemGood l E B')
    (βA : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (βA' : K' ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A'))
    (βB : H ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj B))
    (βB' : H' ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj B'))
    (k : K ⟶ K') (j : H ⟶ H') (a : A ⟶ A') (b : B ⟶ B')
    (ha : k ≫ βA' = βA ≫ (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map a))
    (hb : j ≫ βB' = βB ≫ (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map b)) :
    (integralCompletedTensor l E W).map (Prod.mkHom k j) ≫
        tensorSubstitution l E A' B' hA' hB' βA' βB' =
      tensorSubstitution l E A B hA hB βA βB ≫
        (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map
          ((coefficientTotalTensor.{u, u+1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom a b))) := by
  let R := (pullbackTensorCalculus l E W).reduction
  let L := coefficientSequenceLimit l E W
  let T := (pullbackTensorCalculus l E W).systemClosed.tensor
  have hd : Prod.mkHom (R.map k) (R.map j) ≫
        Prod.mkHom (reduction l E βA') (reduction l E βB') =
      Prod.mkHom (reduction l E βA) (reduction l E βB) ≫
        Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b) := by
    ext
    · exact reduction_naturality l E βA βA' k (DerivedCategory.Q.map a) ha
    · exact reduction_naturality l E βB βB' j (DerivedCategory.Q.map b) hb
  have ht : (integralCompletedTensor l E W).map (Prod.mkHom k j) ≫
      (pullbackTensorIntegralTensorModel l E W).hom.app (K', H') =
      (pullbackTensorIntegralTensorModel l E W).hom.app (K, H) ≫
        L.map (T.map (Prod.mkHom (R.map k) (R.map j))) :=
    (pullbackTensorIntegralTensorModel l E W).hom.naturality (Prod.mkHom k j)
  have hs : T.map (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) ≫
        (pullbackTensorSystemModel l E W A' B' hA'.1 hB'.1).inv =
      (pullbackTensorSystemModel l E W A B hA.1 hB.1).inv ≫
        DerivedCategory.Q.map ((coefficientTotalTensor.{u, u+1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom a b)) := by
    exact (pullbackTensorCalculus l E W).systemTensorModel.comparison.inv.naturality
      (Prod.mkHom
        (show (⟨A, hA.1⟩ : ObjectProperty.FullSubcategory
          (CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E W))) ⟶
          ⟨A', hA'.1⟩ from ⟨a⟩)
        (show (⟨B, hB.1⟩ : ObjectProperty.FullSubcategory
          (CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E W))) ⟶
          ⟨B', hB'.1⟩ from ⟨b⟩))
  unfold tensorSubstitution
  change _ ≫ _ ≫ L.map (T.map _) ≫ L.map _ =
    (_ ≫ L.map (T.map _) ≫ L.map _) ≫ L.map _
  simp only [Category.assoc]
  rw [← Category.assoc, ht]
  simp only [Category.assoc]
  rw [← L.map_comp_assoc, ← T.map_comp, hd, T.map_comp, L.map_comp]
  simp only [Category.assoc]
  rw [← L.map_comp, hs, L.map_comp]

private theorem pull_substitution_naturality {V W : Scheme.{u}} (g : V ⟶ W)
    {K K' : DerivedCategory (scalarReductionSource l E W)}
    {A A' : StrictQuotient.Complex l E W}
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (β' : K' ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A'))
    (k : K ⟶ K') (a : A ⟶ A')
    (hc : k ≫ β' = β ≫ (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map a)) :
    (integralDerivedPullback l E g).map k ≫ pullSubstitution l E g A' β' =
      pullSubstitution l E g A β ≫ (coefficientSequenceLimit l E V).map
        (DerivedCategory.Q.map ((IntegralCoherence.pull l E g).map a)) := by
  let L := coefficientSequenceLimit l E V
  let F := pullbackTensorSequenceDerived l E g
  let e : DerivedCategory.Q ⋙ F ≅
      (IntegralCoherence.pull l E g) ⋙ DerivedCategory.Q :=
    (pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (pullBridge l E g) DerivedCategory.Q
  have he := e.hom.naturality a
  dsimp only [Functor.comp_map] at he
  have hd := reduction_naturality l E β β' k (DerivedCategory.Q.map a) hc
  have ht : (integralDerivedPullback l E g).map k ≫
      (pullbackTensorIntegralPullbackModel l E g).hom.app K' =
      (pullbackTensorIntegralPullbackModel l E g).hom.app K ≫
        L.map (F.map ((pullbackTensorCalculus l E W).reduction.map k)) :=
    (pullbackTensorIntegralPullbackModel l E g).hom.naturality k
  unfold pullSubstitution
  change _ ≫ _ ≫ L.map (F.map _) ≫ L.map (e.hom.app A') =
    (_ ≫ L.map (F.map _) ≫ L.map (e.hom.app A)) ≫ L.map _
  simp only [Category.assoc]
  rw [← Category.assoc, ht]
  simp only [Category.assoc]
  rw [← L.map_comp_assoc, ← F.map_comp, hd, F.map_comp, L.map_comp]
  simp only [Category.assoc]
  rw [← L.map_comp, he, L.map_comp]

private theorem substitute_inputs_naturality
    {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (N N' : Fin 3 → StrictQuotient.Complex l E Y)
    (M M' : Fin 3 → DerivedCategory (scalarReductionSource l E Y))
    (β : ∀ i : Fin 3, M i ⟶ (coefficientSequenceLimit l E Y).obj
      (DerivedCategory.Q.obj (N i)))
    (β' : ∀ i : Fin 3, M' i ⟶ (coefficientSequenceLimit l E Y).obj
      (DerivedCategory.Q.obj (N' i)))
    (good : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l E (strictValue l E N A))
    (good' : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l E (strictValue l E N' A))
    (a : ∀ i, N i ⟶ N' i) (v : ∀ i, M i ⟶ M' i)
    (hc : ∀ i, v i ≫ β' i = β i ≫
      (coefficientSequenceLimit l E Y).map (DerivedCategory.Q.map (a i)))
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :
    (value l E A).map v ≫ substituteInputs l E N' M' β' good' A =
      substituteInputs l E N M β good A ≫
        (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map (strictMap l E a A)) := by
  induction A with
  | input i => simpa only [value, strictValue, expression, IntegralCoherence.value,
      substituteInputs, strictMap, Pi.eval_map, Pi.eval_obj] using hc i
  | unitY =>
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ (coefficientSequenceLimit l E Y).map
        (DerivedCategory.Q.map (𝟙 (HomologicalComplex.tensorUnit
          (coefficientSequenceModules l E Y) (.up ℤ))))
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  | unitX =>
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ (coefficientSequenceLimit l E X).map
        (DerivedCategory.Q.map (𝟙 (HomologicalComplex.tensorUnit
          (coefficientSequenceModules l E X) (.up ℤ))))
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  | unitZ =>
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ (coefficientSequenceLimit l E Z).map
        (DerivedCategory.Q.map (𝟙 (HomologicalComplex.tensorUnit
          (coefficientSequenceModules l E Z) (.up ℤ))))
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  | tensor A B hA hB =>
      have ht := tensor_substitution_naturality l E (good A) (good' A) (good B) (good' B)
        _ _ _ _ _ _ _ _ hA hB
      rw [RingedDerivedNative.totalTensor_map_eq.{u+1, u, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology _))
        (coefficientSequenceCommRingSheaf l E _) _ _ _ _ _ _] at ht
      dsimp only [value, strictValue, expression, IntegralCoherence.value,
        substituteInputs, strictMap, Functor.comp_map, Functor.prod'_map,
        Functor.comp_obj, Functor.prod'_obj]
      dsimp only [StrictQuotient.total, coefficientTotalTensor,
        HomologicalComplex.monoidalCategory, CategoryTheory.Monoidal.induced,
        HomologicalComplex.monoidalCategoryStruct] at ht ⊢
      exact ht
  | pullF A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value,
        substituteInputs, strictMap, Functor.comp_map]
      exact pull_substitution_naturality l E f _ _ _ _ hA
  | pullH A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value,
        substituteInputs, strictMap, Functor.comp_map]
      exact pull_substitution_naturality l E h _ _ _ _ hA
  | pullHF A hA =>
      dsimp only [value, strictValue, expression, IntegralCoherence.value,
        substituteInputs, strictMap, Functor.comp_map]
      exact pull_substitution_naturality l E (h ≫ f) _ _ _ _ hA

private theorem substitution_naturality {Z X Y : Scheme.{u}} {h : Z ⟶ X} {f : X ⟶ Y}
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P) : NaturalSubstitution l E M P φ good := by
  unfold NaturalSubstitution
  intro M' P' φ' good' a v comm W A
  unfold substitution
  apply substitute_inputs_naturality
  intro i
  let L := coefficientSequenceLimit l E Y
  let R := (pullbackTensorCalculus l E Y).reduction
  let e := pullbackTensorReductionModel l E Y
  have hφ : v i ≫ (φ' i).inv = (φ i).inv ≫ DerivedCategory.Q.map (a i) := by
    apply (cancel_mono (φ' i).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, comm i,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have he : R.map (DerivedCategory.Q.map (a i)) ≫ e.hom.app (P' i) =
      e.hom.app (P i) ≫ DerivedCategory.Q.map
        (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).map
          (a i)) := by
    exact e.hom.naturality (show P i ⟶ P' i from ⟨a i⟩)
  change v i ≫ (pullbackTensorCalculus l E Y).adjunction.unit.app (M' i).obj ≫
      L.map (R.map (φ' i).inv ≫ e.hom.app (P' i)) =
    ((pullbackTensorCalculus l E Y).adjunction.unit.app (M i).obj ≫
      L.map (R.map (φ i).inv ≫ e.hom.app (P i))) ≫ L.map _
  rw [← Category.assoc, ← (pullbackTensorCalculus l E Y).adjunction.unit_naturality,
    Category.assoc, ← L.map_comp, ← R.map_comp_assoc, hφ, R.map_comp_assoc, he,
    ← Category.assoc, L.map_comp, Category.assoc]

set_option linter.unusedVariables false in
/-- Quotient normalization and recursive substitution.
Source: realization proof step 1 and representative naturality in step 3;
Stacks 07A2, 0G7E and 0941
(blueprint: lem-pur-completed-comparison-quotient-normalization).

Proof: use the ordinary quotient tower of each prescribed representative. The
ordinary evaluation adjunction identifies its levels and every quotient transition.
K-flatness and flat terms survive reduction; the normalized quotient adjoints are
the balanced maps. Induct on the expression: units are flat K-flat normalized,
tensor preserves these properties, and constant-coefficient inverse image does too.
At a leaf, derived completeness makes the actual reconstruction unit invertible.
Tensor and inverse-image steps use the primitive counit comparisons, with the
normalized effective counit, so both substitution and its coherent reduction are
invertible. The reduction model and evaluation adjunction give the stated
presentation. Naturality holds at leaves by the reconstruction unit and the
reduction-model naturality. Induction, primitive naturality and functoriality of
tensor and inverse image prove it at each remaining constructor. All calculations
are in the category of whole coefficient systems before evaluation. -/
theorem completedComparisonQuotientNormalization
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    :
    ∃ (good : GoodExpressions l E h f P)
      (invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
        IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A)),
    (∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      (∀ n : ℕ, StrictQuotient.Good l E
        (strictValue l E (fun i ↦ quotient l E (P i).obj) A) n) ∧
      IsNormalizedCoefficientSequence l E W
        (DerivedCategory.Q.obj (strictValue l E (fun i ↦ quotient l E (P i).obj) A)) ∧
      IsIso (reduction l E (substitution l E P (fun i ↦ (M i).obj) φ good A))) ∧
    (∀ i : Fin 3, CoefficientReductionPresentation l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction
      (P i).obj (P i).property.1 (quotient l E (P i).obj)
      ((pullbackTensorReductionModel l E Y).app (P i))
      (fun n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app (P i).obj).symm)) ∧
    NaturalSubstitution l E M P φ good := by
  obtain ⟨good, invertible, normalized, presentation⟩ :=
    completedComparisonQuotientModels l E h f M P φ
  exact ⟨good, invertible, normalized, presentation, substitution_naturality l E M P φ good⟩

end WeilConjectures.CompletedQuotient
