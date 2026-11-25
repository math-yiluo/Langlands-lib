/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionDescentData
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Completed tensor square for scalar/reindexing transitions

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-tensor-mixed-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] podTensorReindexAdditive podTensorScalarZero podTensorMixedLeftZero
    podTensorMixedRightZero
  podTensorReindexLimits podTensorReindexColimits
attribute [local irreducible] integralCompletedTensor integralOrdinaryScalar
  integralOperationsTensorTowerFunctor scalarTensorChain scalarTensorOrdinary
  integralOperationsRoos completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted coefficientTotalTensor SheafOfModules.monoidalCategory
attribute [local implicit_reducible] podOrdinaryReindex podGoodReindex
  integralOperationsGoodLocalization integralOperationsTensorComplexFunctor
  integralOperationsRoosFunctor integralOperationsTensorOnGood
  scalarReductionSourceDerived integralTowerHasDerivedCategory
  integralOperationsCommHasDerivedCategory
  podTensorScalarGoodFunctor podTensorScalarGoodComparison podTensorReindexGoodComparison
  podTensorGoodConstructibleLocalization
  podTensorGoodConstructible podTensorMixedTensorIso podTensorGoodCoefficientTransition
  podTensorTensorReindexDerivedChain
  podTensorTensorScalarDerivedChain podTensorTensorMixedDerivedChain

private theorem pasteNormalization
    {C D V : Type*} [Category* C] [Category* D] [Category* V]
    (F : C ⥤ D) (U : V ⥤ D)
    {A B C₁ C₂ C₃ : C} {P Q R : V} {Z : D}
    (a : A ⟶ B) (b : B ⟶ C₃) (c : A ⟶ C₁) (f : C₁ ⟶ C₂)
    (r : C₂ ⟶ C₃) (t : F.obj C₁ ⟶ U.obj P) (t' : F.obj C₂ ⟶ U.obj Q)
    (j : P ⟶ Q) (j' : Q ⟶ R) (z : U.obj R ⟶ Z) (rest : F.obj C₃ ⟶ Z)
    (hs : a ≫ b = c ≫ f ≫ r)
    (ht : F.map r ≫ rest = t' ≫ U.map j' ≫ z)
    (hn : F.map f ≫ t' = t ≫ U.map j) :
    F.map a ≫ F.map b ≫ rest = F.map c ≫ t ≫ U.map (j ≫ j') ≫ z := by
  rw [← F.map_comp_assoc, hs]
  simp only [F.map_comp, U.map_comp, Category.assoc]
  rw [ht, ← Category.assoc (F.map f), hn]
  simp only [Category.assoc]

/-- A representative step of the scalar/reindexing tensor descent.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 05RU, 0941
(blueprint: lem-pod-tensor-mixed-normalization).
Proof: Apply the scalar normalization on the source. Scalar localization factors preserve
    constructibility. Apply the target-field tensor Model law, and use tensor naturality to move
    both scalar factors. Paste these three equalities. -/
theorem podTensorMixedRepresentativeNormalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
    (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj)) :
    (integralOrdinaryDerivedScalar l E L ι Y ⋙ podOrdinaryReindex l L g).map
        ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
      podTensorTensorMixedDerivedChain l E g L ι D' T' P Q =
    (podOrdinaryReindex l L g).map
        ((scalarTensorOrdinary l E L ι Y).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
      (T'.tensor ⟨_, S.sourceConstructible ⟨_, hP⟩⟩
        ⟨_, S.sourceConstructible ⟨_, hQ⟩⟩).hom ≫
      (integralCompletedTensor l L X).map
        (Prod.mkHom
          ((podOrdinaryReindex l L g).map
              ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj) ≫
            (isoReductionIntegralInverse l L g).mapDerivedCategoryFactors.hom.app
              ((podTensorScalarGoodFunctor l E L ι Y).obj P).obj)
          ((podOrdinaryReindex l L g).map
              ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app Q.obj) ≫
            (isoReductionIntegralInverse l L g).mapDerivedCategoryFactors.hom.app
              ((podTensorScalarGoodFunctor l E L ι Y).obj Q).obj)) ≫
      (integralCompletedTensorComparison l L X).hom.app
        ((podGoodReindex l L g D').obj ((podTensorScalarGoodFunctor l E L ι Y).obj P),
          (podGoodReindex l L g D').obj ((podTensorScalarGoodFunctor l E L ι Y).obj Q)) := by
  let P' := (podTensorScalarGoodFunctor l E L ι Y).obj P
  let Q' := (podTensorScalarGoodFunctor l E L ι Y).obj Q
  let p := (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.app P.obj
  let q := (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.app Q.obj
  have hp : sfIntegralConstructible l L Y (DerivedCategory.Q.obj P'.obj) :=
    (sfIntegralConstructible l L Y).prop_of_iso p (S.sourceConstructible ⟨_, hP⟩)
  have hq : sfIntegralConstructible l L Y (DerivedCategory.Q.obj Q'.obj) :=
    (sfIntegralConstructible l L Y).prop_of_iso q (S.sourceConstructible ⟨_, hQ⟩)
  have hs : scalarTensorOrdinaryNormalization l E L ι Y
      (scalarTensorOrdinary l E L ι Y) := by
    unfold scalarTensorOrdinary
    exact (scalarTensorOrdinary_existsUnique l E L ι Y).exists.choose_spec
  have ht := eq_of_heq (_hT'.2.2.2.2.1 P' Q' hp hq)
  have hn := _hT'.2.2.2.1 ⟨_, S.sourceConstructible ⟨_, hP⟩⟩
    ⟨_, S.sourceConstructible ⟨_, hQ⟩⟩ ⟨_, hp⟩ ⟨_, hq⟩
    (ObjectProperty.homMk p.hom) (ObjectProperty.homMk q.hom)
  have hh := pasteNormalization (podOrdinaryReindex l L g) (integralCompletedTensor l L X)
    _ _ _ _ _ _ _ _ _ _ _ (hs P Q) ht hn
  dsimp only [podTensorTensorMixedDerivedChain, podTensorTensorReindexDerivedChain,
    podTensorTensorScalarDerivedChain, Functor.comp_map, Functor.comp_obj,
    P', Q', p, q, Iso.app_hom, ObjectProperty.homMk_hom,
    integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    podReindexTensorChain, Functor.prod_obj, ObjectProperty.ι_obj] at hh ⊢
  simpa only [prod_comp, Functor.comp_map, Category.assoc] using hh

end WeilConjectures
