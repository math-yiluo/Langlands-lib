/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingReductionTensorSquare
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCoherentTensorRoos
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Descent of the strict tensor limit model

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: stage3-pod-reindexing-tensor-limit-model-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] integralCompletedTensor integralCompletedTensorComparison
  podReindexCalculus HasDerivedCategory.standard
  integralOperationsTensorTowerFunctor sfIntegralConstructible

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory podOrdinaryReindex
attribute [local implicit_reducible] integralTowerHasDerivedCategory
  coefficientSequenceHasDerived coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem limitTensorComparison_app
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g) (hA : PodCompletionReindex.Laws l E g A)
    (M N : podReindexingDerived l E Y none) :
    let q := podReindexingTensorFrame l E g A hA M N
    HEq (podReindexingLimitTensorComparisonHom l E g A hA M N)
      (q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map q.w₁ ≫
        q.RX.map q.w₂ ≫ q.dX.inv) := by
  unfold podReindexingLimitTensorComparisonHom
  rfl

private theorem limitTensorComparison_naturality
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (A : PodCompletionReindex l E g)
    (hA : PodCompletionReindex.Laws l E g A)
    (M N M' N' : podReindexingDerived l E Y none)
    (f : M ⟶ M') (h : N ⟶ N') :
    (podOrdinaryReindex l E g).map
        ((integralCompletedTensor l E Y).map (Prod.mkHom f h)) ≫
        podReindexingLimitTensorComparisonHom l E g A hA M' N' =
      podReindexingLimitTensorComparisonHom l E g A hA M N ≫
        (integralCompletedTensor l E X).map
          (Prod.mkHom ((podOrdinaryReindex l E g).map f) ((podOrdinaryReindex l E g).map h)) := by
  unfold podReindexingLimitTensorComparisonHom
  dsimp only [podReindexingTensorFrame, Iso.app_hom, Iso.app_inv]
  have hdY := (podReindexingTensorModel l E Y).hom.naturality (Prod.mkHom f h)
  have hdX := (podReindexingTensorModel l E X).inv.naturality
    (Prod.mkHom ((podOrdinaryReindex l E g).map f) ((podOrdinaryReindex l E g).map h))
  have ha := (NatTrans.prod A.reduction.hom A.reduction.hom).naturality (Prod.mkHom f h)
  have hν := (podReindexingSystemTensor l E g).hom.naturality
    (Prod.mkHom ((podReindexCalculus l E Y).reduction.map f)
      ((podReindexCalculus l E Y).reduction.map h))
  have hδ := A.limit.hom.naturality
    ((podReindexCalculus l E Y).systemClosed.tensor.map
      (Prod.mkHom ((podReindexCalculus l E Y).reduction.map f)
        ((podReindexCalculus l E Y).reduction.map h)))
  dsimp only [Functor.comp_map, Functor.prod_map, NatTrans.prod] at hdY hdX ha hν hδ
  rw [← Functor.map_comp_assoc, hdY, Functor.map_comp_assoc]
  rw [reassoc_of% hδ]
  have hνR := congrArg (coefficientSequenceLimit l E X).map hν
  simp only [Functor.map_comp] at hνR
  conv_lhs => rhs; rhs; rw [reassoc_of% hνR]
  have haR := congrArg (fun k ↦ (coefficientSequenceLimit l E X).map
    ((podReindexCalculus l E X).systemClosed.tensor.map k)) ha
  simp only [Functor.map_comp] at haR
  conv_lhs => rhs; rhs; rhs; rw [reassoc_of% haR]
  simp only [Category.assoc]
  conv_lhs => rhs; rhs; rhs; rhs; rw [hdX]

/-- The localization factor with its good-representative endpoints recorded. -/
private def goodReindexFactors
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (podOrdinaryReindex l E g).obj (DerivedCategory.Q.obj P.obj) ≅
      DerivedCategory.Q.obj (((podGoodReindex l E g A).obj P).obj) := by
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  unfold podOrdinaryReindex podGoodReindex
  exact (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.app P.obj

private theorem frameFinish
    {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
    (q : PodTensorAugmentationFrame C D A B) (t : q.F.obj q.CY ⟶ q.CX)
    (h : q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map q.w₁ ≫
      q.RX.map q.w₂ ≫ q.dX.inv = t) :
    q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map (q.w₁ ≫ q.w₂) = t ≫ q.dX.hom := by
  have he := congrArg (fun f ↦ f ≫ q.dX.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp] using he

/--
The strict normalized tensor equation descends through the product of the two good
complex localizations. The hypotheses record the pure-tensor generator normalization,
the strict model equation and its naturality; the conclusion is the component equation
used by the parent limit-model lemma.

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08TC,
0941. Construct the natural coherent comparison. Its strict Roos normalization
and Model identify it with T.tensor on good representatives after cancelling the
target realization. Choose representatives of the constructible inputs, transport
constructibility across their isomorphisms, and use Naturality to transport this
component equality. Postcompose with the target tensor realization to get the frame
equation. STATEMENT-DISPUTED: the original signature omitted Generators. Simultaneously
negating T.tower and T.tensor preserves Model and Naturality, but changes the equation.
(blueprint: stage3-pod-reindexing-tensor-limit-model-descent).
-/
theorem podReindexing_tensor_limit_model_descent
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hGenerators : PodCompletedTensorReindex.Generators l E g A T)
    (_hModel : PodCompletedTensorReindex.Model l E g A T)
    (_hNaturality : PodCompletedTensorReindex.Naturality l E g A T)
    (M N : sfIntegralConstructibleCategory l E Y) :
    let q := podReindexingTensorFrame l E g A hA M.obj N.obj
    let t : q.F.obj q.CY ⟶ q.CX := (T.tensor M N).hom
    q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map (q.w₁ ≫ q.w₂) =
      t ≫ q.dX.hom := by
  classical
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  let κ := podReindexingLimitTensorComparisonHom l E g A hA
  have hrep (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
      (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj)) :
      κ (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj) =
        (T.tensor ⟨DerivedCategory.Q.obj P.obj, hP⟩
          ⟨DerivedCategory.Q.obj Q.obj, hQ⟩).hom := by
    have hs := podReindexing_tensor_roos_normalization l E g A T hA hGenerators P Q
    have hm := _hModel P Q hP hQ
    let e := (integralCompletedTensor l E X).mapIso
      (Iso.prod (goodReindexFactors l E g A P) (goodReindexFactors l E g A Q)) ≪≫
      (integralCompletedTensorComparison l E X).app
        ((podGoodReindex l E g A).obj P, (podGoodReindex l E g A).obj Q)
    apply (cancel_mono e.hom).1
    dsimp only [e, Iso.trans, Functor.mapIso, Iso.prod, Iso.app] at ⊢
    simpa only [κ, goodReindexFactors, id, podGoodReindex, Iso.app_hom,
      Category.assoc, podReindexingTensorFrame] using eq_of_heq (hs.trans hm)
  dsimp only [κ] at hrep
  let L := integralOperationsGoodLocalization l E Y
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  have : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E Y
  have : L.EssSurj := Localization.essSurj L W
  let P := L.objPreimage M.obj
  let Q := L.objPreimage N.obj
  let eM : DerivedCategory.Q.obj P.obj ≅ M.obj := L.objObjPreimageIso M.obj
  let eN : DerivedCategory.Q.obj Q.obj ≅ N.obj := L.objObjPreimageIso N.obj
  let MP : sfIntegralConstructibleCategory l E Y :=
    ⟨DerivedCategory.Q.obj P.obj,
      ObjectProperty.prop_of_iso (sfIntegralConstructible l E Y) eM.symm M.property⟩
  let NQ : sfIntegralConstructibleCategory l E Y :=
    ⟨DerivedCategory.Q.obj Q.obj,
      ObjectProperty.prop_of_iso (sfIntegralConstructible l E Y) eN.symm N.property⟩
  have hk : κ M.obj N.obj = (T.tensor M N).hom := by
    let e := (podOrdinaryReindex l E g).mapIso
      ((integralCompletedTensor l E Y).mapIso (Iso.prod eM eN))
    apply (cancel_epi e.hom).1
    dsimp only [e, Functor.mapIso, Iso.prod]
    rw [limitTensorComparison_naturality l E g A hA _ _ _ _ eM.hom eN.hom]
    rw [hrep P Q MP.property NQ.property]
    exact (_hNaturality MP NQ M N
      (ObjectProperty.homMk eM.hom) (ObjectProperty.homMk eN.hom)).symm
  exact frameFinish _ (T.tensor M N).hom
    ((eq_of_heq (limitTensorComparison_app l E g A hA M.obj N.obj)).symm.trans hk)

end WeilConjectures
