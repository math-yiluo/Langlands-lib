/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationShiftComposition
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorLimitModel

/-! # Tensor augmentation under normalized reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 2 and 4;
Stacks 07A4, 08J9, 099B and 099M (blueprint: lem-pod-reindexing-tensor-augmentation-square).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
  HasDerivedCategory.standard
attribute [local irreducible] integralCompletedTensor
  podOrdinaryReindex pullbackTensorIntegralTensorModel
  coefficientSequenceLimit integralComparisonDerivedSequencePullback
  podReindexingSystemTensor

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  SheafOfModules.instAbelian SheafOfModules.instCategory
attribute [local implicit_reducible] integralTowerHasDerivedCategory
  coefficientSequenceHasDerived coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived

private theorem augmentation_from_frame
    {C D B A : Type*} [Category* C] [Category* D] [Category* B] [Category* A]
    (q : PodTensorAugmentationFrame C D A B)
    (v : q.F.obj q.S ⟶ q.T) (t : q.F.obj q.CY ⟶ q.CX)
    (hred : q.P.map q.bY ≫ q.w₁ ≫ q.w₂ = q.a ≫ q.LX.map v ≫ q.bX)
    (hlim : q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map q.w₁ ≫ q.RX.map q.w₂ =
      t ≫ q.dX.hom) :
    q.F.map (q.adjY.unit.app q.S ≫ q.RY.map q.bY ≫ q.dY.inv) ≫ t =
      v ≫ q.adjX.unit.app q.T ≫ q.RX.map q.bX ≫ q.dX.inv := by
  have hlim' : q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map (q.w₁ ≫ q.w₂) = t ≫ q.dX.hom := by
    simpa only [q.RX.map_comp, Category.assoc] using hlim
  apply (cancel_mono q.dX.hom).1
  have hnat := q.δ.naturality q.bY
  dsimp only [Functor.comp_map] at hnat
  have hux := q.adjX.unit.naturality v
  dsimp only [Functor.id_map, Functor.comp_map] at hux
  calc
    _ = q.F.map (q.adjY.unit.app q.S) ≫ q.F.map (q.RY.map q.bY) ≫
        q.δ.app q.U ≫ q.RX.map (q.w₁ ≫ q.w₂) := by
      rw [Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      rw [← hlim']
      simp only [← q.F.map_comp_assoc, Iso.inv_hom_id, q.F.map_id, Category.id_comp]
    _ = q.F.map (q.adjY.unit.app q.S) ≫ q.δ.app (q.LY.obj q.S) ≫
        q.RX.map (q.P.map q.bY ≫ (q.w₁ ≫ q.w₂)) := by
      rw [q.RX.map_comp, ← Category.assoc (q.F.map (q.RY.map q.bY)), hnat]
      simp only [Functor.map_comp, Category.assoc]
    _ = (q.F.map (q.adjY.unit.app q.S) ≫ q.δ.app (q.LY.obj q.S) ≫ q.RX.map q.a) ≫
        q.RX.map (q.LX.map v) ≫ q.RX.map q.bX := by
      rw [hred]
      simp only [Functor.map_comp, Category.assoc]
    _ = v ≫ q.adjX.unit.app q.T ≫ q.RX.map q.bX := by
      rw [q.unit]
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ q.RX.map q.bX) hux.symm
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id,
        Category.comp_id]

section FixedAugmentation
attribute [local irreducible] podReindexCalculus

private theorem augmentation_fixed
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hT : PodCompletedTensorReindex.Laws l E g A T)
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g) :
    ∀ M L : sfIntegralConstructibleCategory l E Y,
      (podOrdinaryReindex l E g).map
          ((podReindexCalculus l E Y).adjunction.unit.app
              ((podReindexCalculus l E Y).integralClosed.tensor.obj (M.obj, L.obj)) ≫
            (coefficientSequenceLimit l E Y).map
              ((podReindexCalculus l E Y).reductionTensor.hom.app (M.obj, L.obj)) ≫
            (podReindexingTensorModel l E Y).inv.app (M.obj, L.obj)) ≫
          (T.tensor M L).hom =
        podReindexingIntegralTensorHom l E g c h M.obj L.obj ≫
          (podReindexCalculus l E X).adjunction.unit.app
            ((podReindexCalculus l E X).integralClosed.tensor.obj
              ((podOrdinaryReindex l E g).obj M.obj, (podOrdinaryReindex l E g).obj L.obj)) ≫
          (coefficientSequenceLimit l E X).map
            ((podReindexCalculus l E X).reductionTensor.hom.app
              ((podOrdinaryReindex l E g).obj M.obj, (podOrdinaryReindex l E g).obj L.obj)) ≫
          (podReindexingTensorModel l E X).inv.app
            ((podOrdinaryReindex l E g).obj M.obj, (podOrdinaryReindex l E g).obj L.obj) := by
  intro M L
  let q := podReindexingTensorFrame l E g A hA M.obj L.obj
  have hh := augmentation_from_frame q
    (podReindexingIntegralTensorHom l E g c h M.obj L.obj) (T.tensor M L).hom
    (podReindexing_reduction_tensor_square l E g A hA c h M.obj L.obj)
    (podReindexing_tensor_limit_model l E g A T hA hT M L)
  dsimp only [q, podReindexingTensorFrame, Functor.comp_obj, Functor.id_obj,
    Iso.app_inv] at hh
  exact hh

end FixedAugmentation

/-- Ordinary-to-completed tensor augmentation commutes with the two normalized
reindexing tensor maps. The parameter η is fixed by its displayed defining equation.
Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 099M
(blueprint: lem-pod-reindexing-tensor-augmentation-square).

Proof: take simultaneous flat-term K-flat representatives of M and L. The ordinary
reindexing tensor map sends each homogeneous x tensor y to Fx tensor Fy. Reduction
sends this generator to its two quotient reductions, and the completed tensor map
has exactly this formula by Generators and Model. The tensor augmentation is the
actual reduction adjunction unit, followed by reductionTensor and the normalized
Roos tensor comparison. The Unit law transports its first factor; the quotient
formulas transport its second factor. On both Roos product coordinates the two
composites are the same diagonal relabelling, by RoosFst and RoosSnd. Thus the
augmentation square commutes on representatives, including all quotient arrows.
The representative localizations and their naturality descend this equality to
M and L. The equality h only identifies the two projection-fixed presentations;
equality proofs give the same eqToIso by proof irrelevance. No completeness of
the ordinary tensor or finite Tor dimension is used. -/
theorem podReindexing_tensor_augmentation_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hT : PodCompletedTensorReindex.Laws l E g A T)
    (η : ∀ (W : Scheme.{u}) (M L : podReindexingDerived l E W none),
      (podReindexCalculus l E W).integralClosed.tensor.obj (M, L) ⟶
        (integralCompletedTensor l E W).obj (M, L))
    (hη : η = fun W M L ↦
      (podReindexCalculus l E W).adjunction.unit.app
        (@MonoidalCategoryStruct.tensorObj _ _
          (podReindexCalculus l E W).integralClosed.monoidal.toMonoidalCategoryStruct M L) ≫
      (coefficientSequenceLimit l E W).map
        ((podReindexCalculus l E W).reductionTensor.hom.app (M, L)) ≫
      (pullbackTensorIntegralTensorModel l E W).inv.app (M, L))
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g) :
    ∀ M L : sfIntegralConstructibleCategory l E Y,
      (podOrdinaryReindex l E g).map (η Y M.obj L.obj) ≫ (T.tensor M L).hom =
        (((eqToIso h).app
          ((podReindexCalculus l E Y).integralClosed.tensor.obj (M.obj, L.obj))).symm ≪≫
          c.tensor.app (M.obj, L.obj) ≪≫
          (podReindexCalculus l E X).integralClosed.tensor.mapIso
            (((eqToIso h).app M.obj).prod ((eqToIso h).app L.obj))).hom ≫
          η X ((podOrdinaryReindex l E g).obj M.obj)
            ((podOrdinaryReindex l E g).obj L.obj) := by
  intro M L
  have hc := augmentation_fixed l E g A T hA hT c h M L
  rw [podReindexingTensorModel_inv_app, podReindexingTensorModel_inv_app,
    podReindexingIntegralTensorHom_eq] at hc
  rw [congrFun (congrFun (congrFun hη Y) M.obj) L.obj,
    congrFun (congrFun (congrFun hη X) ((podOrdinaryReindex l E g).obj M.obj))
      ((podOrdinaryReindex l E g).obj L.obj)]
  dsimp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj] at hc ⊢
  exact hc

end WeilConjectures
