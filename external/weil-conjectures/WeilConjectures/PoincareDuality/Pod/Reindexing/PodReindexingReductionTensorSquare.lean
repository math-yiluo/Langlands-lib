/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingReductionTensorSquareDescent

/-! # Coherent reduction of the normalized ordinary reindexing tensor comparison

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing tensor realization, displayed in the reindexing calculus.
Source: Stacks 07A4 and 0941
(blueprint: lem-pod-reindexing-tensor-limit-model). -/
@[irreducible] def podReindexingTensorModel (W : Scheme.{u}) :
    integralCompletedTensor l E W ≅
      (podReindexCalculus l E W).reduction.prod
        (podReindexCalculus l E W).reduction ⋙
          (podReindexCalculus l E W).systemClosed.tensor ⋙ coefficientSequenceLimit l E W :=
  pullbackTensorIntegralTensorModel l E W

/-- The wrapper changes only the displayed presentation of the tensor realization.
Source: Stacks 07A4 and 0941
(blueprint: lem-pod-reindexing-tensor-limit-model). -/
theorem podReindexingTensorModel_inv_app (W : Scheme.{u})
    (M N : podReindexingDerived l E W none) :
    (podReindexingTensorModel l E W).inv.app (M, N) =
      (pullbackTensorIntegralTensorModel l E W).inv.app (M, N) := by
  unfold podReindexingTensorModel
  rfl

/-- Data for a reduction/limit tensor square, without either compatibility assertion.
All entries are actual maps; the record only shares their types between the two squares.
Source: Stacks 07A4 and the reduction/limit adjunction
(blueprint: lem-pod-reindexing-reduction-tensor-square). -/
structure PodTensorAugmentationFrame
    (C D A B : Type*) [Category* C] [Category* D] [Category* A] [Category* B] where
  F : C ⥤ D
  P : A ⥤ B
  LY : C ⥤ A
  LX : D ⥤ B
  RY : A ⥤ C
  RX : B ⥤ D
  adjY : LY ⊣ RY
  adjX : LX ⊣ RX
  δ : RY ⋙ F ⟶ P ⋙ RX
  S : C
  T : D
  U : A
  V : B
  W : B
  CY : C
  CX : D
  bY : LY.obj S ⟶ U
  bX : LX.obj T ⟶ V
  a : P.obj (LY.obj S) ⟶ LX.obj (F.obj S)
  w₁ : P.obj U ⟶ W
  w₂ : W ⟶ V
  dY : CY ≅ RY.obj U
  dX : CX ≅ RX.obj V
  unit : F.map (adjY.unit.app S) ≫ δ.app (LY.obj S) ≫ RX.map a =
    adjX.unit.app (F.obj S)

/-- The frame is built from the specified comparisons, with the Unit law as its
only compatibility proof. It makes no tensor compatibility assertion.
Source: Stacks 07A4 and the reduction/limit adjunction
(blueprint: lem-pod-reindexing-reduction-tensor-square). -/
def podReindexingTensorFrame
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g) (hA : PodCompletionReindex.Laws l E g A)
    (M N : podReindexingDerived l E Y none) :
    PodTensorAugmentationFrame
      (podReindexingDerived l E Y none) (podReindexingDerived l E X none)
      (DerivedCategory (coefficientSequenceModules l E Y))
      (DerivedCategory (coefficientSequenceModules l E X)) where
  F := podOrdinaryReindex l E g
  P := integralComparisonDerivedSequencePullback l E g
  LY := (podReindexCalculus l E Y).reduction
  LX := (podReindexCalculus l E X).reduction
  RY := coefficientSequenceLimit l E Y
  RX := coefficientSequenceLimit l E X
  adjY := (podReindexCalculus l E Y).adjunction
  adjX := (podReindexCalculus l E X).adjunction
  δ := A.limit.hom
  S := (podReindexCalculus l E Y).integralClosed.tensor.obj (M, N)
  T := (podReindexCalculus l E X).integralClosed.tensor.obj
    ((podOrdinaryReindex l E g).obj M, (podOrdinaryReindex l E g).obj N)
  U := (podReindexCalculus l E Y).systemClosed.tensor.obj
    ((podReindexCalculus l E Y).reduction.obj M, (podReindexCalculus l E Y).reduction.obj N)
  V := (podReindexCalculus l E X).systemClosed.tensor.obj
    ((podReindexCalculus l E X).reduction.obj ((podOrdinaryReindex l E g).obj M),
      (podReindexCalculus l E X).reduction.obj ((podOrdinaryReindex l E g).obj N))
  W := (podReindexCalculus l E X).systemClosed.tensor.obj
    ((integralComparisonDerivedSequencePullback l E g).obj
      ((podReindexCalculus l E Y).reduction.obj M),
      (integralComparisonDerivedSequencePullback l E g).obj
        ((podReindexCalculus l E Y).reduction.obj N))
  CY := (integralCompletedTensor l E Y).obj (M, N)
  CX := (integralCompletedTensor l E X).obj
    ((podOrdinaryReindex l E g).obj M, (podOrdinaryReindex l E g).obj N)
  bY := (podReindexCalculus l E Y).reductionTensor.hom.app (M, N)
  bX := (podReindexCalculus l E X).reductionTensor.hom.app
    ((podOrdinaryReindex l E g).obj M, (podOrdinaryReindex l E g).obj N)
  a := A.reduction.hom.app
    ((podReindexCalculus l E Y).integralClosed.tensor.obj (M, N))
  w₁ := (podReindexingSystemTensor l E g).hom.app
    ((podReindexCalculus l E Y).reduction.obj M, (podReindexCalculus l E Y).reduction.obj N)
  w₂ := (podReindexCalculus l E X).systemClosed.tensor.map
    (Prod.mkHom (A.reduction.hom.app M) (A.reduction.hom.app N))
  dY := (podReindexingTensorModel l E Y).app (M, N)
  dX := (podReindexingTensorModel l E X).app
    ((podOrdinaryReindex l E g).obj M, (podOrdinaryReindex l E g).obj N)
  unit := by
    have hu := hA.2.2.2.1
      ((podReindexCalculus l E Y).integralClosed.tensor.obj (M, N))
    dsimp only [Functor.comp_obj, Functor.id_obj] at hu
    exact hu

/-- The ordinary tensor comparison commutes with coherent reduction before applying
any limit or adjunction unit. No completed tensor comparison occurs in this equation.
Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 03EL, 07A4, 0941
(blueprint: lem-pod-reindexing-reduction-tensor-square).

Proof: choose simultaneous flat-term K-flat representatives P,Q. Use c.tensor_model
and the reductionTensor_normalization of the recorded coefficient calculus to replace
both tensor comparisons by their strict signed total-tensor maps. The reduction
comparison A.reduction is the whole-system adjunction mate, by
podReindexing_reduction_inv_mate. LimitModel realizes that mate by the actual strict
Roos map, not by separate derived evaluations. The ordinary quotient unit formulas
and FiniteModel identify the resulting strict reduction comparison with A.quotient.
Its QuotientGenerators law
sends a tensor x to its scalar-reindexed quotient tensor. The system comparison is
pullbackTensorSystemComparison, whose cochain normalization is the same ordinary
inverse-image tensor map on the sequence site. On each homogeneous tensor both routes
send b tensor (x tensor y) to the two reindexed reduced factors, with b on the first
factor and 1 on the second. Balancing and c.tensorChain_pure prove equality on pure
tensors; the quotient transition laws give equality as entire system chain maps.
Descend this equality along the product of the K-flat resolving localizations.
The equality h only transports the ordinary functor, so introduces no additional map.
The argument uses neither completeness nor a Tor bound and applies to zero inputs
and the empty scheme. -/
theorem podReindexing_reduction_tensor_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (hA : PodCompletionReindex.Laws l E g A)
    (c : PodReindexingCoherence.Comparison l E g none
      (podReindexCalculus l E X).integralClosed (podReindexCalculus l E Y).integralClosed
      (podReindexCalculus l E X).integralTensorModel
      (podReindexCalculus l E Y).integralTensorModel)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (M N : podReindexingDerived l E Y none) :
    let q := podReindexingTensorFrame l E g A hA M N
    let v : q.F.obj q.S ⟶ q.T := podReindexingIntegralTensorHom l E g c h M N
    q.P.map q.bY ≫ q.w₁ ≫ q.w₂ = q.a ≫ q.LX.map v ≫ q.bX := by
  dsimp [podReindexingTensorFrame, podReindexingIntegralTensorHom]
  exact podReindexing_reduction_tensor_square_descent l E g A hA c h
    c.tensorChain_pure M N

end WeilConjectures
