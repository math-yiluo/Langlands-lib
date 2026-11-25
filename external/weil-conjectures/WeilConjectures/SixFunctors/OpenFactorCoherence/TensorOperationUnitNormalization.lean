/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorTensorModel
public import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Pure-section normalization of the quotient tensor augmentation

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5; Stacks 03EL, 07A4, 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open Opposite CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
open IntegralAmbient
attribute [local implicit_reducible] PurCompactSupport.completed

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- Every natural chain with the recorded tensor-operation augmentation has its two
prescribed quotient coordinates.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5; Stacks 03EL, 07A4, 0941
(blueprint: lem-sf-tensor-operation-unit-normalization).
Proof: the operation-unit coordinate theorem identifies the first coordinate with the
product augmentation followed by the strict tensor-tower comparison, and makes the
shifted coordinate zero. Project the first identity to level n and evaluate on a
homogeneous pure tensor. The quotient augmentation sends that tensor to its generator
with scalar 1. The strict tensor-tower normalization sends this generator to the tensor
of the two quotient-unit sections. These equalities give exactly the first clause of
IsTensorChain; the second clause is the zero shifted coordinate. The same formulas hold
for zero sections and for the empty scheme, without any additional hypotheses. -/
theorem tensorOperationUnit_normalized
    (chain : constructibleTensorTotal l E X ⟶ integralOperationsTensorComplexFunctor l E X)
    (hchain : ∀ P Q, chain.app (P, Q) = tensorOperationUnit l E X P Q) :
    IsTensorChain l E X chain := by
  unfold IsTensorChain
  simp only [hchain]
  constructor
  · intro P Q p q n V x y
    have hf := (tensorOperationUnit_coordinates l E X P Q).1
    have hproj := congrArg (fun f ↦ f ≫ Pi.π
      (fun k ↦ ((integralOperationsTensorTowerFunctor l E X).obj (P, Q)).obj
        (Opposite.op k)) n) hf
    with_unfolding_all
      simp only [Category.assoc, Pi.map_π] at hproj
    have hsec := congrArg (fun f ↦ (f.f (p + q)).val.app V
      (constructibleTensorTotalSection l E X P Q p q V x y)) hproj
    with_unfolding_all
      simp only [IntegralOnSlice.productAugmentation, Pi.lift_comp_π_assoc] at hsec
    have hunit := (IntegralOnSlice.augmentation_existsUnique l E X none).exists.choose_spec
    have htower := (tensorTowerModel l E X).exists.choose_spec P Q n p q V 1 x y
    with_unfolding_all refine hsec.trans ?_
    let T := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q)
    let z := constructibleTensorTotalSection l E X P Q p q V x y
    have hu : ((((IntegralOnSlice.augmentation l E X none).app T).app (op n)).f
        (p + q)).val.app V z =
        IntegralOnSlice.generator l E X none n (T.X (p + q)) V 1 z :=
      hunit T n (p + q) V z
    have hc := congrArg (fun z ↦
      ((((tensorTowerIso l E X).hom.app (P, Q)).app (op n)).f (p + q)).val.app V z) hu
    with_unfolding_all exact hc.trans htower
  · intro P Q i j h
    with_unfolding_all exact (tensorOperationUnit_coordinates l E X P Q).2 i j h

end WeilConjectures.OpenFactorCoherence
