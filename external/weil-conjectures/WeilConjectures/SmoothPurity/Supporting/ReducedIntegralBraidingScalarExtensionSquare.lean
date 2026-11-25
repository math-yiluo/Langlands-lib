/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorCoherentReduction
import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorBraiding

/-!
# Coherent reduction of the integral braiding scalar-extension square

Source: literature/stacks-project/more-algebra.tex, item-flip-tensor-product
(blueprint: lem-pur-integral-braiding-scalar-extension-square-reduced).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/--
The scalar-extension square for the integral braiding becomes equal after coherent
reduction. This is the finite-stage signed-swap assertion assembled through the
normalized reduction systems.

Source: literature/stacks-project/more-algebra.tex, item-flip-tensor-product, signed total symmetry;
Bhatt--Scholze, Lemma 3.5.7.
Proof: the coherent scalar-tensor normalization supplies the natural comparison
between scalar extension followed by reduction and reduction followed by scalar
extension. The whole-system scalar tensorator commutes with signed symmetry, as
proved on flat-term K-flat representatives and homogeneous tensor generators.
Apply the categorical reduced-braiding calculation to these equations and the
defining reduction equations of both integral braidings; then map the result
through coherent reduction.
(blueprint: lem-pur-integral-braiding-scalar-extension-square-reduced).
-/
theorem reducedIntegralBraidingScalarExtensionSquare
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (integralSystemReduction l L W).map (
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          ((pullbackTensorIntegralBraiding l E W M N).hom) ≫
          (integralTensorScalarComparison l E L ι W N M).hom) =
      (integralSystemReduction l L W).map (
        (integralTensorScalarComparison l E L ι W M N).hom ≫
          (pullbackTensorIntegralBraiding l L W
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj M)
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj N)).hom) := by
  let R := integralSystemReduction l E W
  let Q := integralSystemReduction l L W
  let F := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let H := integralComparisonDerivedSequenceScalar l E L ι W
  obtain ⟨p, hp⟩ := integralScalarTensorCoherentReduction l E L ι W
  have := (integralSystemReduction_fullyFaithful l L W).2
  apply congrArg Q.map
  exact reduced_braiding R Q F H
    (constructibleIntegralTensor l E W) (constructibleIntegralTensor l L W)
    (pullbackTensorCalculus l E W).systemClosed.tensor
    (pullbackTensorCalculus l L W).systemClosed.tensor
    (pullbackTensorIntegralReductionTensor l E W)
    (pullbackTensorIntegralReductionTensor l L W) p
    (integralTensorScalarComparison l E L ι W)
    (fun A B ↦ (ScalarExtensionTower.derivedSigma l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).app (A, B))
    (pullbackTensorIntegralBraiding l E W) (pullbackTensorIntegralBraiding l L W)
    (fun A B ↦ (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
      (pullbackTensorCalculus l E W).systemClosed
      (pullbackTensorCalculus l E W).systemTensorModel).app (A, B))
    (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l L W)
      (pullbackTensorCalculus l L W).systemClosed
      (pullbackTensorCalculus l L W).systemTensorModel)
    (fun A B ↦ (pullbackTensorIntegralBraiding_existsUnique l E W A B).exists.choose_spec)
    (fun A B ↦ (pullbackTensorIntegralBraiding_existsUnique l L W A B).exists.choose_spec)
    hp (systemScalarTensorBraiding l E L ι W) M N

end WeilConjectures
