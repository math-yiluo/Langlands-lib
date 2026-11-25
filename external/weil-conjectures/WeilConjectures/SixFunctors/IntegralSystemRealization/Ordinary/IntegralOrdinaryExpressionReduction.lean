/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralRealizationAssemblyData

/-! # Ordinary coefficient maps of finite expressions

Source: blueprint fix-prop-coherence, coefficient comparisons of the individual maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary tensor coefficient comparison, before completion.
Source: blueprint fix-prop-coherence, tensor reduction; the equality of ordinary tensor models.
(blueprint: def-sf-integral-ordinary-expression-reduction). -/
def ordinaryTensorReduction (d : RingedModels l E) (W : Scheme.{u}) :
    (d.tensor W).ordinary.tensor ⋙ (calculus l E W).reduction ⟶
      (calculus l E W).reduction.prod (calculus l E W).reduction ⋙
        (calculus l E W).systemClosed.tensor :=
  Functor.whiskerRight (eqToIso (d.tensorClosed W)).hom (calculus l E W).reduction ≫
    (calculus l E W).reductionTensor.hom

/-- The direct-image coefficient map is the mate of inverse pullback reduction.
Source: blueprint fix-prop-coherence, geometric adjunction compatibility.
(blueprint: def-sf-integral-ordinary-expression-reduction). -/
def ordinaryPushReduction (o : Operations l E) (m : RealizationModel l E o)
    {U V : Scheme.{u}} (f : U ⟶ V) :
    ringedPush l E f ⋙ (calculus l E V).reduction ⟶
      (calculus l E U).reduction ⋙ Operations.push l E o f :=
  (mateEquiv (ringedAdj l E f) (o.direct f).adj (m.reductionPull f).inv)

/-- Coefficient reduction of an ordinary expression, constructed independently of
any realization comparison. At an open vertex use the inverse of its fixed reduction mate;
at compact support use open reduction followed by the proper reduction mate.
Source: blueprint fix-prop-coherence, finite substitution into individual coefficient maps.
(blueprint: def-sf-integral-ordinary-expression-reduction). -/
def Expression.ordinaryReduction (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B} {W : Over B}
    (e : Expression B I X W) (K : ∀ i, Integral l E (X i).left) :
    (calculus l E W.left).reduction.obj (e.ringedObj l E a.ringedModels K) ⟶
      e.systemObj l E o ((inputReduction l E X).obj K) :=
  match e with
  | .var _ => 𝟙 _
  | .pull f e =>
    (a.realizationModel.reductionPull f.left).hom.app (e.ringedObj l E a.ringedModels K) ≫
      (IntegralSystemRealization.pull l E f.left).map (e.ordinaryReduction o a K)
  | .push f _ e =>
    (ordinaryPushReduction l E o a.realizationModel f.left).app
      (e.ringedObj l E a.ringedModels K) ≫
      (Operations.push l E o f.left).map (e.ordinaryReduction o a K)
  | .shriek j hj _ e =>
    letI := hj
    GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E j.left).app
      (e.ringedObj l E a.ringedModels K)) ≫
      (Operations.shriek l E o j.left).map (e.ordinaryReduction o a K)
  | .tensor e t =>
    (ordinaryTensorReduction l E a.ringedModels W.left).app
      (e.ringedObj l E a.ringedModels K, t.ringedObj l E a.ringedModels K) ≫
      (calculus l E W.left).systemClosed.tensor.map
        (Prod.mkHom (e.ordinaryReduction o a K) (t.ordinaryReduction o a K))
  | .compactSupport _ c e =>
    (ordinaryPushReduction l E o a.realizationModel c.g).app
      ((ringedOpen l E c.i).obj (e.ringedObj l E a.ringedModels K)) ≫
      (Operations.push l E o c.g).map
        (GeneratorReduction.inverseOrZero ((a.realizationModel.openReduction l E c.i).app
          (e.ringedObj l E a.ringedModels K)) ≫
          (Operations.shriek l E o c.i).map (e.ordinaryReduction o a K))

end WeilConjectures.IntegralSystemRealization
