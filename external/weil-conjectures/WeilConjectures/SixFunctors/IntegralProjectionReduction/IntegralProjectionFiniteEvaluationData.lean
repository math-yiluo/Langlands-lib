/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionReductionData
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData

/-! # Evaluation diagrams for the system projection

Source: the successive coefficient reductions in fix-prop-projection-formula.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open IntegralSystemRealization

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (d : SixFunctorOperationDatum D C E n hn) (m : ℕ)

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus CompactSupportFiniteProjection.partialTensor
  CompactSupportFiniteProjection.component compactSupportProjectionComponent
  compactSupportProperProjection

/-- A natural tensor comparison, before taking its individual components.
Source: coefficient tensor associativity
(blueprint: def-sf-integral-projection-finite-evaluation-data). -/
abbrev TensorComparison := ∀ X : SixFunctorSpace D,
  Functor.uncurry.obj (d.higher.integralTensor X) ⋙ reduction d m X ≅
    ((reduction d m X).prod (torReduction d m X)) ⋙
      Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor (stage d m) X)

/-- The components of a given natural comparison; no new choice is made.
Source: evaluation of a natural isomorphism
(blueprint: def-sf-integral-projection-finite-evaluation-data). -/
def tensorCoordinates (e : TensorComparison d m) : TensorCoordinates d m :=
  fun X K L ↦ (e X).app (K, L)

/-- Ambient finite evaluation of a whole coefficient system.
Source: the recorded coefficient evaluation calculus
(blueprint: def-sf-integral-projection-finite-evaluation-data). -/
abbrev evaluation (X : SixFunctorSpace D) :=
  coefficientSequenceDerivedEvaluation C.l E X.obj.left m

/-- The full inclusion of the bounded finite category.
Source: the finite coefficient category
(blueprint: def-sf-integral-projection-finite-evaluation-data). -/
abbrev finiteInclusion (X : SixFunctorSpace D) :=
  (intrinsicFiniteTorsionConstructible C.l E (m + 1)
    (Nat.le_add_left 1 m) X.obj.left).ι

/-- Finite evaluation of the reduction is the actual quotient scalar extension.
Source: reductionEvaluation of the coefficient calculus
(blueprint: def-sf-integral-projection-finite-evaluation-data). -/
def reductionEvaluation (X : SixFunctorSpace D)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (evaluation (C := C) (E := E) m X).obj
        ((calculus C.l E X.obj.left).reduction.obj K.obj) ≅
      (finiteInclusion (C := C) (E := E) m X).obj ((reduction d m X).obj K) :=
  ((calculus C.l E X.obj.left).reductionEvaluation m).app K.obj

/-- The source of the system projection of reduced integral inputs.
Source: compactificationProjection on coefficient systems
(blueprint: def-sf-integral-projection-finite-evaluation-data). -/
abbrev systemSource (o : Operations C.l E) {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  (calculus C.l E Y.obj.left).systemClosed.tensor.obj
    ((Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj
      ((calculus C.l E X.obj.left).reduction.obj K.obj)),
      (calculus C.l E Y.obj.left).reduction.obj L.obj)

/-- The target of that same system projection.
Source: compactificationProjection on coefficient systems
(blueprint: def-sf-integral-projection-finite-evaluation-data). -/
abbrev systemTarget (o : Operations C.l E) {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  (Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj
    ((calculus C.l E X.obj.left).systemClosed.tensor.obj
      ((calculus C.l E X.obj.left).reduction.obj K.obj,
        (pull C.l E f.hom.left).obj
          ((calculus C.l E Y.obj.left).reduction.obj L.obj))))

/-- A proper counit projection expressed in the support coordinates of the
identity-open compactification. This is an explicit conjugate of the proper map.
Source: the proper identification in the projection formula
(blueprint: def-sf-integral-projection-finite-evaluation-data). -/
def properViaSupport {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  ((d.higher.integralTensor Y).map
      ((d.higher.integral.properIdentity f).hom.app K)).app L ≫
    compactSupportProperProjection d.higher.integralExchange f K L ≫
    (d.higher.integral.properIdentity f).inv.app
      (((d.higher.integralTensor X).obj K).obj ((d.higher.integral.pull f).obj L))

end WeilConjectures.IntegralProjectionReduction
