/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionFiniteEvaluationData

/-! # Explicit factors of finite evaluation

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions.
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
  pullbackTensorCalculus

/-- The ambient fixed-coefficient tensor, before restricting its input domains.
Source: the finite projection construction
(blueprint: def-sf-integral-projection-evaluation-factors). -/
abbrev evaluatedTensor (X : SixFunctorSpace D) :=
  Functor.uncurry.obj (CompactSupportFiniteProjection.tensor
    (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X)

/-- A comparison on all system inputs, independent of support and integral realization.
Source: finite tensor evaluation
(blueprint: def-sf-integral-projection-evaluation-factors). -/
abbrev SystemTensorEvaluation := ∀ X : SixFunctorSpace D,
  (calculus C.l E X.obj.left).systemClosed.tensor ⋙ evaluation (C := C) (E := E) m X ≅
    (evaluation (C := C) (E := E) m X).prod
      (evaluation (C := C) (E := E) m X) ⋙ evaluatedTensor (C := C) (E := E) m X

/-- Evaluate support by its open and proper factors, and the given finite realization.
Source: supportEvaluation and finiteSupport
(blueprint: def-sf-integral-projection-evaluation-factors). -/
def evaluatedSupport (o : Operations C.l E) {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (evaluation (C := C) (E := E) m Y).obj
        ((Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj
          ((calculus C.l E X.obj.left).reduction.obj K.obj))) ≅
      (finiteInclusion (C := C) (E := E) m Y).obj
        (((stage d m).finite.support f c).obj ((reduction d m X).obj K)) :=
  (supportEvaluation C.l E o c m).app _ ≪≫
    (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).mapIso
      (reductionEvaluation d m X K) ≪≫
    ((stage d m).finiteSupport f c).symm.app _

/-- Evaluate inverse image, retaining the datum's prescribed finite pullback comparison.
Source: pullbackTensorDerivedEvaluation and finitePullback
(blueprint: def-sf-integral-projection-evaluation-factors). -/
def evaluatedPull {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (evaluation (C := C) (E := E) m X).obj
        ((pull C.l E f.hom.left).obj ((calculus C.l E Y.obj.left).reduction.obj L.obj)) ≅
      ((CompactSupportFiniteProjection.torPull (stage d m) f).obj
        ((torReduction d m Y).obj L)).obj :=
  (pullbackTensorDerivedEvaluation C.l E f.hom.left m).app _ ≪≫
    (finiteDerivedPullback C.l E m f.hom.left).mapIso (reductionEvaluation d m Y L) ≪≫
    ((stage d m).finitePullback f).symm.app _

/-- Evaluation of the tensor/pullback input by its three specified factors.
Source: tensor and inverse-image evaluation
(blueprint: def-sf-integral-projection-evaluation-factors). -/
def evaluatedInput (b : SystemTensorEvaluation (C := C) (E := E) m)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (evaluation (C := C) (E := E) m X).obj
      ((calculus C.l E X.obj.left).systemClosed.tensor.obj
        ((calculus C.l E X.obj.left).reduction.obj K.obj,
          (pull C.l E f.hom.left).obj ((calculus C.l E Y.obj.left).reduction.obj L.obj))) ≅
      (finiteInclusion (C := C) (E := E) m X).obj
        (((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
          ((reduction d m X).obj K)).obj
            ((CompactSupportFiniteProjection.torPull (stage d m) f).obj
              ((torReduction d m Y).obj L))) :=
  (b X).app ((calculus C.l E X.obj.left).reduction.obj K.obj,
      (pull C.l E f.hom.left).obj ((calculus C.l E Y.obj.left).reduction.obj L.obj)) ≪≫
    (evaluatedTensor (C := C) (E := E) m X).mapIso
      (Iso.prod (reductionEvaluation d m X K) (evaluatedPull d m f L))

/-- The source endpoint: evaluate tensor, support, and the second integral input.
Source: the source of the finite projection
(blueprint: def-sf-integral-projection-evaluation-factors). -/
def evaluatedSource (b : SystemTensorEvaluation (C := C) (E := E) m)
    (o : Operations C.l E) {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (evaluation (C := C) (E := E) m Y).obj (systemSource o f c K L) ≅
      (finiteInclusion (C := C) (E := E) m Y).obj
        (((CompactSupportFiniteProjection.partialTensor (stage d m) Y).obj
          (((stage d m).finite.support f c).obj ((reduction d m X).obj K))).obj
            ((torReduction d m Y).obj L)) :=
  (b Y).app ((Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj
      ((calculus C.l E X.obj.left).reduction.obj K.obj)),
      (calculus C.l E Y.obj.left).reduction.obj L.obj) ≪≫
    (evaluatedTensor (C := C) (E := E) m Y).mapIso
      (Iso.prod (evaluatedSupport d m o f c K) (reductionEvaluation d m Y L))

/-- The target endpoint: evaluate support, its tensor input, and finite support realization.
Source: the target of the finite projection
(blueprint: def-sf-integral-projection-evaluation-factors). -/
def evaluatedTarget (b : SystemTensorEvaluation (C := C) (E := E) m)
    (o : Operations C.l E) {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (evaluation (C := C) (E := E) m Y).obj (systemTarget o f c K L) ≅
      (finiteInclusion (C := C) (E := E) m Y).obj
        (((stage d m).finite.support f c).obj
          (((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
            ((reduction d m X).obj K)).obj
              ((CompactSupportFiniteProjection.torPull (stage d m) f).obj
                ((torReduction d m Y).obj L)))) :=
  (supportEvaluation C.l E o c m).app _ ≪≫
    (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).mapIso
      (evaluatedInput d m b f K L) ≪≫
    ((stage d m).finiteSupport f c).symm.app
      (((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
        ((reduction d m X).obj K)).obj
          ((CompactSupportFiniteProjection.torPull (stage d m) f).obj
            ((torReduction d m Y).obj L)))

end WeilConjectures.IntegralProjectionReduction
