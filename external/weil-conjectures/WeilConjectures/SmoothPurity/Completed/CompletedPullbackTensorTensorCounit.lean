/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

/-! The tensor component of the completed pullback counit comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The counit on a tensor of two reduced systems is invertible.
Source: the counit-effectivity step of Stacks 0941 and Bhatt--Scholze 3.4.12
(blueprint: lem-pur-completed-pullback-tensor-counit).
Proof: the reduction tensor comparison identifies this tensor with the reduction
of the integral tensor of M and N. Reconstruction inverts the counit on that
reduction. Naturality of the actual counit conjugates it along the reduction tensor
comparison; cancel the isomorphism on its source to obtain the desired counit. -/
theorem completedPullbackTensor_tensor_counit
    (W : Scheme.{u}) (_hW : ∀ w : W, IsUnit (l : W.residueField w))
    (C : CoefficientDerivedSystemCalculus l E W)
    (M N : DerivedCategory (scalarReductionSource l E W)) :
    IsIso (C.adjunction.counit.app
      (C.systemClosed.tensor.obj (C.reduction.obj M, C.reduction.obj N))) := by
  let D : DerivedCategory (scalarReductionSource l E W) :=
    C.integralClosed.tensor.obj (M, N)
  let e : C.reduction.obj D ≅
      C.systemClosed.tensor.obj (C.reduction.obj M, C.reduction.obj N) :=
    C.reductionTensor.app (M, N)
  have : IsIso (C.adjunction.counit.app (C.reduction.obj D)) :=
    ((purNormalizedReconstructionOfScheme.{u, u} l E W C).1 _
      (C.reduction_normalized D)).2
  have hn := C.adjunction.counit.naturality e.hom
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
    Functor.comp_map, Functor.id_map] at hn
  have : IsIso
      (C.reduction.map ((coefficientSequenceLimit.{u, u} l E W).map e.hom) ≫
        C.adjunction.counit.app
          (C.systemClosed.tensor.obj (C.reduction.obj M, C.reduction.obj N))) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (C.reduction.map ((coefficientSequenceLimit.{u, u} l E W).map e.hom)) _

end WeilConjectures
