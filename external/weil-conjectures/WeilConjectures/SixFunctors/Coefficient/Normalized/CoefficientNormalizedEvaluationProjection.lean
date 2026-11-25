/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedEvaluationProjectionComponents

/-! # Projection for normalized coefficient evaluation

Source: Stacks 07A4, 08J9 and 0941; Zheng Construction 4.1.
(blueprint: lem-coef-normalized-evaluation-projection).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem coefficientSequence_isIso_iff_evaluations
    {M N : coefficientSequenceDerived l E W} (f : M ⟶ N) :
    IsIso f ↔ ∀ n : ℕ,
      IsIso ((coefficientSequenceDerivedEvaluation l E W n).map f) := by
  constructor
  · intro hf n
    haveI : IsIso f := hf
    infer_instance
  · intro hf
    obtain ⟨D⟩ := SemilinearSections.semilinearDerivedSections.{t + 1, t, u}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W)
    exact D.systems.detects f hf

/-- The unit-defined finite-prefix projection is invertible on a normalized system.
This is a tensor assertion, before internal Hom or any transition formula for Hom.
Source: Zheng Construction 4.1 and Proposition 4.17(a); Stacks 07A4, 08J9;
step 1 of lem-coef-normalized-internal-hom-fibers.
(blueprint: lem-coef-normalized-evaluation-projection).

Proof: identify L with the derived finite-prefix extension by the unique
unit-compatible isomorphism of left adjoints. Choose flat-term K-flat
representatives of P and M. Below n the projection is scalar tensor
reassociation followed by tensor with the actual normalized reduction of M;
above n both sides are zero. The ordinary comparison is fixed on pure tensors
by hE. Its cochain comparison is therefore the projection just described.
Normalization makes its below-n components invertible, independently of which
normalized scalar adjunction presents those reductions. Evaluation and tensor
preserve the zero objects above n. Joint detection of isomorphisms makes the
projection invertible in the system derived category. Transport back along the
unit-compatible comparison of left adjoints. This includes n=0, zero P or M,
and the empty site; it assumes no flatness of coefficient quotients. -/
theorem coefficientNormalizedEvaluationProjection
    (R : CoefficientDerivedSystemReduction l E W)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (M : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M) (n : ℕ)
    (L : normalizedDVRDerived l E W n ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceDerivedEvaluation l E W n)
    (P : normalizedDVRDerived l E W n) :
    IsIso ((adj.homEquiv _ _).symm
      ((R.finiteClosed n).tensor.map
          (Prod.mkHom (adj.unit.app P)
            (𝟙 ((coefficientSequenceDerivedEvaluation l E W n).obj M))) ≫
        (R.evaluationTensor n).inv.app (L.obj P, M))) := by
  let f := (adj.homEquiv _ _).symm
    ((R.finiteClosed n).tensor.map
        (Prod.mkHom (adj.unit.app P)
          (𝟙 ((coefficientSequenceDerivedEvaluation l E W n).obj M))) ≫
      (R.evaluationTensor n).inv.app (L.obj P, M))
  exact (coefficientSequence_isIso_iff_evaluations l E W f).2
    (fun q ↦ coefficientNormalizedEvaluationProjection_components l E W R hE M hM n L adj P q)

end WeilConjectures
