/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensor

/-! # Field-tower coherence of the explicit integral comparison

Source: Bhatt--Scholze, Propositions 3.5.1 and 6.8.14(2), Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]

/-- For a tower `E ≤ L ≤ M`, the explicit integral comparisons compose, through the
integral scalar associator, to the direct comparison. The associator `assoc` is pinned by
`hassoc` to `sfIntegralScalarComp` followed by equality transport along the
field-inclusion composition law (this is `integralTensorAssociator` of the item's module
`WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensorCoherence`,
which imports this module, with
`hassoc` its defining equation `integralTensorAssociator_eq`); for an arbitrary `assoc`
the equation would be false.

Source: Bhatt--Scholze, Propositions 3.5.1 and 6.8.14(2), Remark 6.8.15; the tower
clause of `lem-sf-native-integral-tensor-coherence`
(blueprint: new-lem-sf-native-integral-tensor-tower-coherence).

Proof: rewrite `assoc` by `hassoc`. By the canonical completed scalar associator formula
(`lem-sf-completed-scalar-associator-ambient-formula`) the integral associator
`sfIntegralScalarComp` is the ordinary derived balancing associator conjugated by the
three completion comparisons. Naturality moves the completion comparisons across the
outer tensor functor `integralTensor l X C M`, and consecutive inverse comparisons cancel.
What remains is associativity of the balanced derived tensor with the native ring of `C`:
on a pure triple tensor `c ⊗ b ⊗ x` both maps give `c b ⊗ x`. Check this on ordinary
tensor units and on K-flat complexes, then descend by the universal derived counit
(`lem-sf-native-integral-tensor`). The scalar equations of the coefficient system
(`lem-sf-locally-finite-adic-coefficient-system`) identify the direct ring map `E → M`,
and the equality transport along `coefficientInclusion_laws` gives exactly the displayed
associator, including repeated fields. -/
theorem integralTensorComparison_tower (C : CoefficientSystem l X)
    (assoc : ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M),
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ⋙
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l (PadicAlgCl l) L) (Coefficient.{u} l (PadicAlgCl l) M)
        (coefficientInclusion l (PadicAlgCl l) L M k) X ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) M)
        (coefficientInclusion l (PadicAlgCl l) E M (h.trans k)) X)
    (hassoc : ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M),
      assoc h k =
        sfIntegralScalarComp l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) X
          0 (Fact.out : l.Prime).ne_zero (Coefficient.{u} l (PadicAlgCl l) M)
          (coefficientInclusion l (PadicAlgCl l) L M k) ≪≫
        eqToIso (congrArg
          (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) M) i X)
          ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l
            (PadicAlgCl l)).2 E L M h k))) :
    ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      (integralTensorComparison l X C h).app K ≫
        (integralTensorComparison l X C k).app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition
            l (PadicAlgCl l) X E L h).obj K) ≫
        (integralTensor l X C M).map ((assoc h k).hom.app K) =
      (integralTensorComparison l X C (h.trans k)).app K := by
  sorry

end WeilConjectures.LocallyFiniteAdicRealization
