/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase

/-! # Evaluation square of the integral pullback Hom comparison

Source: Stacks Project, Tag 0GMX; blueprint main-20261015
theorem-poincare-duality-frobenius--2, Steps 8--11
(blueprint: stage3-derived-automorphism-continuation-a-integral-evaluation).

The evaluation field of `podIntegralHomComparison_laws`. It is formal: the
comparison is defined as a transpose, and evaluation is the inverse transpose
of the identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Evaluation component of the integral pullback Hom compatibility.
Source: Stacks 0GMX; node lem-pod-derived-automorphism-hom-evaluation, steps 8--11.
Proof: for any `f : L ⟶ H(Q)`, parameter naturality of the transposition gives
`transpose (T(f,1) ≫ ev_Q) = f ≫ transpose ev_Q = f`, so `T(f,1) ≫ ev_Q` is the
inverse transpose of `f`. Apply this to `c_P`, which is by definition the
transpose of `μ⁻¹ ≫ F(ev_P)`: then `T(c_P,1) ≫ ev = μ⁻¹ ≫ F(ev_P)`, and
precomposing with `μ` cancels `μ⁻¹`.
(blueprint: stage3-derived-automorphism-continuation-a-integral-evaluation). -/
theorem podIntegralHomComparison_evaluation :
    ∀ P : (constructibleIntegralHomPairs l E Y).FullSubcategory,
      (canonicalIntegralPullbackTensor l E g
          ((constructibleIntegralHom l E Y).obj P) P.obj.1.unop).hom ≫
        (constructibleIntegralTensor l E X).map
          (Prod.mkHom (podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) P) (𝟙 _)) ≫
        (podIntegralClosed l E X).evaluation
          ((podPairPullback (constructibleIntegralPullback l E g)
            (constructibleIntegralHomPairs l E Y) (constructibleIntegralHomPairs l E X)
            (podIntegralPairs_pullback l E g)).obj P) =
      (constructibleIntegralPullback l E g).map
        ((podIntegralClosed l E Y).evaluation P) := by
  intro P
  have key : ∀ (L : sfIntegralConstructibleCategory l E X)
      (Q : (constructibleIntegralHomPairs l E X).FullSubcategory)
      (f : L ⟶ (constructibleIntegralHom l E X).obj Q),
      (constructibleIntegralTensor l E X).map (Prod.mkHom f (𝟙 _)) ≫
          (podIntegralClosed l E X).evaluation Q =
        ((podIntegralClosed l E X).transpose L Q).symm f := by
    intro L Q f
    apply ((podIntegralClosed l E X).transpose L Q).injective
    rw [(podIntegralClosed l E X).parameter_naturality, PodPartialClosed.evaluation,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Category.comp_id]
  erw [key]
  rw [podPartialHomComparison, AddEquiv.symm_apply_apply, Iso.hom_inv_id_assoc]

end WeilConjectures
