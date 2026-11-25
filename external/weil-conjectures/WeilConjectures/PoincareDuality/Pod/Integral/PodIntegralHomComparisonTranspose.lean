/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso

/-! # Transposition under the integral pullback Hom comparison

Source: Stacks Project, Tag 0GMX; blueprint main-20261015
theorem-poincare-duality-frobenius--2, Steps 8--11
(blueprint: stage3-derived-automorphism-continuation-a-integral-transpose).

The transpose field of `podIntegralHomComparison_laws`, proved from parameter
naturality of the closed data and naturality of the canonical integral
pullback-tensor comparison (`derivedPullbackTensorIso`).
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

/-- Transposition component of the integral pullback Hom compatibility.
Source: Stacks 0GMX; node lem-pod-derived-automorphism-hom-evaluation, steps 8--11.
Proof: put `t = transpose_Y f`. By definition `c_P = transpose_X (μ⁻¹ ≫ F ev_P)`,
so parameter naturality turns `F t ≫ c_P` into the transpose of
`T(F t, 1) ≫ μ⁻¹ ≫ F ev_P`. The canonical comparison `μ` is the component of a
natural isomorphism (`derivedPullbackTensorIso`), so
`T(F t, 1) ≫ μ⁻¹ = μ⁻¹ ≫ F(T(t, 1))`. Finally `T(t,1) ≫ ev_P` is the inverse
transpose of `t`, that is `f`, by parameter naturality on `Y`.
(blueprint: stage3-derived-automorphism-continuation-a-integral-transpose). -/
theorem podIntegralHomComparison_transpose :
    ∀ (L : sfIntegralConstructibleCategory l E Y)
      (P : (constructibleIntegralHomPairs l E Y).FullSubcategory)
      (f : (constructibleIntegralTensor l E Y).obj (L, P.obj.1.unop) ⟶ P.obj.2),
      (podIntegralClosed l E X).transpose _ _
          ((canonicalIntegralPullbackTensor l E g L P.obj.1.unop).inv ≫
            (constructibleIntegralPullback l E g).map f) =
        (constructibleIntegralPullback l E g).map
            ((podIntegralClosed l E Y).transpose L P f) ≫
          podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) P := by
  intro L P f
  obtain ⟨eI, heI⟩ := (derivedPullbackTensorIso l E g 0 (AlgebraicClosure ℚ_[l])).2.2.2.2.2.1
  set t := (podIntegralClosed l E Y).transpose L P f
  have hμ : (constructibleIntegralTensor l E X).map
        (Prod.mkHom ((constructibleIntegralPullback l E g).map t) (𝟙 _)) ≫
        (canonicalIntegralPullbackTensor l E g
          ((constructibleIntegralHom l E Y).obj P) P.obj.1.unop).inv =
      (canonicalIntegralPullbackTensor l E g L P.obj.1.unop).inv ≫
        (constructibleIntegralPullback l E g).map
          ((constructibleIntegralTensor l E Y).map (Prod.mkHom t (𝟙 _))) := by
    rw [← heI, ← heI, Iso.app_inv, Iso.app_inv]
    have := eI.inv.naturality (Prod.mkHom t (𝟙 P.obj.1.unop))
    simpa [Functor.comp_map, Functor.prod_map] using this
  have hev : (constructibleIntegralTensor l E Y).map (Prod.mkHom t (𝟙 _)) ≫
      (podIntegralClosed l E Y).evaluation P = f := by
    apply ((podIntegralClosed l E Y).transpose L P).injective
    rw [(podIntegralClosed l E Y).parameter_naturality, PodPartialClosed.evaluation,
      AddEquiv.apply_symm_apply, Category.comp_id]
  rw [podPartialHomComparison]
  erw [← (podIntegralClosed l E X).parameter_naturality]
  congr 1
  symm
  erw [reassoc_of% hμ]
  rw [← Functor.map_comp, hev]

end WeilConjectures
