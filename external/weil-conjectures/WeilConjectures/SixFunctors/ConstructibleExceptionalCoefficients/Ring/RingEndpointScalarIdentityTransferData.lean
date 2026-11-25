/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

/-! # Universe transfer data for endpoint scalar identities -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
attribute [local instance] constructionInclusionShift

/-- The scalar extension record obtained by reusing the finite and integral
constructions at the original coefficient universes.
Source: Zheng, Lemma 5.22 and Proposition 5.26
(blueprint: def-sf-ring-endpoint-scalar-at-closure).
-/
def scalarAtClosure
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s t : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    (S : Scalar.{max u v, max u v} l Ψ a W) : Scalar.{u, v} l Ω a W :=
  { functor := by
      cases s <;> cases t <;> exact S.functor
    realization := by
      cases s <;> cases t <;> exact S.realization
    commShift := by
      cases s <;> cases t <;> exact Scalar.commShift S
    additive := by
      cases s <;> cases t <;> exact Scalar.additive S
    exact := by
      cases s <;> cases t <;> exact Scalar.exact S }

end WeilConjectures.ConstructibleExceptionalCoefficients
