/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingEndpointScalarIdentityTransferData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingEndpointScalarIdentityNormalization

/-! # Universe transfer for endpoint scalar identities -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
attribute [local instance] constructionInclusionShift

private noncomputable def scalarFunctorAtClosureIso
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _)
    (S : Scalar.{max u v, max u v} l Ψ a W)
    (I : ScalarIdentity.{max u v, max u v} l Ψ h W S) :
    (scalarAtClosure.{u, v} l Ω Ψ W S).functor ≅
      𝟭 (C.{u, v} l Ω W (s.stage l)) := by
  cases s <;> exact I.iso

/-- Transfers the multiplication-normalized identity certificate from an equal-universe
closure to the original coefficient universes. This is the normalization substep of
endpoint scalar restriction assembly.
Source: Zheng, Lemma 5.22 and Proposition 5.26
(blueprint: lem-sf-ring-endpoint-scalar-identity-transfer).
-/
theorem scalarIdentityAtClosure
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _)
    (S : Scalar.{max u v, max u v} l Ψ a W)
    (I : ScalarIdentity.{max u v, max u v} l Ψ h W S) :
    Nonempty (ScalarIdentity.{u, v} l Ω h W (scalarAtClosure.{u, v} l Ω Ψ W S)) := by
  cases s with
  | finite E n =>
      let J := scalarFunctorAtClosureIso l Ω Ψ W h S I
      exact ⟨ScalarIdentity.mk J (fun K =>
        scalarIdentityNormalizationAtClosure l Ω Ψ W h S I J (by rfl) K)⟩
  | integral E =>
      let J := scalarFunctorAtClosureIso l Ω Ψ W h S I
      exact ⟨ScalarIdentity.mk J (fun K =>
        scalarIdentityNormalizationAtClosure l Ω Ψ W h S I J (by rfl) K)⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
