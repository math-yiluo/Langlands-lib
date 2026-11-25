/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingEndpointScalarIdentityTransferData

/-! # Normalization transport for endpoint scalar identities -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
attribute [local instance] constructionInclusionShift

/-- The normalization equation is invariant under the universe reindexing of a ring-stage
scalar extension, for an identity isomorphism equal to the certificate isomorphism.
First replace the coefficient map family by the identity using h and function
extensionality, so the equality-isomorphism cast reduces. In each finite or integral
case the categories ignore the closure field. Replace J by I.iso using hJ and apply
I.normalized K to the unchanged inclusion, realization, and tensor unitor.
Source: Zheng, Lemma 5.22 and Proposition 5.26, universe bookkeeping.
(blueprint: lem-sf-ring-endpoint-scalar-identity-normalization-transport).
-/
theorem scalarIdentityNormalizationAtClosure
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _)
    (S : Scalar.{max u v, max u v} l Ψ a W)
    (I : ScalarIdentity.{max u v, max u v} l Ψ h W S)
    (J : (scalarAtClosure.{u, v} l Ω Ψ W S).functor ≅
      𝟭 (C.{u, v} l Ω W (s.stage l)))
    (hJ : HEq J I.iso)
    (K : C.{u, v} l Ω W (s.stage l)) :
    (RingStage.inclusion.{u, v} l Ω W s).map (J.hom.app K) =
      (scalarAtClosure.{u, v} l Ω Ψ W S).realization.hom.app K ≫
        (eqToIso (congrArg pbcDerivedExtend (h W))).hom.app
          ((RingStage.inclusion.{u, v} l Ω W s).obj K) ≫
        (PurCompactSupport.tensorIdentity ((s.coefficients l).ring W)).hom.app
          ((RingStage.inclusion.{u, v} l Ω W s).obj K) := by
  cases a with
  | mk m sq =>
    have hm : m = fun T ↦ 𝟙 ((s.coefficients l).ring T) := funext h
    subst m
    cases s <;> obtain rfl := eq_of_heq hJ <;> exact I.normalized K

end WeilConjectures.ConstructibleExceptionalCoefficients
