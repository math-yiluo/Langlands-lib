/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.ExceptionalRingTransportFamily
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingEndpointScalarIdentityTransfer

/-! # Endpoint ring scalar restrictions -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
  AlgebraicGeometry.Scheme.completedAdicChange AlgebraicGeometry.Scheme.reductionChange
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.presheafToSheaf
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

attribute [local instance] constructionInclusionShift

private theorem isAlgClosedOfEquiv
    {K L : Type*} [Field K] [Field L] [IsAlgClosed K] (e : K ≃+* L) :
    IsAlgClosed L := by
  refine ⟨fun p ↦ ?_⟩
  have h := (IsAlgClosed.splits (p.map e.symm.toRingHom)).map e.toRingHom
  have he : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    ext n
    simp
  rwa [he] at h

private theorem scalarAtClosure_shift
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) :
    ∀ {s t : RingStage.{max u v} l}
      {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
      (S : Scalar.{max u v, max u v} l Ψ a W),
      (letI := ExceptionalIntegralScalar.inclusionShift l Ψ W s
       letI := ExceptionalIntegralScalar.inclusionShift l Ψ W t
       (Scalar.realization.{max u v, max u v} S).hom.CommShift ℤ) →
      (scalarAtClosure.{u, v} l Ω Ψ W S).realization.hom.CommShift ℤ := by
  intro s t
  cases s <;> cases t <;> intro a S h <;> exact h

private theorem scalarAtClosure_finiteEq
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) :
    ∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      {a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l)}
      (S : Scalar.{max u v, max u v} l Ψ a W),
      (Scalar.functor.{max u v, max u v} S) ⋙
          RingStage.inclusion.{max u v, max u v} l Ψ W (.finite E n) =
        RingStage.inclusion.{max u v, max u v} l Ψ W s ⋙ pbcDerivedExtend (a.map W) →
      (scalarAtClosure.{u, v} l Ω Ψ W S).functor ⋙ RingStage.inclusion.{u, v} l Ω W (.finite E n) =
        RingStage.inclusion.{u, v} l Ω W s ⋙ pbcDerivedExtend (a.map W) := by
  intro s
  cases s <;> intro E n a S h <;> exact h

private theorem scalarAtClosure_finiteNormalized
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) :
    ∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      {a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l)}
      (S : Scalar.{max u v, max u v} l Ψ a W)
      (h : (Scalar.functor.{max u v, max u v} S) ⋙
          RingStage.inclusion.{max u v, max u v} l Ψ W (.finite E n) =
        RingStage.inclusion.{max u v, max u v} l Ψ W s ⋙ pbcDerivedExtend (a.map W)),
      (Scalar.realization.{max u v, max u v} S) = eqToIso h →
      (scalarAtClosure.{u, v} l Ω Ψ W S).realization =
        eqToIso (scalarAtClosure_finiteEq.{u, v} l Ω Ψ W E n S h) := by
  intro s
  cases s <;> intro E n a S h hn <;> exact hn

/-- Endpoint restrictions of allowed derived coefficient extensions, independently of
compactifications and exceptional adjunctions.
Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26; scalar-mates plan steps 1 and 5
(blueprint: lem-sf-ring-endpoint-scalar-restrictions).

Proof: use the identity morphism of W and its canonical proper compactification.
The existing coherent ring-transport-family theorem supplies operations and normalized
system transport for this compactification. The existing integral scalar-mates core
then supplies its endpoint scalar restrictions, including the literal finite-target
restriction, the strict-tower integral restriction, both realization normalizations,
and shift compatibility. The multiplication-normalized scalar identities are
constructed by lifting the ambient identity through the fully faithful inclusion.

To use the equal-universe transport interface, replace Ω by ULift Ω and transport
algebraic closedness along its ring equivalence. At finite and integral stages the
categories, inclusions, shifts and triangles are independent of the closure. Case
analysis on the two ring stages therefore reuses the scalar functor, realization,
shift, additivity and exactness fields verbatim at the original universes. The same
case analysis transfers the finite equality and its eqToIso normalization, both
integral equations and the realization shift equation. For an identity map, compose
the scalar realization with the equality isomorphism to identity extension and the
ambient multiplication tensor unitor. Full faithfulness lifts this natural
isomorphism, and its image equation is exactly ScalarIdentity.normalized. Since
the compactification is always the canonical one of the identity of W, this choice
requires only W and does not depend on any geometric operation or
compactification supplied by a caller. The identity morphism is separated and
proper even when W is not separated over the base; no extra hypothesis is needed.
Empty W and positive level one are included in the two existing theorems. -/
theorem exists_ring_endpoint_scalar_restrictions
    (D : FiniteFieldDatum.{max u v}) (_hl : l ≠ D.p) (W : Scheme.{max u v})
    [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))] :
    ∃ scalar : ∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)),
      Allowed l a → Scalar.{u, v} l Ω a W,
    ∃ finiteScalar_eq : ∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (scalar a ha).functor ⋙ RingStage.inclusion.{u, v} l Ω W (.finite E n) =
        RingStage.inclusion.{u, v} l Ω W s ⋙ pbcDerivedExtend (a.map W),
    (∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (scalar a ha).realization = eqToIso (finiteScalar_eq E n a ha)) ∧
    (∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier),
      (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)).functor ⋙
          RingStage.inclusion.{u, v} l Ω W (.integral L) =
        RingStage.inclusion.{u, v} l Ω W (.integral E) ⋙
          integralScalarExtensionOfUniverses l E.carrier L.carrier i W) ∧
    (∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u, v} l Ω W (.integral E)),
      HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)).realization.inv.app K)
        ((completedScalarComparison l E.carrier L.carrier i W).app K.obj)) ∧
    (∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a), (scalar a ha).realization.hom.CommShift ℤ) ∧
    (∀ {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a),
      Nonempty (ScalarIdentity.{u, v} l Ω h W (scalar a ha))) := by
  classical
  let Ω' := ULift.{u} Ω
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (Padic l)
  have : IsAlgClosure (Padic l) Ω' :=
    { isAlgClosed := isAlgClosedOfEquiv (ULift.ringEquiv.symm : Ω ≃+* Ω')
      isAlgebraic := Algebra.IsAlgebraic.of_injective
        (ULift.algEquiv (R := Padic l)).toAlgHom ULift.down_injective }
  let c := Compactification.ofIsProper (𝟙 W)
  obtain ⟨operation, left, ⟨tr⟩⟩ :=
    exists_exceptional_ring_transport_family l Ω' D _hl (𝟙 W) c
  obtain ⟨d, _, _⟩ := ExceptionalIntegralScalar.exceptionalIntegralScalarMates_core
    l Ω' D _hl c operation left tr
  let scalar : ∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)),
      Allowed l a → Scalar.{u, v} l Ω a W := fun a ha ↦
    scalarAtClosure.{u, v} l Ω Ω' W (d.scalar a ha true)
  have finite_eq : ∀ {s : RingStage.{max u v} l}
      (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (scalar a ha).functor ⋙ RingStage.inclusion.{u, v} l Ω W (.finite E n) =
        RingStage.inclusion.{u, v} l Ω W s ⋙ pbcDerivedExtend (a.map W) := by
    intro s E n a ha
    exact scalarAtClosure_finiteEq.{u, v} l Ω Ω' W E n (d.scalar a ha true)
      (d.finiteScalar_eq E n a ha true)
  refine ⟨scalar, finite_eq, ?_, ?_, ?_, ?_, ?_⟩
  · intro s E n a ha
    exact scalarAtClosure_finiteNormalized.{u, v} l Ω Ω' W E n (d.scalar a ha true)
      (d.finiteScalar_eq E n a ha true) (d.finiteScalar_normalized E n a ha true)
  · intro E L i
    exact d.integralScalar_eq E L i true
  · intro E L i K
    exact d.integralScalar_normalized E L i true K
  · intro s t a ha
    exact scalarAtClosure_shift.{u, v} l Ω Ω' W (d.scalar a ha true) (d.scalarShift a ha true)
  · intro s a h ha
    exact scalarIdentityAtClosure.{u, v} l Ω Ω' W h (d.scalar a ha true)
      (d.scalarIdentity a h ha true)

end WeilConjectures.ConstructibleExceptionalCoefficients
