/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Jacobson.Ring
public import WeilConjectures.FieldTheory.AlgebraicallyClosedInTensor

/-!
# The constant field of an integrally closed domain

Let `A` be an integrally closed domain containing a field `k`. The *constant field* of `A` over
`k` is the integral closure `k'` of `k` in `A`; it is a field
(`Subalgebra.isField_integralClosure`). It is integrally closed in the fraction field `K` of `A`,
so for every separable algebraic extension `L` of `k'` the ring `A ⊗[k'] L` is a domain
(`Algebra.TensorProduct.isDomain_integralClosure_tensorProduct`): it embeds into `K ⊗[k'] L`,
which is a domain by `Algebra.TensorProduct.isDomain_of_isSeparable`.

Geometrically: a normal integral affine scheme is geometrically irreducible over its constant
field.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]

/-- The integral closure of a field in a domain is a field. -/
theorem isField_integralClosure : IsField (integralClosure k A) :=
  isField_of_isIntegral_of_isField' (R := k) (S := integralClosure k A) (Field.toIsField k)

/-- The integral closure of `k` in `A`, as a field. -/
noncomputable abbrev ConstantField (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] : Type _ :=
  integralClosure k A

noncomputable instance : Field (ConstantField k A) := isField_integralClosure.toField

variable [IsIntegrallyClosed A]

/-- The constant field is integrally closed in the fraction field: an element of `Frac A`
integral over `k'` is integral over `k`, hence over `A`, hence in `A`, hence in `k'`. -/
theorem mem_range_of_isIntegral_constantField {x : FractionRing A}
    (hx : IsIntegral (ConstantField k A) x) :
    x ∈ (algebraMap (ConstantField k A) (FractionRing A)).range := by
  have hk : IsIntegral k x := isIntegral_trans (R := k) (A := ConstantField k A) x hx
  have hA : IsIntegral A x := hk.tower_top
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  have ha : IsIntegral k a := (isIntegral_algHom_iff (IsScalarTower.toAlgHom k A (FractionRing A))
    (IsFractionRing.injective A (FractionRing A))).1 hk
  exact ⟨⟨a, ha⟩, rfl⟩

/-- **Geometric irreducibility over the constant field.** For an integrally closed domain `A`
containing `k` with constant field `k'` and a separable algebraic extension `L/k'`, the ring
`A ⊗[k'] L` is a domain. -/
theorem isDomain_constantField (L : Type*) [Field L] [Algebra (ConstantField k A) L]
    [Algebra.IsSeparable (ConstantField k A) L] : IsDomain (A ⊗[ConstantField k A] L) := by
  have := isDomain_of_isSeparable (K := FractionRing A) L
    (fun x hx ↦ mem_range_of_isIntegral_constantField (k := k) (A := A) hx)
  let f := Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom (ConstantField k A) A (FractionRing A))
    (AlgHom.id (ConstantField k A) L)
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := L)
      (IsScalarTower.toAlgHom (ConstantField k A) A (FractionRing A)).toLinearMap
      (IsFractionRing.injective A (FractionRing A))
  exact hf.isDomain f.toRingHom

omit [IsIntegrallyClosed A] in
/-- The constant field of a domain of finite type over a finite field is finite: it embeds into
the residue field at a maximal ideal, which is finite over `k` by the Nullstellensatz. -/
theorem finite_constantField [Finite k] [Algebra.FiniteType k A] : Finite (ConstantField k A) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let _ := Ideal.Quotient.field m
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have : Finite (A ⧸ m) := Module.finite_of_finite k
  let g : ConstantField k A →+* A ⧸ m := (Ideal.Quotient.mk m).comp (integralClosure k A).val
  exact Finite.of_injective g g.injective

end Algebra.TensorProduct
