/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Unramified.Field

/-! # Reducedness of generic tensor algebras for a DVR root extension

Source: Stacks Project, Tag 09EV, and separable extension base change.
(blueprint: lem-sbc-dvr-galois-root-tensor-reduced) -/

@[expose] public section

universe u
open scoped TensorProduct
namespace RingTheory

/-- The generic tensor algebra of a positive-degree uniformizer root is reduced.

Source: Stacks Project, Tag 09EV, and finite separable extension base change.
(blueprint: lem-sbc-dvr-galois-root-tensor-reduced)

Proof: Put K = Frac(B) and A = B[t]/(t^n-pi). The polynomial is
Eisenstein at (pi): it is monic, every coefficient below the leading
coefficient lies in (pi), and its constant coefficient -pi does not lie
in (pi)^2, since pi is irreducible. Eisenstein's criterion makes it
irreducible and therefore prime over the DVR B. Thus A is a domain.
The monic positive-degree quotient embeds B in A and then in L = Frac(A).
Lift the B-algebra structure on L to K. The given B-structure on E
forms a tower B -> K -> E. Since K is B-flat and E is K-flat, E is
B-flat. Hence the inclusion A -> L induces an injection
E tensor_B A -> E tensor_B L. The latter is canonically
E tensor_K L, since K is a localization of B. The Galois extension
E/K is separable and finite, so L tensor_K E is formally unramified
and essentially of finite type over the field L, hence reduced.
Commuting the factors and restricting along the injection proves
reducedness. The same Eisenstein argument works for n = 1; no
invertibility of n or separability of L/K is needed. -/
theorem dvr_galois_root_tensor_reduced
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧ IsGalois (FractionRing B) E) :
    let : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp
        (algebraMap B (FractionRing B))).toAlgebra
    IsReduced (E ⊗[B]
      AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)) := by
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp
      (algebraMap B (FractionRing B))).toAlgebra
  let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
  have hmon := Polynomial.monic_X_pow_sub_C pi (Nat.ne_of_gt hnpos)
  have heis : ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi).IsEisensteinAt
      (Ideal.span {pi}) := by
    refine hmon.isEisensteinAt_of_mem_of_notMem ?_ ?_ ?_
    · exact (Ideal.span_singleton_eq_top).not.mpr hpi.not_isUnit
    · intro k hk
      rw [Polynomial.natDegree_X_pow_sub_C] at hk
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        ite_eq_right (Nat.ne_of_lt hk), zero_sub]
      by_cases hk0 : k = 0
      · subst k
        simp [Polynomial.coeff_C]
      · simp [Polynomial.coeff_C, hk0]
    · simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        ite_eq_right (Nat.ne_of_gt hnpos).symm, Polynomial.coeff_C_zero, zero_sub,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton, dvd_neg]
      simpa only [pow_one] using
        (pow_dvd_pow_iff hpi.ne_zero hpi.not_isUnit).not.mpr (by omega : ¬ 2 ≤ 1)
  have hprime : (Ideal.span {pi}).IsPrime :=
    (Ideal.span_singleton_prime hpi.ne_zero).mpr (irreducible_iff_prime.mp hpi)
  have hirr := heis.irreducible hprime hmon.isPrimitive
    (by simpa only [Polynomial.natDegree_X_pow_sub_C] using hnpos)
  have : IsDomain A := AdjoinRoot.isDomain_of_prime (irreducible_iff_prime.mp hirr)
  have hBA : Function.Injective (algebraMap B A) :=
    AdjoinRoot.of.injective_of_degree_ne_zero
      (by rw [Polynomial.degree_X_pow_sub_C hnpos];
          exact_mod_cast (Nat.ne_of_gt hnpos))
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hBA
  have : FaithfulSMul B (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective B (FractionRing A)).mpr
      ((IsFractionRing.injective A (FractionRing A)).comp hBA)
  let : Algebra (FractionRing B) (FractionRing A) := FractionRing.liftAlgebra B _
  have : IsScalarTower B (FractionRing B) (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra B _
  have : IsScalarTower B (FractionRing B) E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Flat B E := Module.Flat.trans B (FractionRing B) E
  let g : A →ₐ[B] FractionRing A := IsScalarTower.toAlgHom B A (FractionRing A)
  let f : E ⊗[B] A →ₐ[B] E ⊗[B] FractionRing A :=
    Algebra.TensorProduct.map (AlgHom.id B E) g
  have hf : Function.Injective f := by
    change Function.Injective
      (_root_.TensorProduct.map (LinearMap.id : E →ₗ[B] E) g.toLinearMap)
    exact Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap
      (IsFractionRing.injective A (FractionRing A))
  let e := IsLocalization.algebraTensorEquiv (nonZeroDivisors B) (FractionRing B)
    E (FractionRing A)
  have : FiniteDimensional (FractionRing B) E := hE.1
  have : IsGalois (FractionRing B) E := hE.2
  have : Algebra.FormallyUnramified (FractionRing B) E :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  have : Algebra.FormallyUnramified (FractionRing A) (FractionRing A ⊗[FractionRing B] E) :=
    inferInstance
  have : IsReduced (FractionRing A ⊗[FractionRing B] E) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing A) _
  exact isReduced_of_injective
    (((Algebra.TensorProduct.comm (FractionRing B) E (FractionRing A)).toRingHom).comp
      (e.symm.toRingHom.comp f.toRingHom))
    ((Algebra.TensorProduct.comm (FractionRing B) E (FractionRing A)).injective.comp
      (e.symm.injective.comp hf))

end RingTheory
