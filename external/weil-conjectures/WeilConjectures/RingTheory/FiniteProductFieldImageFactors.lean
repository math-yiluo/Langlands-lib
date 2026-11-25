/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Algebra.Pi

import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small

/-!
# Finite domain factors from a product embedding

Source: the coordinate-factor argument in the docstring of
`exists_spread_generic_product_domains`, smooth purity blueprint,
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-finite-product-field-image-factors)
-/

@[expose] public section

set_option autoImplicit false

universe u v

/-- A finite algebra embedded into a product of fields, containing all coordinate
idempotents and clearing denominators in every coordinate, is a product of finite domains
whose fraction fields are those fields. The factors lie in the base ring's universe.

Source: `lem-weil-pbc-spread-generic-product-domains`, proof step 2 and the
universe-presentation part of step 3, from the finite-algebra calculation in the smooth
purity blueprint `lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-finite-product-field-image-factors)

Proof: For each coordinate j, take T j to be the image subalgebra of the coordinate
map. Its underlying ring is a domain because it is a subring of a field. It is a finite
module as a quotient of C. The induced map from C to the product of T j is injective
by injectivity of the original product map. Given a tuple in the product, choose a
preimage of each coordinate, multiply it by a lift of the corresponding coordinate
idempotent, and sum. This proves surjectivity, including the empty product case, where
the sum is zero. A denominator identity expresses every element of L j as the ratio
of two elements of T j, with denominator the image of a nonzero base element; base
injectivity makes it nonzero. Apply IsFractionRing.of_field to the injective inclusion.
Finally T j is small by Module.Finite.small; take D j to be Shrink T j and transport
its inclusion, finiteness, domain, fraction-ring structures, and product equivalence.
The transported inclusion commutes with the base map, giving the scalar tower. -/
theorem exists_finite_domain_factors_of_product_embedding
    (R : Type u) [CommRing R] (C : Type v) [CommRing C] [Algebra R C]
    [Module.Finite R C] (r : ℕ) (L : Fin r → Type (max u v))
    [∀ j, Field (L j)] [∀ j, Algebra R (L j)]
    (hbase : ∀ j, Function.Injective (algebraMap R (L j)))
    (f : C →ₐ[R] (∀ j, L j)) (hf : Function.Injective f)
    (hid : ∀ j, ∃ e, ∀ i, f e i = if i = j then 1 else 0)
    (hden : ∀ j (z : L j), ∃ a : R, a ≠ 0 ∧
      ∃ x, algebraMap R (L j) a * z = f x j) :
    ∃ (D : Fin r → Type u) (_ : ∀ j, CommRing (D j))
      (_ : ∀ j, Algebra R (D j)) (_ : ∀ j, Algebra (D j) (L j))
      (_ : ∀ j, IsScalarTower R (D j) (L j)),
      (∀ j, Module.Finite R (D j) ∧ IsDomain (D j) ∧ IsFractionRing (D j) (L j)) ∧
      Nonempty (C ≃ₐ[R] (∀ j, D j)) := by
  classical
  let q : ∀ j, C →ₐ[R] L j := fun j ↦ (Pi.evalAlgHom R L j).comp f
  let T : ∀ j, Subalgebra R (L j) := fun j ↦ (q j).range
  have hfinite (j) : Module.Finite R (T j) :=
    Module.Finite.of_surjective (q j).rangeRestrict.toLinearMap (q j).rangeRestrict_surjective
  let ψ : C →ₐ[R] (∀ j, T j) := AlgHom.pi fun j ↦ (q j).rangeRestrict
  have hψinj : Function.Injective ψ := by
    intro x y h
    apply hf
    funext j
    exact congrArg Subtype.val (congrFun h j)
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : ∀ j, ∃ x, q j x = (y j).val := fun j ↦ (y j).property
    choose x hx using hy
    choose e he using hid
    refine ⟨∑ j, e j * x j, ?_⟩
    funext i
    apply Subtype.ext
    change f (∑ j, e j * x j) i = (y i).val
    simp only [map_sum, map_mul, Finset.sum_apply, Pi.mul_apply, he]
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, q, AlgHom.comp_apply, Pi.evalAlgHom_apply] using hx i
  have hfrac (j) : IsFractionRing (T j) (L j) := by
    have : FaithfulSMul (T j) (L j) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
    apply IsFractionRing.of_field
    intro z
    obtain ⟨a, ha, x, hx⟩ := hden j z
    refine ⟨(q j).rangeRestrict x, algebraMap R (T j) a, ?_⟩
    change z = q j x / algebraMap R (L j) a
    apply (eq_div_iff ((map_ne_zero_iff _ (hbase j)).mpr ha)).mpr
    simpa only [mul_comm, q, AlgHom.comp_apply, Pi.evalAlgHom_apply] using hx
  have hsmall (j) : Small.{u} (T j) := Module.Finite.small R (T j)
  let D : Fin r → Type u := fun j ↦ Shrink.{u} (T j)
  let e : ∀ j, D j ≃ₐ[R] T j := fun j ↦ Shrink.algEquiv R (T j)
  let : ∀ j, Algebra (D j) (L j) := fun j ↦
    ((T j).val.toRingHom.comp (e j).toRingHom).toAlgebra
  have htower (j) : IsScalarTower R (D j) (L j) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap R (L j) a = ((e j) (algebraMap R (D j) a)).val
    rw [(e j).commutes]
    rfl
  have hDfinite (j) : Module.Finite R (D j) :=
    Module.Finite.equiv (e j).symm.toLinearEquiv
  have hDfrac (j) : IsFractionRing (D j) (L j) :=
    IsFractionRing.of_ringEquiv_left (e j).toRingEquiv (fun _ ↦ rfl)
  refine ⟨D, inferInstance, inferInstance, inferInstance, htower, ?_, ?_⟩
  · intro j
    exact ⟨hDfinite j, inferInstance, hDfrac j⟩
  · exact ⟨(AlgEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans
      (AlgEquiv.piCongrRight fun j ↦ (e j).symm)⟩

