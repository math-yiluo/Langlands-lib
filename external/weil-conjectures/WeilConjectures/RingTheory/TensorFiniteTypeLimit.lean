/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Nilpotent.Defs

/-! # Finite-type reduction for tensor products

Source: literature/stacks-project/algebra.tex, Algebra, Lemma 00I3
(algebra-lemma-limit-argument) (blueprint: lem-weil-pbc-tensor-finite-type-limit)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra

private theorem lift_pair_right
    (k : Type u) [Field k]
    (R : Type v) [CommRing R] [Algebra k R]
    (S : Type w) [CommRing S] [Algebra k S] (x y : R ⊗[k] S) :
    ∃ (B : Subalgebra k S), B.FG ∧
      ∃ x' y' : R ⊗[k] B,
        TensorProduct.map (AlgHom.id R R) B.val x' = x ∧
        TensorProduct.map (AlgHom.id R R) B.val y' = y := by
  obtain ⟨B, hB, x', hx⟩ := exists_fg_and_mem_baseChange x
  obtain ⟨C, hC, y', hy⟩ := exists_fg_and_mem_baseChange y
  change TensorProduct.map (AlgHom.id R R) B.val x' = x at hx
  change TensorProduct.map (AlgHom.id R R) C.val y' = y at hy
  refine ⟨B ⊔ C, hB.sup hC,
    TensorProduct.map (AlgHom.id R R) (Subalgebra.inclusion le_sup_left) x',
    TensorProduct.map (AlgHom.id R R) (Subalgebra.inclusion le_sup_right) y', ?_, ?_⟩
  · simpa only [← AlgHom.comp_apply, ← TensorProduct.map_id_comp,
      Subalgebra.val_comp_inclusion] using hx
  · simpa only [← AlgHom.comp_apply, ← TensorProduct.map_id_comp,
      Subalgebra.val_comp_inclusion] using hy

private theorem zero_divisors_right
    (k : Type u) [Field k]
    (R : Type v) [CommRing R] [Algebra k R]
    (S : Type w) [CommRing S] [Algebra k S]
    (h : ∃ x y : R ⊗[k] S, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0) :
    ∃ (B : Subalgebra k S), B.FG ∧
      ∃ x y : R ⊗[k] B, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  obtain ⟨B, hB, x', y', hx', hy'⟩ := lift_pair_right k R S x y
  let f := TensorProduct.map (AlgHom.id R R) B.val
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  refine ⟨B, hB, x', y', ?_, ?_, ?_⟩
  · intro hzero
    apply hx
    rw [← hx', hzero, map_zero]
  · intro hzero
    apply hy
    rw [← hy', hzero, map_zero]
  · apply hf
    simpa only [f, map_mul, map_zero, hx', hy'] using hxy

private theorem zero_divisors_comm
    (k : Type u) [Field k]
    (R : Type v) [CommRing R] [Algebra k R]
    (S : Type w) [CommRing S] [Algebra k S]
    (h : ∃ x y : R ⊗[k] S, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0) :
    ∃ x y : S ⊗[k] R, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  let e := TensorProduct.comm k R S
  refine ⟨e x, e y, ?_, ?_, ?_⟩
  · simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hx
  · simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hy
  · rw [← map_mul, hxy, map_zero]

/-- Finite-type reduction for tensor products, clauses (1) and (2) of Stacks Algebra,
Lemma 00I3 (algebra-lemma-limit-argument).

Proof:
1. The finitely generated subalgebras of each factor form a directed system:
   adjoining the union of two finite generating sets gives a common upper bound,
   and each element belongs to the subalgebra it generates. Their filtered colimits
   are the full algebras; use `lem-weil-pbc-filtered-colimit-algebras-elementwise`.
2. For a nonzero nilpotent z with z^n = 0, first descend z to a finitely generated
   subalgebra of R with S fixed, and enlarge that stage until its nth power is zero.
   Then fix that stage and descend the element and its zero nth power to a finitely
   generated subalgebra of S. Use the representative and eventual-zero clauses of
   `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise` twice (with tensor
   symmetry on the second pass). Each representative is nonzero because its image
   is z. Thus the smaller tensor product is not reduced.
3. For nonzero x and y with xy = 0, descend both to a common finitely generated
   R-stage with S fixed, then enlarge it until their product vanishes. Next descend
   both to a common finitely generated S-stage with that R-stage fixed, and enlarge
   it until the product vanishes. Use the same tensor-colimit node's representative
   and eventual-zero assertions. Both resulting factors stay nonzero because their
   images are x and y, so the smaller tensor product has a nonzero zero-divisor.

(blueprint: lem-weil-pbc-tensor-finite-type-limit) -/
theorem tensor_finite_type_limit
    (k : Type u) [Field k]
    (R : Type v) [CommRing R] [Algebra k R]
    (S : Type w) [CommRing S] [Algebra k S] :
    (¬ IsReduced (R ⊗[k] S) →
      ∃ (R' : Subalgebra k R) (S' : Subalgebra k S),
        Algebra.FiniteType k R' ∧ Algebra.FiniteType k S' ∧
        ¬ IsReduced (R' ⊗[k] S')) ∧
    ((∃ x y : R ⊗[k] S, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0) →
      ∃ (R' : Subalgebra k R) (S' : Subalgebra k S),
        Algebra.FiniteType k R' ∧ Algebra.FiniteType k S' ∧
        ∃ x y : R' ⊗[k] S', x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0) := by
  constructor
  · intro h
    by_contra hno
    apply h
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro S' hS'
    have hswap : IsReduced (S' ⊗[k] R) := by
      apply IsReduced.tensorProduct_of_flat_of_forall_fg
      intro R' hR'
      have hr : IsReduced (R' ⊗[k] S') := by
        by_contra hn
        exact hno ⟨R', S', R'.fg_iff_finiteType.mp hR',
          S'.fg_iff_finiteType.mp hS', hn⟩
      have := hr
      exact isReduced_of_injective (TensorProduct.comm k S' R')
        (TensorProduct.comm k S' R').injective
    have := hswap
    exact isReduced_of_injective (TensorProduct.comm k R S')
      (TensorProduct.comm k R S').injective
  · intro h
    obtain ⟨R', hR', h⟩ := zero_divisors_right k S R (zero_divisors_comm k R S h)
    obtain ⟨S', hS', h⟩ := zero_divisors_right k R' S (zero_divisors_comm k S R' h)
    exact ⟨R', S', R'.fg_iff_finiteType.mp hR', S'.fg_iff_finiteType.mp hS', h⟩

end Algebra
