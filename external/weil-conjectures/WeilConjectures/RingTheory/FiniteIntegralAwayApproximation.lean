/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite approximation of an integral-closure localization

Source: Stacks Project, Tag 09XI, proof of (5) implies (2), construction of B''.
(blueprint: lem-weil-pbc-finite-integral-away-approximation)
-/

@[expose] public section

universe u v

namespace Algebra

/-- A principal localization isomorphism from the integral closure descends to a finite
subalgebra, retaining an idempotent congruence for its parameter.

Source: Stacks Project, Tag 09XI, proof of (5) implies (2), construction of B''.
(blueprint: lem-weil-pbc-finite-integral-away-approximation)

Proof:
1. Choose finitely many algebra generators x of B. Surjectivity of the localization
map gives y in the integral closure and n with y = g^n x in B, for each generator.
2. Express g*g-g as a finite sum of elements of I times integral-closure elements.
Generate an A-subalgebra by g, all y, and the elements in this expression. Their
integrality and finiteness make this subalgebra D module-finite over A.
3. The recorded expression gives b*b-b in ID, where b is g regarded in D, so its
quotient image is idempotent. Localized inclusion is injective, since any equality
of fractions can be cleared in B and hence in its subring D. It is surjective:
the image contains the inverse of g and the generators x=y/g^n, so every fraction
in B[1/g] is in its image. -/
theorem exists_finite_integral_away_approximation
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (I : Ideal A) (g : integralClosure A B)
    (hg : IsIdempotentElem
      (Ideal.Quotient.mk (I.map (algebraMap A (integralClosure A B))) g))
    (hloc : Function.Bijective
      (Localization.awayMap (integralClosure A B).val.toRingHom g)) :
    ∃ (D : Subalgebra A B) (_ : Module.Finite A D) (b : D),
      b.1 = g.1 ∧ IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A D)) b) ∧
      Function.Bijective (Localization.awayMap D.val.toRingHom b) := by
  classical
  let S := integralClosure A B
  let : Algebra.IsIntegral A S := ⟨fun x ↦
    (isIntegral_algHom_iff S.val Subtype.val_injective).mp x.2⟩
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  have hsurj := Localization.awayMap_surjective_iff.mp hloc.2
  choose y m hym using hsurj
  have hmem : g * g - g ∈ I.map (algebraMap A S) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, hg.eq, sub_self]
  change g * g - g ∈ Submodule.span S
    ((algebraMap A S) '' (I : Set A)) at hmem
  rw [Set.image_eq_range] at hmem
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  let t := insert g (s.image y ∪ l.support.image l)
  let T := Algebra.adjoin A (↑t : Set S)
  have ht : (↑t : Set S) ⊆ T := Algebra.subset_adjoin
  let g' : T := ⟨g, ht (by simp [t])⟩
  have hcoeff : ∀ a : (I : Set A), l a ∈ T := by
    intro a
    by_cases ha : a ∈ l.support
    · exact ht (by simp only [t, Finset.mem_coe, Finset.mem_insert,
        Finset.mem_union]; exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)))
    · rw [Finsupp.notMem_support_iff.mp ha]
      exact T.zero_mem
  let c : ↥(I : Set A) → T := fun a ↦ ⟨l a, hcoeff a⟩
  have hz : (∑ a ∈ l.support, c a * algebraMap A T a.1) = g' * g' - g' := by
    apply Subtype.ext
    simpa [c, Finsupp.sum, smul_eq_mul] using hl
  have hzmem : g' * g' - g' ∈ I.map (algebraMap A T) := by
    rw [← hz]
    exact sum_mem (fun a _ ↦
      Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ a.2))
  let D := T.map S.val
  let f : T ≃ₐ[A] D := T.equivMapOfInjective S.val Subtype.val_injective
  let b := f g'
  let : Module.Finite A T := Algebra.finite_adjoin_of_finite_of_isIntegral
    t.finite_toSet (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  have hD : Module.Finite A D := Module.Finite.of_surjective f.toLinearMap f.surjective
  have hbg : b.1 = g.1 := rfl
  have hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A D)) b) := by
    rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
    have hm : (I.map (algebraMap A T)).map f.toRingHom = I.map (algebraMap A D) := by
      rw [Ideal.map_map]
      congr 1
    rw [← hm]
    have h := Ideal.mem_map_of_mem f.toRingHom hzmem
    simpa [b] using h
  refine ⟨D, hD, b, hbg, hb,
    IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, ?_⟩
  have hgen : (IsScalarTower.toAlgHom A B (Localization.Away b.1)).range ≤
      (Localization.awayMapₐ D.val b).range := by
    rw [← Algebra.map_top, ← hs, Subalgebra.map_le, Algebra.adjoin_le_iff]
    intro x hx
    suffices ∃ a ∈ D, ∃ n, b.1 ^ n ∈ D ∧
        ∃ k, b.1 ^ k * a = b.1 ^ k * (x * b.1 ^ n) by
      simpa [(IsLocalization.mk'_surjective (.powers b)).exists,
        (IsLocalization.mk'_surjective (.powers b.1)).forall, Localization.awayMapₐ,
        IsLocalization.Away.map, IsLocalization.map_mk', Submonoid.mem_powers_iff,
        Subtype.ext_iff, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, ← map_pow,
        IsLocalization.eq_iff_exists (.powers b.1), Subalgebra.val]
    refine ⟨(y x).1, ?_, m x, pow_mem b.2 _, 0, ?_⟩
    · exact ⟨y x, ht (Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩))), rfl⟩
    · simpa [hbg, mul_comm] using hym x
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (.powers (D.val.toRingHom b)) x
  obtain ⟨y, hy : Localization.awayMap _ _ _ = _⟩ := hgen ⟨x, rfl⟩
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, map_pow, hy]
  simp [Localization.Away.invSelf, Localization.awayMap, ← Algebra.smul_def,
    IsLocalization.Away.map, IsLocalization.map_mk', Localization.mk_eq_mk',
    ← IsLocalization.mk'_pow]

end Algebra
