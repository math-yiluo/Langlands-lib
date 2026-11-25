/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # Bounded complementary monomials span the generated subfield -/

@[expose] public section
set_option autoImplicit false
universe u w
attribute [local instance] ZMod.algebra
namespace RingTheory

/-- The complementary generated subfield is contained in the span of bounded
complementary monomials; no p-basis hypothesis is needed.

Source: Stacks Project, Tag 07P5, coefficient subfield in the first proof paragraph,
with the exponent-reduction argument expanded.
(blueprint: lem-weil-pbc-p-basis-complement-monomial-span).

Proof: Let F = F_p(k^p) and W be the F-span in question. The zero exponent gives
1 and single exponents give the complementary generators, since p > 1. For any
finitely supported complementary exponent D, divide each exponent by p. Its
monomial is the p-th power of the quotient monomial times the bounded remainder
monomial, hence is in W. Products of bounded monomials are therefore in W, and
bilinearity proves W is closed under multiplication. Every p-th power is in F.
For a nonzero a in W, the identity a inverse = (a^p) inverse times a^(p-1)
shows closure under inverses. W is consequently a subfield containing the
p-th powers and all complementary generators. The defining subfield closure
is contained in W. For empty J the same argument applies; for empty I the only
monomial is 1 and the resulting field is F. -/
theorem pBasisComplementMonomial_mem_span
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k) (J : Finset I) (kJ : Subfield k)
    (hkJ : kJ = Subfield.closure
      (Set.range (fun x : k ↦ x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x}))
    (a : kJ) :
    (a : k) ∈ Submodule.span
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k ↦ x ^ p)))
      (Set.range (fun D : {D : I →₀ ℕ //
        (∀ i, D i < p) ∧ ∀ i ∈ J, D i = 0} ↦
        (D : I →₀ ℕ).prod (fun i e ↦ t i ^ e))) := by
  classical
  let F := IntermediateField.adjoin (ZMod p) (Set.range (fun x : k ↦ x ^ p))
  let C := {D : I →₀ ℕ // (∀ i, D i < p) ∧ ∀ i ∈ J, D i = 0}
  let mon (D : I →₀ ℕ) := D.prod (fun i e ↦ t i ^ e)
  let W : Submodule F k := Submodule.span F (Set.range (fun D : C ↦ mon D))
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpow (x : k) : x ^ p ∈ F := IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  have hscalar (c : F) (x : k) : c • x = (c : k) * x := rfl
  have hone : (1 : k) ∈ W := by
    exact Submodule.subset_span ⟨⟨0, by simp [hp]⟩, by simp [mon]⟩
  have hmon (D : I →₀ ℕ) (hD : ∀ i ∈ J, D i = 0) : mon D ∈ W := by
    let R : I →₀ ℕ := D.mapRange (fun n ↦ n % p) (Nat.zero_mod p)
    have hR : (∀ i, R i < p) ∧ ∀ i ∈ J, R i = 0 := by
      constructor
      · intro i
        exact Nat.mod_lt _ hp
      · intro i hi
        simp [R, hD i hi]
    let q : k := D.prod (fun i e ↦ t i ^ (e / p))
    have heq : mon D = q ^ p * mon R := by
      dsimp only [mon]
      rw [Finsupp.prod_of_support_subset R Finsupp.support_mapRange
        (fun i e ↦ t i ^ e) (by intro i _; exact pow_zero _)]
      simp only [q, Finsupp.prod]
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [← pow_mul, ← pow_add]
      congr 1
      simpa only [R, Finsupp.mapRange_apply, Nat.mul_comm] using
        (Nat.div_add_mod (D i) p).symm
    rw [heq]
    exact (hscalar (⟨q ^ p, hpow q⟩ : F) (mon R)) ▸
      W.smul_mem (⟨q ^ p, hpow q⟩ : F) (Submodule.subset_span ⟨⟨R, hR⟩, rfl⟩)
  have hmul (x y : k) (hx : x ∈ W) (hy : y ∈ W) : x * y ∈ W := by
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨D, rfl⟩ := hx
      obtain ⟨E, rfl⟩ := hy
      have heq : mon (D + E) = mon D * mon E :=
        Finsupp.prod_add_index' (fun i ↦ pow_zero (t i)) (fun i a b ↦ pow_add (t i) a b)
      rw [← heq]
      apply hmon
      intro i hi
      simp [D.property.2 i hi, E.property.2 i hi]
    | zero_left y hy => simp
    | zero_right x hx => simp
    | add_left x y z hx hy hz hxz hyz =>
      simpa only [add_mul] using W.add_mem hxz hyz
    | add_right x y z hx hy hz hxy hxz =>
      simpa only [mul_add] using W.add_mem hxy hxz
    | smul_left c x y hx hy hxy =>
      simpa only [smul_mul_assoc] using W.smul_mem c hxy
    | smul_right c x y hx hy hxy =>
      simpa only [mul_smul_comm] using W.smul_mem c hxy
  have hpowW (x : k) (hx : x ∈ W) (n : ℕ) : x ^ n ∈ W := by
    induction n with
    | zero => simpa using hone
    | succ n hn => simpa only [pow_succ] using hmul _ _ hn hx
  have hinv (x : k) (hx : x ∈ W) : x⁻¹ ∈ W := by
    by_cases hzero : x = 0
    · simp [hzero]
    have heq : x⁻¹ = (x ^ p)⁻¹ * x ^ (p - 1) := by
      apply (mul_left_cancel₀ hzero)
      calc
        x * x⁻¹ = 1 := mul_inv_cancel₀ hzero
        _ = x * ((x ^ p)⁻¹ * x ^ (p - 1)) := by
          rw [mul_left_comm x, ← pow_succ', Nat.sub_add_cancel hp,
            inv_mul_cancel₀ (pow_ne_zero _ hzero)]
    rw [heq]
    exact (hscalar (⟨(x ^ p)⁻¹, F.inv_mem (hpow x)⟩ : F) _) ▸
      W.smul_mem (⟨(x ^ p)⁻¹, F.inv_mem (hpow x)⟩ : F) (hpowW x hx (p - 1))
  let L : Subfield k :=
    { carrier := W
      zero_mem' := W.zero_mem
      one_mem' := hone
      add_mem' := W.add_mem
      neg_mem' := W.neg_mem
      mul_mem' := fun hx hy ↦ hmul _ _ hx hy
      inv_mem' := hinv }
  have hcl : Subfield.closure
      (Set.range (fun x : k ↦ x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x}) ≤ L := by
    apply Subfield.closure_le.mpr
    rintro x (⟨y, rfl⟩ | ⟨i, hi, rfl⟩)
    · change y ^ p ∈ W
      simpa only [hscalar, mul_one] using W.smul_mem (⟨y ^ p, hpow y⟩ : F) hone
    · have hsingle : mon (Finsupp.single i 1) = t i := by simp [mon]
      rw [← hsingle]
      apply hmon
      intro j hj
      have hne : j ≠ i := by rintro rfl; exact hi hj
      simp [hne]
  exact hcl (hkJ ▸ a.property)

end RingTheory
