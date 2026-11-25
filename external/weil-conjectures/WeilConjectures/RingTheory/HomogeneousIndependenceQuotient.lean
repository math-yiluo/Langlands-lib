/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Filtration
import WeilConjectures.Mathlib.RingTheory.Ideal.Operations

/-!
# Removing one variable from a polynomial associated graded ring

Source: the local dimension argument in blueprint
`lemma-connected-components-images-homomorphisms--3`, clause (2), expanded in
`lem-wf-height-of-homogeneous-independence`, steps 3 and 4.
-/

@[expose] public section

open MvPolynomial

namespace IsLocalRing

private theorem homogeneous_eval_mem_pow
    {k A ι : Type*} [Field k] [CommRing A] [Algebra k A]
    {I : Ideal A} {x : ι → A} (hx : ∀ i, x i ∈ I)
    {f : MvPolynomial ι k} {r : ℕ} (hf : f.IsHomogeneous r) : aeval x f ∈ I ^ r := by
  have hmem : aeval x f ∈ (Ideal.span (Set.range x)) ^ r := by
    apply (Ideal.mem_span_pow_iff_exists_isHomogeneous x _).mpr
    refine ⟨MvPolynomial.map (algebraMap k A) f, hf.map _, ?_⟩
    simp only [eval_map]
    rfl
  exact pow_le_pow_left' (Ideal.span_le.mpr (Set.range_subset_iff.mpr hx)) r hmem

private theorem homogeneous_representatives
    {k A ι : Type*} [Field k] [CommRing A] [Algebra k A] [Finite ι]
    (I : Ideal A) (x : ι → A)
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ I)
    (hgen : I = Ideal.span (Set.range x)) {r : ℕ} {a : A} (ha : a ∈ I ^ r) :
    ∃ f : MvPolynomial ι k, f.IsHomogeneous r ∧ a - aeval x f ∈ I ^ (r + 1) := by
  classical
  let := Fintype.ofFinite ι
  have hx (i : ι) : x i ∈ I := hgen ▸ Ideal.mem_span_range_self
  have hspan (b : A) (hb : b ∈ I) : ∃ c : ι → k,
      b - ∑ i, algebraMap k A (c i) * x i ∈ I ^ 2 := by
    rw [hgen, Ideal.span, Submodule.mem_span_range_iff_exists_fun] at hb
    obtain ⟨d, hd⟩ := hb
    choose c hc using fun i ↦ hres (d i)
    refine ⟨c, ?_⟩
    rw [← hd, ← Finset.sum_sub_distrib]
    apply Ideal.sum_mem _
    intro i _
    rw [smul_eq_mul, ← sub_mul, pow_two]
    exact Ideal.mul_mem_mul (hc i) (hx i)
  induction r generalizing a with
  | zero =>
    obtain ⟨c, hc⟩ := hres a
    exact ⟨C c, isHomogeneous_C _ _, by simpa using hc⟩
  | succ r ih =>
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun a ha b hb ↦ ?_) ?_
    · obtain ⟨f, hf, ha'⟩ := ih ha
      obtain ⟨c, hb'⟩ := hspan b hb
      refine ⟨f * ∑ i, C (c i) * X i,
        hf.mul (IsHomogeneous.sum _ _ _ fun i _ ↦ isHomogeneous_C_mul_X _ _), ?_⟩
      let s := ∑ i, algebraMap k A (c i) * x i
      have hs : aeval x (∑ i, C (c i) * X i) = s := by simp [s]
      have hsI : s ∈ I := Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hx i)
      have hF := homogeneous_eval_mem_pow hx hf
      rw [map_mul, hs, show a * b - aeval x f * s =
        (a - aeval x f) * s + aeval x f * (b - s) +
        (a - aeval x f) * (b - s) by ring]
      refine add_mem (add_mem ?_ ?_) ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ha' hsI
      · rw [show r + 1 + 1 = r + 2 by omega, pow_add]
        exact Ideal.mul_mem_mul hF hb'
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ha' (Ideal.pow_le_self two_ne_zero hb')
    · rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
      refine ⟨f + g, hf.add hg, ?_⟩
      rw [map_add, add_sub_add_comm]
      exact add_mem ha hb

/-- Source: blueprint `lem-wf-height-of-homogeneous-independence`, steps 3 and 4,
following Waterhouse, *Introduction to Affine Group Schemes*, §11.4.

Proof in words: write m for the maximal ideal. Every residue class is represented by k.
Since the x_i generate m, the degree-r
monomials span m^r/m^(r+1). The independence hypothesis makes this graded piece exactly
the degree-r part of the polynomial ring over k. Krull intersection makes the m-adic
filtration separated. Every nonzero y therefore has a finite order d, and multiplication
of its initial form by X_0 is nonzero. Consequently x_0 y has order d+1; in particular
x_0 is a nonzerodivisor. Moreover, if x_0 y lies in m^r then y lies in m^(r-1).
For a homogeneous polynomial f in the remaining variables whose value in A/(x_0) lies
in the image of m^(r+1), lift this assertion to f(x)=z+x_0 y with z in m^(r+1).
The strictness just proved implies y in m^(r-1) when r>0. Represent its initial form
by a degree-(r-1) polynomial g. Then f-X_0 g has value in m^(r+1), so independence
in A gives f=X_0 g. Since f does not involve X_0, it is zero. For r=0, reduce modulo
m and use degree-zero independence directly. This also covers the one-variable case,
where the remaining polynomial ring is k.
(blueprint: lem-wf-homogeneous-independence-quotient). -/
theorem homogeneous_independence_quotient
    {k A : Type*} [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
    [IsLocalRing A] {n : ℕ} (x : Fin (n + 1) → A)
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ maximalIdeal A)
    (hgen : maximalIdeal A = Ideal.span (Set.range x))
    (hind : ∀ (r : ℕ) (f : MvPolynomial (Fin (n + 1)) k), f.IsHomogeneous r →
      aeval x f ∈ maximalIdeal A ^ (r + 1) → f = 0) :
    x 0 ∈ nonZeroDivisors A ∧
      ∀ (r : ℕ) (f : MvPolynomial (Fin n) k), f.IsHomogeneous r →
        aeval (fun i ↦ Ideal.Quotient.mk (Ideal.span {x 0}) (x i.succ)) f ∈
          (Ideal.map (Ideal.Quotient.mk (Ideal.span {x 0})) (maximalIdeal A)) ^ (r + 1) →
        f = 0 := by
  classical
  let m := maximalIdeal A
  have hx (i : Fin (n + 1)) : x i ∈ m := by
    change x i ∈ maximalIdeal A
    rw [hgen]
    exact Ideal.mem_span_range_self
  have horder (d : ℕ) (a : A) (ha : a ∈ m ^ d) (ha' : a ∉ m ^ (d + 1)) :
      x 0 * a ∉ m ^ (d + 2) := by
    obtain ⟨g, hg, hag⟩ := homogeneous_representatives m x hres hgen ha
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact ha' (by simpa using hag)
    intro hmul
    have hprod : X 0 * g = (0 : MvPolynomial (Fin (n + 1)) k) := by
      apply hind (d + 1) _
      · simpa only [Nat.add_comm 1] using (isHomogeneous_X k 0).mul hg
      · have he : x 0 * (a - aeval x g) ∈ m ^ (d + 2) := by
          rw [show d + 2 = 1 + (d + 1) by omega, pow_add, pow_one]
          exact Ideal.mul_mem_mul (hx 0) hag
        have hsub := (m ^ (d + 2)).sub_mem hmul he
        simpa only [map_mul, aeval_X, mul_sub, sub_sub_cancel] using hsub
    exact mul_ne_zero (X_ne_zero 0) hg0 hprod
  have hstrict (r : ℕ) (a : A) (ha : x 0 * a ∈ m ^ (r + 1)) : a ∈ m ^ r := by
    by_contra hnot
    have hn : a ∉ ⨅ d : ℕ, m ^ d := fun h ↦ hnot ((Ideal.mem_iInf.mp h) r)
    obtain ⟨d, hd, hd'⟩ := Ideal.exists_mem_pow_notMem_pow_succ_of_notMem_iInf hn
    have hdr : d < r := by
      by_contra h
      exact hnot (Ideal.pow_le_pow_right (Nat.le_of_not_gt h) hd)
    exact horder d a hd hd' (Ideal.pow_le_pow_right (by omega) ha)
  have hreg : x 0 ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    have hmsep : (⨅ d : ℕ, m ^ d) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing m (maximalIdeal.isMaximal A).ne_top
    have hmem : a ∈ ⨅ d : ℕ, m ^ d := by
      apply Ideal.mem_iInf.mpr
      intro d
      exact hstrict d a (ha ▸ Ideal.zero_mem _)
    simpa only [hmsep, Ideal.mem_bot] using hmem
  refine ⟨hreg, ?_⟩
  intro r f hf hmem
  let J : Ideal A := Ideal.span {x 0}
  let q : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J
  let F : MvPolynomial (Fin (n + 1)) k := rename Fin.succ f
  have hF : F.IsHomogeneous r := hf.rename_isHomogeneous
  have heval : q (aeval x F) =
      aeval (fun i ↦ Ideal.Quotient.mk J (x i.succ)) f := by
    rw [comp_aeval_apply, aeval_rename]
    rfl
  change _ ∈ (Ideal.map q.toRingHom m) ^ (r + 1) at hmem
  rw [← heval, ← Ideal.map_pow] at hmem
  obtain ⟨z, hz, hzeq⟩ :=
    (Ideal.mem_map_iff_of_surjective q.toRingHom Ideal.Quotient.mk_surjective).mp hmem
  change q z = q (aeval x F) at hzeq
  have hJ : aeval x F - z ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (aeval x F - z) = 0
    rw [map_sub, hzeq, sub_self]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hJ
  have hxb : x 0 * b = aeval x F - z := by simpa only [mul_comm] using hb
  have hJle : J ≤ m := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hx 0))
  cases r with
  | zero =>
    have hfx : aeval x F ∈ m := by
      have hz' : z ∈ m := by simpa using hz
      have hsum := m.add_mem (hJle hJ) hz'
      simpa only [sub_add_cancel] using hsum
    have hzero := hind 0 F hF (by simpa only [Nat.zero_add, pow_one, m] using hfx)
    exact (rename_injective Fin.succ (Fin.succ_injective n))
      (hzero.trans (map_zero _).symm)
  | succ d =>
    have hbmem : b ∈ m ^ d := by
      apply hstrict d b
      rw [hxb]
      exact (m ^ (d + 1)).sub_mem (homogeneous_eval_mem_pow hx hF)
        (Ideal.pow_le_pow_right (by omega) hz)
    obtain ⟨g, hg, hbg⟩ := homogeneous_representatives m x hres hgen hbmem
    have hdiff : F - X 0 * g = 0 := by
      apply hind (d + 1) _
      · exact hF.sub (by simpa only [Nat.add_comm 1] using (isHomogeneous_X k 0).mul hg)
      · have he : x 0 * (b - aeval x g) ∈ m ^ (d + 2) := by
          rw [show d + 2 = 1 + (d + 1) by omega, pow_add, pow_one]
          exact Ideal.mul_mem_mul (hx 0) hbg
        have hsum := (m ^ (d + 2)).add_mem hz he
        convert hsum using 1
        rw [map_sub, map_mul, aeval_X]
        rw [mul_sub, hxb]
        ring
    let φ : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin n) k :=
      aeval (Fin.cases 0 X)
    have hφF : φ F = f := by
      dsimp only [φ, F]
      rw [aeval_rename]
      change aeval X f = f
      exact aeval_X_left_apply f
    have hφX : φ (X 0) = 0 := by simp [φ]
    have h := congrArg φ hdiff
    simpa only [map_sub, map_mul, hφF, hφX, zero_mul, sub_zero, map_zero] using h

end IsLocalRing
