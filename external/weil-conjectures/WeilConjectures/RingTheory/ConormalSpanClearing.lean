/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! # Clearing a finite ideal from localized conormal spanning

Source: Stacks Project, Tag 07CP, preparation (2)--(4), and Tag 00DV.
(blueprint: lem-weil-pbc-conormal-span-clearing).
-/

@[expose] public section

universe u

namespace Ideal

/-- Localized conormal spanning gives exact equations after multiplying by an element
whose quotient image is a positive power of the original chart element.

Source: Stacks Project, Tag 07CP, preparation (2)--(4); Tag 00DV for Nakayama.
(blueprint: lem-weil-pbc-conormal-span-clearing).

Proof: Put J = (f_j, j in E), I = (f_j), and q:A -> A/I. Lift linear
combinations of selected conormal classes to J. Localized spanning and the
localization equality criterion give x^k_l*f_l in J+I^2 for every l.
In T=A_x these imply I_T <= J_T+I_T^2. The ideal I_T is finitely generated,
so Nakayama applied to I_T/J_T gives e with e-1 in I_T and e*I_T contained
in J_T. The localization ideal membership criterion writes
(e-1)*x^N=b in T with b in I. Consequently (x^N+b)*f_l belongs to J_T.
Clear this membership to get x^k_l*(x^N+b)*f_l in J. Set K to one plus
the maximum of these finitely many exponents (the empty maximum is zero).
For a=x^K*(x^N+b), every a*f_l belongs to J, and q(a)=q(x)^(K+N).
The exponent K+N is positive. Express each membership as a sum over E,
and extend its coefficients by zero outside E. Empty generator families,
empty E, and zero rings require no additional assumptions; all finiteness
comes from the finite family generating I. -/
theorem exists_conormal_span_clearing
    {A : Type u} [CommRing A] (m : ℕ) (f : Fin m → A)
    (x : A) (E : Finset (Fin m)) :
    let I := Ideal.span (Set.range f)
    let q := Ideal.Quotient.mk I
    Submodule.span (Localization.Away (q x))
      (Set.range (fun j : E ↦ LocalizedModule.mkLinearMap (Submonoid.powers (q x))
        I.Cotangent (I.toCotangent ⟨f j, Ideal.subset_span ⟨j, rfl⟩⟩))) = ⊤ →
    ∃ (a : A) (h : Fin m → Fin m → A) (s : ℕ),
      0 < s ∧ q a = q x ^ s ∧
      ∀ l : Fin m, a * f l = ∑ j ∈ E, h l j * f j  := by
  classical
  dsimp only
  intro hspan
  let I := Ideal.span (Set.range f)
  let q := Ideal.Quotient.mk I
  let Q := A ⧸ I
  let S := Localization.Away (q x)
  let F := LocalizedModule.mkLinearMap (Submonoid.powers (q x)) I.Cotangent
  let v : E → I := fun j ↦ ⟨f j, Ideal.subset_span ⟨j, rfl⟩⟩
  let t : E → I.Cotangent := fun j ↦ I.toCotangent (v j)
  let N : Submodule Q I.Cotangent := Submodule.span Q (Set.range t)
  let J : Ideal A := Ideal.span (Set.range (fun j : E ↦ f j))
  have hJ : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨j, rfl⟩
  have hvJ (j : E) : (v j : A) ∈ J := Ideal.subset_span ⟨j, rfl⟩
  have hrep (z : I.Cotangent) (hz : z ∈ N) :
      ∃ g : I, (g : A) ∈ J ∧ I.toCotangent g = z := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact ⟨v j, hvJ j, rfl⟩
    | zero => exact ⟨0, J.zero_mem, map_zero _⟩
    | add z w hz hw ihz ihw =>
      obtain ⟨g, hg, rfl⟩ := ihz
      obtain ⟨h, hh, rfl⟩ := ihw
      exact ⟨g + h, J.add_mem hg hh, map_add _ _ _⟩
    | smul r z hz ih =>
      obtain ⟨g, hg, rfl⟩ := ih
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      refine ⟨a • g, J.mul_mem_left a hg, ?_⟩
      rw [map_smul]
      exact (algebraMap_smul Q a _).symm
  let N' := N.localized' S (Submonoid.powers (q x)) F
  have hN' : N' = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨t j, Submodule.subset_span ⟨j, rfl⟩, 1, IsLocalizedModule.mk'_one _ _ _⟩
  have hmem (l : Fin m) : ∃ k : ℕ, x ^ k * f l ∈ J ⊔ I ^ 2 := by
    let z : I := ⟨f l, Ideal.subset_span ⟨l, rfl⟩⟩
    have hz : F (I.toCotangent z) ∈ N' := by rw [hN']; trivial
    obtain ⟨w, hw, s, hs⟩ := hz
    have heq : F ((s : Q) • I.toCotangent z) = F w := by
      rw [map_smul, ← hs]
      exact IsLocalizedModule.mk'_cancel' F w s
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (q x)) F).mp heq
    have hw' : (s' : Q) • (s : Q) • I.toCotangent z ∈ N :=
      hs' ▸ N.smul_mem (s' : Q) hw
    obtain ⟨g, hg, hgz⟩ := hrep _ hw'
    obtain ⟨k, hk⟩ := s.property
    obtain ⟨k', hk'⟩ := s'.property
    change (q x) ^ k = (s : Q) at hk
    change (q x) ^ k' = (s' : Q) at hk'
    have hpow : I.toCotangent (x ^ (k' + k) • z) =
        (s' : Q) • (s : Q) • I.toCotangent z := by
      rw [map_smul, ← algebraMap_smul Q, map_pow, pow_add, mul_smul]
      change (q x) ^ k' • (q x) ^ k • I.toCotangent z = _
      rw [hk, hk']
    have hdiff : x ^ (k' + k) * f l - (g : A) ∈ I ^ 2 :=
      I.toCotangent_eq.mp (hpow.trans hgz.symm)
    refine ⟨k' + k, ?_⟩
    have := (J ⊔ I ^ 2).add_mem ((show J ≤ J ⊔ I ^ 2 from le_sup_left) hg)
      ((show I ^ 2 ≤ J ⊔ I ^ 2 from le_sup_right) hdiff)
    convert this using 1; abel
  let T := Localization.Away x
  let r := algebraMap A T
  let It := I.map r
  let Jt := J.map r
  have hItfg : It.FG := by
    rw [show It = Ideal.span (r '' Set.range f) from Ideal.map_span r (Set.range f)]
    exact Submodule.fg_span ((Set.finite_range f).image r)
  have hIt : It ≤ Jt ⊔ It ^ 2 := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨l, rfl⟩
    obtain ⟨k, hk⟩ := hmem l
    have hmap := Ideal.mem_map_of_mem r hk
    rw [Ideal.map_sup, Ideal.map_pow, map_mul, map_pow] at hmap
    exact (Ideal.unit_mul_mem_iff_mem _
      ((IsLocalization.Away.algebraMap_isUnit (S := T) x).pow k)).mp hmap
  have hIt' : It ≤ Jt ⊔ It • It := by simpa only [pow_two, Ideal.smul_eq_mul] using hIt
  obtain ⟨e, he, hek⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hItfg le_rfl hIt'
  obtain ⟨⟨b, den⟩, hden⟩ := (IsLocalization.mem_map_algebraMap_iff
    (Submonoid.powers x) T).mp he
  obtain ⟨N, hN⟩ := den.property
  change x ^ N = (den : A) at hN
  have heq : e * r (x ^ N) = r (x ^ N + (b : A)) := by
    have h := hden
    rw [← hN, sub_mul, one_mul] at h
    rw [map_add]
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hJt (l : Fin m) : r ((x ^ N + (b : A)) * f l) ∈ Jt := by
    have hfl : r (f l) ∈ It := Ideal.mem_map_of_mem r (Ideal.subset_span ⟨l, rfl⟩)
    have h := hek (Submodule.smul_mem_pointwise_smul (r (f l)) e It hfl)
    change e * r (f l) ∈ Jt at h
    have h' := Jt.mul_mem_left (r (x ^ N)) h
    rw [map_mul, ← heq]
    simpa only [mul_assoc, mul_left_comm e] using h'
  have hclear (l : Fin m) : ∃ k : ℕ, x ^ k * ((x ^ N + (b : A)) * f l) ∈ J := by
    obtain ⟨d, hd, h⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers x) T J _).mp (hJt l)
    obtain ⟨k, rfl⟩ := hd
    exact ⟨k, h⟩
  choose k hk using hclear
  let K := (Finset.univ.sup k) + 1
  have hK (l : Fin m) : k l ≤ K :=
    (Finset.le_sup (Finset.mem_univ l)).trans (Nat.le_add_right _ _)
  let a := x ^ K * (x ^ N + (b : A))
  have haJ (l : Fin m) : a * f l ∈ J := by
    have h := J.mul_mem_left (x ^ (K - k l)) (hk l)
    simpa only [a, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hK l)] using h
  have hcoeff (l : Fin m) : ∃ c : E → A, ∑ j, c j * f j = a * f l :=
    Ideal.mem_span_range_iff_exists_fun.mp (haJ l)
  choose c hc using hcoeff
  let h : Fin m → Fin m → A := fun l j ↦ if hj : j ∈ E then c l ⟨j, hj⟩ else 0
  refine ⟨a, h, K + N, ?_, ?_, fun l ↦ ?_⟩
  · dsimp [K]
    omega
  · have hb : q (b : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr b.property
    change q a = q x ^ (K + N)
    simp only [a, map_mul, map_add, map_pow, hb, add_zero, ← pow_add]
  · rw [← hc l]
    rw [← Finset.sum_attach E (fun j ↦ h l j * f j)]
    apply Finset.sum_congr (by ext; simp)
    intro j hj
    simp only [h, dite_eq_left j.property]

end Ideal
