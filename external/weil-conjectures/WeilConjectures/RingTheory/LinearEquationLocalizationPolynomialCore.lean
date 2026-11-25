/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
@[expose] public section
universe u
namespace MvPolynomial
/-- Core existence and inverse-on-free-variables part of the localization computation.

The source is Stacks Project, Tag 07EU, `lemma-final-solve`, where the
calculation is omitted. Construct the forward map by the polynomial universal
property, sending each free variable to the corresponding class in the
localization. For the inverse, put
`z = fᵢ⁻¹ (1 - ∑ j ≠ i, fⱼ yⱼ)`, evaluate the original polynomial ring by
sending `xᵢ` to `z` and the other variables to `yⱼ`, and factor through the
linear relation because `fᵢ z + ∑ j ≠ i fⱼ yⱼ - 1 = 0`. The image of `fᵢ`
is a unit, so the localization universal property extends this map to `Bf`.
The inverse followed by the forward map fixes each free polynomial variable.
The forward followed by the inverse fixes the classes of the other variables,
and fixes `xᵢ` because the relation gives
`1 - ∑ j ≠ i, fⱼ xⱼ = fᵢ xᵢ`, so multiplying by `fᵢ⁻¹` recovers `xᵢ`.
Polynomial uniqueness, quotient surjectivity and localization uniqueness now
show both composites are identities. The inverse therefore sends every free
class to its variable, as claimed.
(blueprint: theorem-finite-etale-covers-proper-henselian--2) -/
theorem linearEquationLocalizationPolynomialCore (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A) (i : Fin r) :
    let I : Ideal (MvPolynomial (Fin r) A) :=
      Ideal.span {(∑ j : Fin r, C (f j) * X j) - 1}
    let B := MvPolynomial (Fin r) A ⧸ I
    let q := Ideal.Quotient.mk I
    let Af := Localization.Away (f i)
    let Bf := Localization.Away (algebraMap A B (f i))
    letI : Algebra Af Bf := (Localization.awayMap (algebraMap A B) (f i)).toAlgebra
    let x : Fin r → Bf := fun j ↦ algebraMap B Bf (q (X j))
    ∃ e : MvPolynomial {j : Fin r // j ≠ i} Af ≃ₐ[Af] Bf,
      e.toAlgHom = aeval (fun j ↦ x j.1) ∧
      (∀ j : {j : Fin r // j ≠ i}, e.symm (x j.1) = X j) := by
  classical
  dsimp only
  let I : Ideal (MvPolynomial (Fin r) A) :=
    Ideal.span {(∑ j : Fin r, C (f j) * X j) - 1}
  let B := MvPolynomial (Fin r) A ⧸ I
  let Af := Localization.Away (f i)
  let Bf := Localization.Away (algebraMap A B (f i))
  let : Algebra Af Bf := (Localization.awayMap (algebraMap A B) (f i)).toAlgebra
  let x : Fin r → Bf := fun j ↦ algebraMap B Bf (Ideal.Quotient.mk I (X j))
  let F := aeval (R := Af) (fun j : {j : Fin r // j ≠ i} ↦ x j.1)
  have hinj : Function.Injective F := by
    let I : Ideal (MvPolynomial (Fin r) A) :=
      Ideal.span {(∑ j : Fin r, C (f j) * X j) - 1}
    let B := MvPolynomial (Fin r) A ⧸ I
    let Af := Localization.Away (f i)
    let Bf := Localization.Away (algebraMap A B (f i))
    let : Algebra Af Bf := (Localization.awayMap (algebraMap A B) (f i)).toAlgebra
    let P := MvPolynomial {j : Fin r // j ≠ i} Af
    let coeff : A →+* P := C.comp (algebraMap A Af)
    let z : P := C (IsLocalization.Away.invSelf (S := Af) (f i)) *
      (1 - ∑ j : {j : Fin r // j ≠ i}, coeff (f j.1) * X j)
    let y : Fin r → P := fun j ↦ if h : j = i then z else X ⟨j, h⟩
    let g : MvPolynomial (Fin r) A →+* P := eval₂Hom coeff y
    have hgi : g (X i) = z := by simp [g, y]
    have hgj (j : {j : Fin r // j ≠ i}) : g (X j.1) = X j := by
      simp [g, y, j.property]
    have hgC (a : A) : g (C a) = coeff a := by simp [g]
    have hinv : coeff (f i) * C (IsLocalization.Away.invSelf (S := Af) (f i)) = 1 := by
      change C (algebraMap A Af (f i)) * C _ = _
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have hrel : g ((∑ j : Fin r, C (f j) * X j) - 1) = 0 := by
      rw [map_sub, map_sum, map_one,
        Fintype.sum_eq_add_sum_subtype_ne (fun j ↦ g (C (f j) * X j)) i]
      simp only [map_mul, hgC, hgi, hgj]
      change coeff (f i) * (C _ * (1 - ∑ j : {j : Fin r // j ≠ i},
        coeff (f j.1) * X j)) + (∑ j : {j : Fin r // j ≠ i},
        coeff (f j.1) * X j) - 1 = 0
      rw [← mul_assoc, hinv, one_mul]
      ring
    have hker : I ≤ RingHom.ker g := by
      apply Ideal.span_le.mpr
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      exact RingHom.mem_ker.mpr hrel
    let gb : B →+* P := Ideal.Quotient.lift I g (fun p hp ↦ RingHom.mem_ker.mp (hker hp))
    have hunit : IsUnit (gb (algebraMap A B (f i))) := by
      change IsUnit (g (C (f i)))
      rw [hgC]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Af) (f i)).map C
    let back : Bf →+* P := IsLocalization.Away.lift (algebraMap A B (f i)) hunit
    have hback (p : MvPolynomial (Fin r) A) :
        back (algebraMap B Bf (Ideal.Quotient.mk I p)) = g p := by
      change IsLocalization.Away.lift _ hunit (algebraMap B Bf _) = _
      rw [IsLocalization.Away.lift_eq]
      rfl
    have hcoeff (a : A) : algebraMap Af Bf (algebraMap A Af a) =
        algebraMap B Bf (Ideal.Quotient.mk I (C a)) := by
      change Localization.awayMap (algebraMap A B) (f i) (algebraMap A Af a) = _
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    have hbackC : back.comp (algebraMap Af Bf) = (C : Af →+* P) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (f i))
      apply RingHom.ext
      intro a
      change back (algebraMap Af Bf (algebraMap A Af a)) = C (algebraMap A Af a)
      rw [hcoeff, hback, hgC]
      rfl
    let F := aeval (R := Af) (fun j : {j : Fin r // j ≠ i} ↦
      algebraMap B Bf (Ideal.Quotient.mk I (X j.1)))
    have hleft : back.comp F.toRingHom = RingHom.id P := by
      apply MvPolynomial.ringHom_ext
      · intro a
        change back (F (C a)) = C a
        rw [aeval_C]
        exact RingHom.congr_fun hbackC a
      · intro j
        change back (F (X j)) = X j
        rw [aeval_X, hback, hgj]
    intro p q hpq
    have h := congrArg back hpq
    have hp := RingHom.congr_fun hleft p
    have hq := RingHom.congr_fun hleft q
    exact hp.symm.trans (h.trans hq)
  have hsurj : Function.Surjective F := by
    let I : Ideal (MvPolynomial (Fin r) A) :=
      Ideal.span {(∑ j : Fin r, C (f j) * X j) - 1}
    let B := MvPolynomial (Fin r) A ⧸ I
    let Af := Localization.Away (f i)
    let Bf := Localization.Away (algebraMap A B (f i))
    let : Algebra Af Bf := (Localization.awayMap (algebraMap A B) (f i)).toAlgebra
    let q := Ideal.Quotient.mk I
    let x : Fin r → Bf := fun j ↦ algebraMap B Bf (q (X j))
    let P := MvPolynomial {j : Fin r // j ≠ i} Af
    let F : P →ₐ[Af] Bf := aeval (fun j ↦ x j.1)
    have hcoeff (a : A) : algebraMap Af Bf (algebraMap A Af a) =
        algebraMap B Bf (q (C a)) := by
      change Localization.awayMap (algebraMap A B) (f i) (algebraMap A Af a) = _
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    let c : Bf := algebraMap Af Bf (algebraMap A Af (f i))
    let v : Af := IsLocalization.Away.invSelf (f i)
    have hv : c * algebraMap Af Bf v = 1 := by
      change algebraMap Af Bf (algebraMap A Af (f i)) *
        algebraMap Af Bf (IsLocalization.Away.invSelf (f i)) = 1
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have hrel : (∑ j : Fin r, algebraMap Af Bf (algebraMap A Af (f j)) * x j) = 1 := by
      have hq : q ((∑ j : Fin r, C (f j) * X j) - 1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
      have h := congrArg (algebraMap B Bf) hq
      simpa only [map_sub, map_sum, map_mul, map_one, map_zero, ← hcoeff,
        sub_eq_zero, x] using h
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun j ↦ algebraMap Af Bf (algebraMap A Af (f j)) * x j) i] at hrel
    let z : P := C v *
      (1 - ∑ j : {j : Fin r // j ≠ i}, C (algebraMap A Af (f j.1)) * X j)
    have hFC (a : Af) : F (C a) = algebraMap Af Bf a := aeval_C _ _
    have hFX (j : {j : Fin r // j ≠ i}) : F (X j) = x j.1 := aeval_X _ _
    have hz : F z = x i := by
      change F (C v * (1 - ∑ j : {j : Fin r // j ≠ i},
        C (algebraMap A Af (f j.1)) * X j)) = x i
      simp only [map_mul, map_sub, map_one, map_sum, hFC, hFX]
      rw [← eq_sub_of_add_eq hrel]
      change algebraMap Af Bf v * (c * x i) = x i
      rw [← mul_assoc, mul_comm (algebraMap Af Bf v), hv, one_mul]
    have hx (j : Fin r) : ∃ p : P, F p = x j := by
      by_cases h : j = i
      · subst j
        exact ⟨z, hz⟩
      · exact ⟨X ⟨j, h⟩, aeval_X _ _⟩
    have hpoly (p : MvPolynomial (Fin r) A) :
        ∃ p' : P, F p' = algebraMap B Bf (q p) := by
      induction p using MvPolynomial.induction_on with
      | C a =>
        refine ⟨C (algebraMap A Af a), ?_⟩
        rw [aeval_C, hcoeff]
      | add p t hp ht =>
        obtain ⟨p', hp'⟩ := hp
        obtain ⟨t', ht'⟩ := ht
        refine ⟨p' + t', ?_⟩
        simp only [map_add, hp', ht']
      | mul_X p j hp =>
        obtain ⟨p', hp'⟩ := hp
        obtain ⟨j', hj'⟩ := hx j
        refine ⟨p' * j', ?_⟩
        simp only [map_mul, hp', hj', x]
    intro t
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (algebraMap A B (f i)) t
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨p', hp'⟩ := hpoly p
    have hc : algebraMap B Bf (algebraMap A B (f i)) = c := (hcoeff (f i)).symm
    rw [hc] at hb
    refine ⟨p' * C (v ^ n), ?_⟩
    change F (p' * C (v ^ n)) = t
    rw [map_mul, aeval_C, map_pow, hp', ← hb, mul_assoc, ← mul_pow, hv, one_pow, mul_one]
  have hF : Function.Bijective F := ⟨hinj, hsurj⟩
  let e := AlgEquiv.ofBijective F hF
  refine ⟨e, rfl, ?_⟩
  intro j
  have hX : e (X j) = x j.1 := by
    change F (X j) = x j.1
    exact aeval_X _ _
  change e.symm (x j.1) = X j
  rw [← hX]
  exact e.symm_apply_apply (X j)
end MvPolynomial
