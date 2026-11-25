/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Localizations of a blow-up chart away from the exceptional divisor

Two criteria identifying localizations of an algebra `C` over `R` with localizations of `R`.

* If `R → C` is injective, `C` is a domain and every element of `C` lands in `R` after
  multiplication by a power of `x` (as for the chart `C = R[T]/(xT - y)` of a blow-up), then
  inverting `x v` on `C`, where `u = x ^ k v` with `u ∈ R`, is inverting `x u` on `R`
  (`BlowupChart.isLocalization_away_mul`).
* If `S` is an intermediate algebra `A ⊆ S ⊆ A[1/a]`, then `S[1/a] = A[1/a]`
  (`BlowupChart.isLocalization_away_of_subalgebra`).
-/

@[expose] public section

namespace BlowupChart

/-- Let `R → C` be injective with `C` a domain, `x ∈ R` nonzero in `C`, such that every element of
`C` lands in `R` after multiplication by a power of `x`. If `u ∈ R` equals `x ^ k v` in `C` with
`v ≠ 0`, then a localization of `C` away from `x v` is a localization of `R` away from `x u`. -/
theorem isLocalization_away_mul {R C L : Type*} [CommRing R] [CommRing C] [CommRing L]
    [Algebra R C] [Algebra C L] [Algebra R L] [IsScalarTower R C L] [IsDomain C]
    (hinj : Function.Injective (algebraMap R C)) {x : R} (hx : algebraMap R C x ≠ 0)
    (hC : ∀ c : C, ∃ (n : ℕ) (r : R), algebraMap R C x ^ n * c = algebraMap R C r)
    {v : C} (hv : v ≠ 0) {u : R} {k : ℕ} (hu : algebraMap R C u = algebraMap R C x ^ k * v)
    [IsLocalization.Away (algebraMap R C x * v) L] : IsLocalization.Away (x * u) L := by
  have hs := IsLocalization.Away.algebraMap_isUnit (S := L) (algebraMap R C x * v)
  rw [map_mul] at hs
  have hX := isUnit_of_mul_isUnit_left hs
  have hV := isUnit_of_mul_isUnit_right hs
  refine IsLocalization.Away.mk _ ?_ (fun z => ?_) (fun a b hab => ?_)
  · rw [IsScalarTower.algebraMap_apply R C L, map_mul, map_mul, hu, map_mul, map_pow]
    exact hX.mul ((hX.pow k).mul hV)
  · obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R C x * v) z
    obtain ⟨m, r, hr⟩ := hC c
    refine ⟨n + m, r * x ^ (k * n) * u ^ m, ?_⟩
    simp only [IsScalarTower.algebraMap_apply R C L, map_mul, map_pow, hu] at hc ⊢
    rw [← hr, map_mul, map_pow]
    linear_combination (algebraMap C L (algebraMap R C x) ^ m *
      algebraMap C L (algebraMap R C x) ^ (k * n) *
      (algebraMap C L (algebraMap R C x) ^ k * algebraMap C L v) ^ m) * hc
  · refine ⟨0, ?_⟩
    rw [pow_zero, one_mul, one_mul]
    apply hinj
    rw [IsScalarTower.algebraMap_apply R C L, IsScalarTower.algebraMap_apply R C L] at hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (algebraMap R C x * v) hab
    exact mul_left_cancel₀ (pow_ne_zero n (mul_ne_zero hx hv)) hn

/-- If `S` is an `A`-subalgebra of a localization `B = A[1/a]`, then a localization of `S` away from
`a` is a localization of `A` away from `a`. -/
theorem isLocalization_away_of_subalgebra {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (a : A) [IsLocalization.Away a B] (S : Subalgebra A B) (L : Type*) [CommRing L] [Algebra S L]
    [Algebra A L] [IsScalarTower A S L] [IsLocalization.Away (algebraMap A S a) L] :
    IsLocalization.Away a L := by
  refine IsLocalization.Away.mk _ ?_ (fun z => ?_) (fun b c hbc => ?_)
  · rw [IsScalarTower.algebraMap_apply A S L]
    exact IsLocalization.Away.algebraMap_isUnit _
  · obtain ⟨n, s, hs⟩ := IsLocalization.Away.surj (algebraMap A S a) z
    obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj a (s : B)
    have hb' : s * algebraMap A S a ^ m = algebraMap A S b := Subtype.ext (by simpa using hb)
    refine ⟨n + m, b, ?_⟩
    rw [IsScalarTower.algebraMap_apply A S L, IsScalarTower.algebraMap_apply A S L, ← hb',
      map_mul, ← hs, pow_add, map_pow]
    ring
  · rw [IsScalarTower.algebraMap_apply A S L, IsScalarTower.algebraMap_apply A S L] at hbc
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (algebraMap A S a) hbc
    have hn' : algebraMap A B (a ^ n * b) = algebraMap A B (a ^ n * c) := by
      simpa using congrArg Subtype.val hn
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq a hn'
    exact ⟨m + n, by rw [pow_add, mul_assoc, hm, mul_assoc]⟩

/-- Localization commutes with quotients: if `g : A → B` is surjective, then
`A[1/a] / (ker g) ≅ B[1/g(a)]`. -/
noncomputable def quotientAwayEquiv {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : Function.Surjective g) (a : A) :
    Localization.Away a ⧸ (RingHom.ker g).map (algebraMap A (Localization.Away a)) ≃+*
      Localization.Away (g a) :=
  (Ideal.quotEquivOfEq (IsLocalization.ker_map (Localization.Away (g a)) g
    (Submonoid.map_powers _ _)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := Localization.awayMap g a)
      (Localization.awayMap_surjective_iff.mpr fun b => by
        obtain ⟨c, rfl⟩ := hg b
        exact ⟨c, 0, by simp⟩))

end BlowupChart
