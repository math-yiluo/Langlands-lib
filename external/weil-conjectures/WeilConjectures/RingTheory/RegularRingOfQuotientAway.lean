/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Regular.SMul
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Regularity from a principal quotient and a principal localization

* `IsRegularLocalRing.of_isRegularLocalRing_quotient`: a noetherian local ring `R` with a
  non-zero-divisor `x` in its maximal ideal such that `R ⧸ (x)` is regular local is regular local
  (Stacks Project, Tag 00NU).
* `IsRegularRing.of_quotient_of_away`: a noetherian ring `A` with a non-zero-divisor `a` such that
  `A ⧸ (a)` and `A[1/a]` are regular rings is a regular ring.
-/

@[expose] public section

universe u v

open IsLocalRing

/-- **Lifting regularity across a non-zero-divisor** (Stacks Project, Tag 00NU): if `x` is a
non-zero-divisor in the maximal ideal of a noetherian local ring `R` and `R ⧸ (x)` is a regular
local ring, then `R` is a regular local ring. -/
theorem IsRegularLocalRing.of_isRegularLocalRing_quotient
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular R x)
    [IsRegularLocalRing (R ⧸ Ideal.span {x})] : IsRegularLocalRing R := by
  classical
  let I := Ideal.span ({x} : Set R)
  let Q := R ⧸ I
  let φ := Ideal.Quotient.mk I
  let m := maximalIdeal R
  let mq := maximalIdeal Q
  obtain ⟨s, hcard, hs⟩ := (IsNoetherian.noetherian mq).exists_span_finset_card_eq_spanFinrank
  let a : Q → R := Function.surjInv Ideal.Quotient.mk_surjective
  have ha (y : Q) : φ (a y) = y := Function.surjInv_eq _ y
  let t : Set R := insert x (a '' (s : Set Q))
  have hfin : t.Finite := (s.finite_toSet.image a).insert x
  have ht : Ideal.span t = m := by
    have hmap : (Ideal.span t).map φ = mq := by
      rw [Ideal.map_span, Set.image_insert_eq]
      have hx0 : φ x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
      rw [hx0, Set.image_image]
      simp only [ha, Set.image_id']
      rw [Ideal.span_insert_zero]
      exact hs
    have hI : I ≤ Ideal.span t := Ideal.span_mono (by
      intro y hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact Set.mem_insert _ _)
    have hc : (Ideal.span t).comap (RingHom.id R) = m := by
      rw [Ideal.comap_id]
      have hh := congrArg (Ideal.comap φ) hmap
      rw [Ideal.comap_map_of_surjective φ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI] at hh
      have hm : mq.comap φ = m := by
        rw [show mq = m.map φ from (map_maximalIdeal_of_surjective φ
          Ideal.Quotient.mk_surjective).symm]
        rw [Ideal.comap_map_of_surjective φ Ideal.Quotient.mk_surjective,
          ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
          sup_eq_left.mpr (Ideal.span_le.mpr (by rintro y rfl; exact hx))]
      exact hh.trans hm
    simpa using hc
  have hbound : m.spanFinrank ≤ mq.spanFinrank + 1 := by
    rw [← ht]
    calc
      _ ≤ t.ncard := Submodule.spanFinrank_span_le_ncard_of_finite hfin
      _ ≤ (a '' (s : Set Q)).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ (s : Set Q).ncard + 1 := Nat.add_le_add_right (Set.ncard_image_le s.finite_toSet) 1
      _ = mq.spanFinrank + 1 := by rw [Set.ncard_coe_finset, hcard]
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    hreg (by simpa [ringJacobson_eq_maximalIdeal] using hx)
  rw [← hdim, ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := Q)]
  exact_mod_cast hbound

/-- If `a` is a non-zero-divisor of a noetherian ring `A` such that both `A ⧸ (a)` and the
localization `A[1/a]` are regular rings, then `A` is a regular ring: at a prime containing `a`
apply `IsRegularLocalRing.of_isRegularLocalRing_quotient` to `A_P`, whose quotient by `a` is a
localization of `A ⧸ (a)`; at a prime not containing `a`, `A_P` is a localization of `A[1/a]`. -/
theorem IsRegularRing.of_quotient_of_away {A : Type u} [CommRing A] [IsNoetherianRing A]
    {a : A} (ha : a ∈ nonZeroDivisors A) [IsRegularRing (A ⧸ Ideal.span {a})]
    (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.Away a S] [IsRegularRing S] :
    IsRegularRing A := by
  rw [isRegularRing_iff]
  intro P hP
  by_cases haP : a ∈ P
  · let L := Localization.AtPrime P
    let I := Ideal.span ({a} : Set A)
    have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr haP
    let q : Ideal (A ⧸ I) := P.map (Ideal.Quotient.mk I)
    have hq : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
    have hqP : q.comap (Ideal.Quotient.mk I) = P := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hIP]
    have hcompl : Algebra.algebraMapSubmonoid (A ⧸ I) P.primeCompl = q.primeCompl := by
      have h := Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective q
      simp only [hqP] at h
      exact h
    have : IsLocalization q.primeCompl (L ⧸ I.map (algebraMap A L)) := by
      rw [← hcompl]
      infer_instance
    have hmap : I.map (algebraMap A L) = Ideal.span {algebraMap A L a} := by
      rw [Ideal.map_span, Set.image_singleton]
    have : IsRegularLocalRing (L ⧸ Ideal.span {algebraMap A L a}) := by
      rw [← hmap]
      exact IsRegularLocalRing.of_ringEquiv
        (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
          (L ⧸ I.map (algebraMap A L))).toRingEquiv
    refine IsRegularLocalRing.of_isRegularLocalRing_quotient L (algebraMap A L a)
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff L P a).mpr haP) ?_
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors
      (IsLocalization.map_nonZeroDivisors_le P.primeCompl L ⟨a, ha, rfl⟩)
  · have hdisj : Disjoint (Submonoid.powers a : Set A) P :=
      (Ideal.disjoint_powers_iff_notMem a hP.isRadical).mpr haP
    let Q : Ideal S := P.map (algebraMap A S)
    have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) S P hP
      hdisj
    have hQP : Q.comap (algebraMap A S) = P :=
      IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) S hP hdisj
    have : IsLocalization P.primeCompl (Localization.AtPrime Q) := by
      simpa only [hQP] using
        IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers a)
          (Localization.AtPrime Q) Q
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime Q)
        (Localization.AtPrime P)).toRingEquiv
