/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Local charts of the finite algebra quotient

Source: Stacks Project, Tags 07N9, 00E3 and 00CT.
(blueprint: lem-weil-pbc-localized-finite-quotient-charts)
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- The local factors of a positive finite-algebra quotient are its localizations.
Source: Stacks Project, Tag 07N9, prime correspondence in the proof;
Tags 00E3 (localization prime correspondence) and 00CT (quotients and localization).
(blueprint: lem-weil-pbc-localized-finite-quotient-charts)

Proof: The tensor algebra B is the localization of S at the image of R minus p.
Extension and contraction identify primes of B containing J with primes of S
whose contraction is p. Indeed their contraction contains p, and disjointness
from R minus p gives the reverse inclusion. A prime contains J^n exactly when
it contains J, since n is positive. The quotient correspondence therefore gives
an equivalence between Q and the primes of B/J^n. These primes are maximal:
B is finite over R_p, and the quotient is integral over the quotient of R_p
by its maximal-ideal power, which has only its maximal ideal as a prime.
The equivalence sends q to the quotient of its extension to B; its displayed
contraction formula determines it uniquely. Localizing B at that extension is
S_q: both invert precisely the elements outside q, by localization in stages.
The S-algebra property determines psi on S, and on inverses of the denominators,
so psi is this canonical localization map. Localization commutes with quotient,
and map preserves powers, giving the stated localization structure on S_q/K_q^n.
If Q is empty, B/J^n is the zero ring and both indexing types are empty. -/
theorem localized_finite_quotient_charts
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    ∀ (ψ : ∀ q : Q, B →ₐ[S] Localization.AtPrime q.1) (n : ℕ), n ≠ 0 →
      let K := fun q : Q ↦ J.map (ψ q).toRingHom
      ∃ e : Q ≃ MaximalSpectrum (B ⧸ J ^ n),
        (∀ q : Q, (e q).asIdeal.comap
          ((Ideal.Quotient.mk (J ^ n)).comp (algebraMap S B)) = q.1) ∧
        ∀ q : Q,
          let f : (B ⧸ J ^ n) →+* (Localization.AtPrime q.1 ⧸ (K q) ^ n) :=
            Ideal.quotientMap ((K q) ^ n) (ψ q).toRingHom (by
            rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])
          letI := f.toAlgebra
          IsLocalization.AtPrime (Localization.AtPrime q.1 ⧸ (K q) ^ n) (e q).asIdeal := by
  classical
  dsimp only
  let A := Localization.AtPrime p
  let B := A ⊗[R] S
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
  let J := p.map (algebraMap R B)
  let Q := p.primesOver S
  let M := Algebra.algebraMapSubmonoid S p.primeCompl
  have : IsLocalization M B := inferInstance
  intro ψ n hn
  let π := Ideal.Quotient.mk (J ^ n)
  have hJ (P : Ideal B) [P.IsPrime] (hP : J ≤ P) : P.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) P
    change (P.comap (algebraMap A B)).IsMaximal
    have hm : IsLocalRing.maximalIdeal A ≤ P.comap (algebraMap A B) := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A,
        Ideal.map_le_iff_le_comap, Ideal.comap_comap,
        ← IsScalarTower.algebraMap_eq]
      exact Ideal.map_le_iff_le_comap.mp hP
    have he := (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le
      (Ideal.IsPrime.ne_top (inferInstance : (P.comap (algebraMap A B)).IsPrime)) hm
    rw [← he]
    infer_instance
  have hd (q : Q) : Disjoint (M : Set S) (q.1 : Set S) := by
    exact Ideal.disjoint_primeCompl_of_liesOver q.1 p
  have hqprime (q : Q) : (q.1.map (algebraMap S B)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M B q.1 inferInstance (hd q)
  have hqcomap (q : Q) : (q.1.map (algebraMap S B)).comap (algebraMap S B) = q.1 :=
    IsLocalization.under_map_of_isPrime_disjoint M B inferInstance (hd q)
  have hqJ (q : Q) : J ≤ q.1.map (algebraMap S B) := by
    dsimp [J]
    rw [IsScalarTower.algebraMap_eq R S B, ← Ideal.map_map]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr (Ideal.over_def q.1 p).le)
  have hqmax (q : Q) : (q.1.map (algebraMap S B)).IsMaximal := by
    have := hqprime q
    exact hJ _ (hqJ q)
  have hqn (q : Q) : J ^ n ≤ q.1.map (algebraMap S B) :=
    (Ideal.pow_le_self hn).trans (hqJ q)
  let e₀ : Q → MaximalSpectrum (B ⧸ J ^ n) := fun q ↦
    ⟨(q.1.map (algebraMap S B)).map π, by
      have := hqmax q
      apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      simpa [π] using hqn q⟩
  have he₀ (q : Q) : (e₀ q).asIdeal.comap π = q.1.map (algebraMap S B) := by
    exact Ideal.comap_map_mk (hqn q)
  have hcon (q : Q) :
      (e₀ q).asIdeal.comap (π.comp (algebraMap S B)) = q.1 := by
    rw [← Ideal.comap_comap, he₀, hqcomap]
  have hinj : Function.Injective e₀ := by
    intro q r h
    apply Subtype.ext
    rw [← hcon q, ← hcon r, h]
  have hsurj : Function.Surjective e₀ := by
    intro m
    let P := m.asIdeal.comap π
    have : P.IsPrime := inferInstance
    have hpow : J ^ n ≤ P := by
      intro x hx
      change π x ∈ m.asIdeal
      simp [π, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    have hJP : J ≤ P := Ideal.IsPrime.le_of_pow_le hpow
    let q := P.comap (algebraMap S B)
    have : q.IsPrime := inferInstance
    have hqp : q.LiesOver p := by
      constructor
      apply le_antisymm
      · change p ≤ (P.comap (algebraMap S B)).comap (algebraMap R S)
        rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
        exact Ideal.map_le_iff_le_comap.mp hJP
      · intro x hx
        by_contra hxp
        have hu : IsUnit (algebraMap R B x) := by
          rw [IsScalarTower.algebraMap_apply R S B]
          exact IsLocalization.map_units (M := M) B
            ⟨algebraMap R S x, ⟨x, hxp, rfl⟩⟩
        exact (inferInstance : P.IsPrime).ne_top (P.eq_top_of_isUnit_mem hx
          (by simpa only [IsScalarTower.algebraMap_apply R S B] using hu))
    let q' : Q := ⟨q, inferInstance, inferInstance⟩
    refine ⟨q', ?_⟩
    apply MaximalSpectrum.ext
    change (q.map (algebraMap S B)).map π = m.asIdeal
    rw [IsLocalization.map_under M B P]
    exact Ideal.map_comap_of_surjective π Ideal.Quotient.mk_surjective m.asIdeal
  let e : Q ≃ MaximalSpectrum (B ⧸ J ^ n) := Equiv.ofBijective e₀ ⟨hinj, hsurj⟩
  refine ⟨e, hcon, ?_⟩
  intro q
  let T := Localization.AtPrime q.1
  let P := q.1.map (algebraMap S B)
  let K := J.map (ψ q).toRingHom
  let f : (B ⧸ J ^ n) →+* (T ⧸ K ^ n) :=
    Ideal.quotientMap (K ^ n) (ψ q).toRingHom (by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])
  change letI := f.toAlgebra; IsLocalization.AtPrime (T ⧸ K ^ n) (e q).asIdeal
  let := (ψ q).toAlgebra
  have : IsScalarTower S B T := IsScalarTower.of_algebraMap_eq fun x ↦
    ((ψ q).commutes x).symm
  have hle : M ≤ q.1.primeCompl := by
    intro x hx
    exact Set.disjoint_left.mp (hd q) hx
  have : IsLocalization (q.1.primeCompl.map (algebraMap S B)) T :=
    IsLocalization.isLocalization_of_submonoid_le B T M q.1.primeCompl hle
  have hPT : (IsLocalRing.maximalIdeal T).comap (algebraMap B T) = P := by
    apply (IsLocalization.orderEmbedding M B).injective
    change ((IsLocalRing.maximalIdeal T).comap (algebraMap B T)).comap
      (algebraMap S B) = P.comap (algebraMap S B)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact (IsLocalization.AtPrime.under_maximalIdeal T q.1).trans (hqcomap q).symm
  have : IsLocalization P.primeCompl T := by
    apply IsLocalization.of_le (q.1.primeCompl.map (algebraMap S B)) P.primeCompl
    · rintro x ⟨s, hs, rfl⟩
      change algebraMap S B s ∉ P
      change s ∉ q.1 at hs
      change algebraMap S B s ∉ q.1.map (algebraMap S B)
      simpa only [← Ideal.mem_comap, hqcomap] using hs
    · intro x hx
      change x ∉ P at hx
      rw [← hPT] at hx
      exact (IsLocalRing.mem_maximalIdeal _).not.mp hx |> not_not.mp
  let := f.toAlgebra
  have hquot : IsLocalization (P.primeCompl.map π) (T ⧸ K ^ n) := by
    apply IsLocalization.of_surjective P.primeCompl T π Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (K ^ n)) Ideal.Quotient.mk_surjective
    · apply RingHom.ext
      intro x
      change Ideal.Quotient.mk (K ^ n) ((ψ q) x) = f (π x)
      rfl
    · rw [Ideal.mk_ker, Ideal.mk_ker, Ideal.map_pow]
      exact le_rfl
  have hcompl : P.primeCompl.map π = (e q).asIdeal.primeCompl := by
    have hPe : (e q).asIdeal.comap π = P := he₀ q
    simpa only [hPe] using
      Ideal.map_primeCompl_comap_of_surjective π Ideal.Quotient.mk_surjective (e q).asIdeal
  rw [hcompl] at hquot
  exact hquot

end AdicCompletion
