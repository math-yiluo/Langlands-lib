/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuDelocalizeWeak
import WeilConjectures.RingTheory.PopescuHeightZeroAuxiliaryWitnesses
import Mathlib.RingTheory.KrullDimension.Zero

@[expose] public section

universe u v t

namespace Algebra

/-- The construction in Stacks Project, Lemma 07FA, produces a finite presentation
factorization whose extended singular ideal contains the original one and escapes `q`.
The detailed construction uses the weak delocalization lemma, nilpotence in the
zero-dimensional localization, and the auxiliary polynomial algebra localizations.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07FA.
(blueprint: lem-weil-pbc-popescu-delocalize-height-zero-data)
-/
theorem exists_popescu_resolution_data_of_local_height_zero
    {R : Type u} {A : Type v} {Λ : Type t}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
    (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)
    (hlocal :
      letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
      CanBePopescuResolved
        (Algebra.TensorProduct.lift
          (Algebra.ofId (Localization.AtPrime (q.asIdeal.under R))
            (Localization.AtPrime q.asIdeal))
          ((IsScalarTower.toAlgHom R Λ (Localization.AtPrime q.asIdeal)).comp α)
          (fun _ _ => Commute.all _ _))
        ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal), inferInstance⟩)
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      ∃ (β : A →ₐ[R] B) (γ : B →ₐ[R] Λ),
        FinitePresentation R B ∧ γ.comp β = α ∧
          popescuIdeal α ≤ popescuIdeal γ ∧ ¬ popescuIdeal γ ≤ q.asIdeal := by
  classical
  let : IsNoetherianRing A := FiniteType.isNoetherianRing R A
  let : Ring.KrullDimLE 0 (Localization.AtPrime q.asIdeal) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  obtain ⟨s, hs⟩ := (singularIdeal R A).fg_of_isNoetherianRing
  have hs_mem : ∀ a ∈ s, a ∈ singularIdeal R A := by
    intro a ha
    rw [← hs]
    exact Ideal.subset_span ha
  have hnil : ∀ a : s, ∃ n : ℕ, ∃ ell : Λ,
      ell ∉ q.asIdeal ∧ ell * α a.val ^ n = 0 := by
    intro a
    have haq : α a.val ∈ q.asIdeal :=
      hminimal.le (Ideal.le_radical
        (Ideal.mem_map_of_mem α.toRingHom (hs_mem a.val a.property)))
    have hn : IsNilpotent (algebraMap Λ (Localization.AtPrime q.asIdeal) (α a.val)) :=
      Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff
          (Localization.AtPrime q.asIdeal) q.asIdeal (α a.val)).mpr haq)
    obtain ⟨n, hn⟩ := hn
    have hz : algebraMap Λ (Localization.AtPrime q.asIdeal) (α a.val ^ n) = 0 := by
      simpa only [map_pow] using hn
    obtain ⟨ell, hell⟩ := (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) _).mp hz
    exact ⟨n, ell.val, ell.property, hell⟩
  choose n ell hell hkill using hnil
  obtain ⟨C, _instC, _algC, β, γ, hfpC, hcompC, hnotC⟩ :=
    exists_factorization_singularIdeal_not_le_of_local_popescu_resolution
      α q hminimal hlocal
  let := hfpC
  have hc : ∃ c ∈ singularIdeal R C, γ c ∉ q.asIdeal := by
    by_contra h
    apply hnotC
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    exact not_not.mp (fun hn ↦ h ⟨c, hc, hn⟩)
  obtain ⟨c, hc, hcq⟩ := hc
  obtain ⟨B, _instB, _algB, β', δ, hfpB, hcompB, hb, hd⟩ :=
    exists_popescu_height_zero_auxiliary_witnesses α β γ hcompC s hs_mem n ell hkill c hc
  refine ⟨B, inferInstance, inferInstance, β', δ, hfpB, hcompB, ?_, ?_⟩
  · unfold popescuIdeal
    rw [Ideal.radical_le_radical_iff, Ideal.map_le_iff_le_comap, ← hs, Ideal.span_le]
    intro a ha
    obtain ⟨d, hd, heq⟩ := hd ⟨a, ha⟩
    exact ⟨n ⟨a, ha⟩ + 1, heq ▸ Ideal.mem_map_of_mem δ.toRingHom hd⟩
  · obtain ⟨b, hb, heq⟩ := hb
    intro hle
    have hmem := hle (Ideal.le_radical (Ideal.mem_map_of_mem δ.toRingHom hb))
    change δ b ∈ q.asIdeal at hmem
    rw [heq] at hmem
    rcases q.isPrime.mem_or_mem hmem with hprod | hc'
    · obtain ⟨a, _, ha⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
      exact hell a ha
    · exact hcq hc'

end Algebra
