/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.QuotientAssociatedPrimesFlatBaseChange
import WeilConjectures.RingTheory.CodimensionOneAnalyticallyUnramified
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# A principal-quotient criterion for an analytically unramified local domain

Source: Stacks Project, Algebra, Lemma Tag 0330
(blueprint: lem-weil-pbc-analytic-unramified-principal-criterion).
-/

@[expose] public section

universe u

private theorem reduced_of_principal_associated_localizations
    (C : Type u) [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    (x : C) (hxm : x ∈ IsLocalRing.maximalIdeal C)
    (hx : Function.Injective (fun y : C => x * y))
    (hdom : ∀ q : associatedPrimes C (C ⧸ Ideal.span {x}),
      IsDomain (Localization.AtPrime q.1)) : IsReduced C := by
  have divide (y : C) (hy : y ^ 2 = 0) :
      ∃ z : C, y = x * z ∧ z ^ 2 = 0 := by
    have hyq : Ideal.Quotient.mk (Ideal.span {x}) y = 0 := by
      apply (Module.injective_pi_localization_associatedPrimes
        C (C ⧸ Ideal.span {x})).2
      intro q
      have : IsDomain (Localization.AtPrime q.1) := hdom q
      have hloc : algebraMap C (Localization.AtPrime q.1) y = 0 := by
        apply IsNilpotent.eq_zero
        exact ⟨2, by rw [← map_pow, hy, map_zero]⟩
      obtain ⟨s, hs⟩ :=
        (IsLocalization.map_eq_zero_iff q.1.primeCompl (Localization.AtPrime q.1) y).mp hloc
      refine ⟨s, s.2, ?_⟩
      change Ideal.Quotient.mk (Ideal.span {x}) ((s : C) * y) = 0
      rw [hs, map_zero]
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hyq)
    refine ⟨z, hz, ?_⟩
    apply hx
    apply hx
    calc
      x * (x * z ^ 2) = y ^ 2 := by rw [hz]; ring
      _ = 0 := hy
      _ = x * (x * 0) := by simp
  have hpowers : ∀ n : ℕ, ∀ y : C, y ^ 2 = 0 → y ∈ Ideal.span {x} ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro y hy
      obtain ⟨z, rfl, hz⟩ := divide y hy
      rw [pow_succ']
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (ih z hz)
  apply (isReduced_iff_pow_one_lt 2 (by decide)).2
  intro y hy
  have hproper : Ideal.span {x} ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal C).ne_top
      (Ideal.span_le.mpr (by simpa using hxm))
  have hm : y ∈ (⨅ n : ℕ, Ideal.span {x} ^ n) := by
    exact Ideal.mem_iInf.mpr (fun n => hpowers n y hy)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing (I := Ideal.span {x}) hproper] at hm
  exact hm

/-- (blueprint: lem-weil-pbc-analytic-unramified-principal-criterion)
Stacks Project, Algebra, Lemma Tag 0330: a Noetherian local domain is analytically unramified
if a nonzero element of its maximal ideal has a quotient without embedded associated primes,
and the localizations at these primes are regular and the prime quotients analytically unramified.

Proof from the node's eight steps:
1. The maximal-ideal-adic completion is Noetherian, local and flat over `A`
   (`lem-weil-pbc-adic-completion-noetherian`, `lem-weil-pbc-local-completion-local-ring`,
   `lem-weil-pbc-noetherian-completion-flat`). Flatness preserves injectivity of multiplication
   by the nonzero element `t`, so `t` is a nonzerodivisor on the completion
   (`def-weil-pbc-flat-ring-map`, `def-weil-pbc-adic-completion`).
2. Each associated prime of the principal quotient is minimal over `(t)` by hypothesis.
   The height bound for a one-element ideal gives height at most one; the nonzero element
   in the domain gives height at least one. Localization has dimension one and is Noetherian
   (`lem-weil-pbc-noetherian-height-quotient-bound`,
   `lem-weil-pbc-localization-dimension-chains-below-prime`,
   `lem-weil-pbc-localization-noetherian`, `def-weil-pbc-localization-at-prime`).
3. The already-proved `IsRegularLocalRing.isDiscreteValuationRing` turns a regular
   one-dimensional local ring into a DVR (`lem-sc-regular-dim1-dvr`).
4. The DVR and analytically unramified prime quotient imply that localizations of the
   completion at associated primes of the completed prime quotient are DVRs, hence domains
   (`lem-weil-pbc-codimension-one-analytically-unramified`,
   `def-weil-pbc-analytically-unramified`).
5. `associatedPrimes_quotient_map_of_flat` specializes the Bourbaki formula to quotient
   rings (`lem-weil-pbc-associated-primes-flat-quotient`). It identifies the associated
   primes of the completed principal quotient
   with the union of those of the completed prime quotients
   (`lem-weil-pbc-associated-primes-flat-base-change`,
   `lem-weil-pbc-noetherian-completion-flat`); tensoring the principal presentation gives
   the required quotient identification. Thus the completion localized at each such prime
   is a domain.
6. A square-zero element `y` of the completion vanishes in these domain localizations.
   Injection of a module into its localizations at associated primes shows that its class
   modulo `t` vanishes (`lem-weil-pbc-module-injects-localizations-associated-primes`,
   `def-weil-pbc-module-localization`, `def-weil-pbc-localization-at-prime`,
   `lem-weil-pbc-adic-completion-noetherian`). Write `y = t * y'`; cancellation of the
   nonzerodivisor `t` twice gives that `y'` is square-zero.
7. Induction puts every square-zero element in every power of `(t)`. Since `(t)` lies in
   the maximal ideal of the Noetherian local completion, Krull intersection makes it zero
   (`lem-weil-pbc-krull-intersection-jacobson`, `lem-weil-pbc-local-completion-local-ring`,
   `lem-weil-pbc-adic-completion-noetherian`).
8. If a nonzero nilpotent had least vanishing power `n > 1`, its `(n - 1)`-st power would
   be nonzero and square-zero, a contradiction. Thus the completion is reduced, which is
   analytic unramifiedness (`def-weil-pbc-analytically-unramified`). -/
theorem isAnalyticallyUnramified_of_principal_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (t : A) (ht : t ≠ 0) (htm : t ∈ IsLocalRing.maximalIdeal A)
    (hnoEmbedded : ∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {t}),
      (Ideal.span {t}).IsMinimalPrime p)
    (hregular : ∀ p : associatedPrimes A (A ⧸ Ideal.span {t}),
      IsRegularLocalRing (Localization.AtPrime p.1))
    (hunramified : ∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {t}),
      p.IsAnalyticallyUnramified) :
    IsAnalyticallyUnramified A := by
  let B := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have : IsNoetherianRing B := AdicCompletion.isNoetherianRing _
  let x : B := algebraMap A B t
  have hxm : x ∈ IsLocalRing.maximalIdeal B := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ htm
  have hx : Function.Injective (fun y : B => x * y) := by
    simpa only [IsSMulRegular, x, Algebra.smul_def] using
      (Module.Flat.isSMulRegular_of_nonZeroDivisors
        (M := B) (mem_nonZeroDivisors_of_ne_zero ht))
  apply reduced_of_principal_associated_localizations B x hxm hx
  intro q
  have hq : q.1 ∈ associatedPrimes B
      (B ⧸ (Ideal.span {t}).map (algebraMap A B)) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact q.2
  obtain ⟨p, hp, hqp⟩ :=
    associatedPrimes_quotient_map_of_flat A B (Ideal.span {t}) q.1 hq
  have : p.IsPrime := hp.isPrime
  have hmin := hnoEmbedded p hp
  have hheight : p.height = 1 := by
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
        (Ideal.span {t}) p hmin
    · exact (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ht)).trans (Ideal.height_mono hmin.le)
  have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, hheight]
    rfl
  have : IsRegularLocalRing (Localization.AtPrime p) := hregular ⟨p, hp⟩
  have : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsRegularLocalRing.isDiscreteValuationRing _ hdim
  obtain ⟨hdom, _⟩ :=
    AdicCompletion.isDiscreteValuationRing_atPrime_of_isAnalyticallyUnramified
      A p (hunramified p hp) q.1 ((isAssociatedPrime_iff.mp hqp).2)
  exact hdom
