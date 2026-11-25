/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import WeilConjectures.RingTheory.AdjoinQuotientSurjective
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# Contraction of associated primes of a fractional monogenic principal quotient

Source: Stacks Project, Algebra, Tag 0334, Step 5, the quotient presentation and
associated-prime comparison used to verify (2) and (3)(a).
(blueprint: lem-weil-pbc-monogenic-associated-contraction).
-/

@[expose] public section

universe u v

open Module.associatedPrimes

/-- A constant divisible by the generator in the adjoin is already divisible over the base. -/
private theorem base_mem_principal_iff
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (x : K) (hx0 : x ≠ 0) (r : R) :
    algebraMap R (Algebra.adjoin R ({x} : Set K)) r ∈ Ideal.span
        {(⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ :
          Algebra.adjoin R ({x} : Set K))} ↔
      algebraMap R K r ∈ Submodule.span R ({x} : Set K) := by
  let S := Algebra.adjoin R ({x} : Set K)
  let t : S := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  constructor
  · intro hr
    obtain ⟨⟨z, hzmem⟩, hz⟩ := Ideal.mem_span_singleton'.mp hr
    by_cases hr0 : r = 0
    · simp [hr0]
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hzmem
    obtain ⟨f, hf⟩ := hzmem
    change Polynomial.aeval x f = z at hf
    let P : Polynomial R := Polynomial.C r - Polynomial.X * f
    have hconst : P.coeff 0 = r := by simp [P]
    have hlead : P.reverse.leadingCoeff = r := by
      rw [Polynomial.reverse_leadingCoeff,
        Polynomial.trailingCoeff_eq_coeff_zero (hconst ▸ hr0), hconst]
    have heq : (z : K) * x = algebraMap R K r := congrArg (fun w : S ↦ (w : K)) hz
    have hroot : P.eval₂ (algebraMap R K) x = 0 := by
      change Polynomial.aeval x P = 0
      simp only [P, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, hf]
      rw [mul_comm, heq, sub_self]
    let : Invertible x := invertibleOfNonzero hx0
    have hrev : P.reverse.eval₂ (algebraMap R K) (⅟x) = 0 :=
      (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap R K) x P).mpr hroot
    have hint : IsIntegral R (algebraMap R K r * x⁻¹) := by
      simpa only [hlead, invOf_eq_inv, Algebra.smul_def] using
        isIntegral_leadingCoeff_smul P.reverse (⅟x) hrev
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
  · intro hr
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨algebraMap R S c, ?_⟩
    apply Subtype.ext
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.smul_def] using hc

/-- Associated primes of the localized monogenic principal quotient contract to
associated primes of the fractional principal quotient of the base domain.

Source: Stacks Project, Algebra, Tag 0334, Step 5, the paragraphs identifying
`S/xS = R/J` and contracting associated primes; Tag 00PQ and Tag 0310.
(blueprint: lem-weil-pbc-monogenic-associated-contraction).

Proof:
1. Put `S = R[x]` and `J = R ∩ xR`. The map `R → S/xS` is surjective:
   adjoin induction reduces this to constants, sums, products and the generator,
   whose image is zero.
2. Its kernel is `J`. One inclusion is immediate. For the other, write a constant
   `r` in `xS` as `r = x f(x)` and put `P = C r - X f`. If `r = 0`, membership
   in `J` is automatic. Otherwise `P` has constant coefficient `r`; its reverse
   polynomial vanishes at `x⁻¹` and has leading coefficient `r`. Tag 00PQ says
   `r/x` is integral over `R`, hence in `R` by normality. Thus `r ∈ xR`.
   The first isomorphism theorem now gives `R/J ≃ S/xS`.
3. Let `p` be the given associated prime of `S_m/xS_m`, and contract it to
   `qS` in `S`. The quotient `S_m/xS_m` is the localization of `S/xS`.
   Since `S` is Noetherian and `S/xS` is finite, associated primes commute
   with localization (Tag 0310), so `qS` is associated to `S/xS`.
4. Choose a nonzero class whose annihilator over `S` is `qS`. Its annihilator
   over `R` is `qS ∩ R`; transport the class across the isomorphism of step 2.
   Hence `qS ∩ R` is associated to `R/J`. If the principal quotient is zero,
   there are no associated primes and the assertion is vacuous. -/
theorem adjoin_singleton_associated_contraction
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (x : K) (hx0 : x ≠ 0)
    [IsNoetherianRing (Algebra.adjoin R ({x} : Set K))]
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (_hx : (⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ :
      Algebra.adjoin R ({x} : Set K)) ∈ m)
    (p : associatedPrimes (Localization.AtPrime m)
      (Localization.AtPrime m ⧸ Ideal.span
        {algebraMap (Algebra.adjoin R ({x} : Set K)) (Localization.AtPrime m)
          ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩})) :
    (p.1.under (Algebra.adjoin R ({x} : Set K))).under R ∈ associatedPrimes R
      (R ⧸ (Submodule.span R ({x} : Set K)).comap (Algebra.linearMap R K)) := by
  let S := Algebra.adjoin R ({x} : Set K)
  let A := Localization.AtPrime m
  let t : S := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  let I : Ideal S := Ideal.span {t}
  let J : Ideal R := (Submodule.span R ({x} : Set K)).comap (Algebra.linearMap R K)
  let L := A ⧸ I.map (algebraMap S A)
  have hmap : I.map (algebraMap S A) = Ideal.span {algebraMap S A t} := by
    simp only [I, Ideal.map_span, Set.image_singleton]
  have hp : p.1 ∈ associatedPrimes A L := by
    change p.1 ∈ associatedPrimes A (A ⧸ I.map (algebraMap S A))
    rw [hmap]
    exact p.2
  let fL : (S ⧸ I) →ₗ[S] L := (IsScalarTower.toAlgHom S (S ⧸ I) L).toLinearMap
  have : IsLocalizedModule m.primeCompl fL := inferInstance
  have hqS : p.1.under S ∈ associatedPrimes S (S ⧸ I) :=
    comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      m.primeCompl fL p.1 hp ((isNoetherianRing_iff_ideal_fg S).mp inferInstance _)
  let qS : Ideal S := p.1.under S
  let q : Ideal R := qS.under R
  let : qS.IsPrime := inferInstance
  let : q.IsPrime := inferInstance
  obtain ⟨_, w, hw⟩ := (isAssociatedPrime_iff).mp hqS
  change qS = _ at hw
  have hqR : q ∈ associatedPrimes R (S ⧸ I) := by
    apply isAssociatedPrime_iff.mpr
    refine ⟨inferInstance, w, ?_⟩
    ext r
    change algebraMap R S r ∈ qS ↔ _
    rw [hw]
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, algebraMap_smul]
  let f : R →ₐ[R] (S ⧸ I) := Algebra.ofId R (S ⧸ I)
  have hsurj : Function.Surjective f :=
    adjoin_quotient_surjective R K ({x} : Set K) I
      (fun y hy ↦ by
        obtain rfl := Set.mem_singleton_iff.mp hy
        exact Ideal.subset_span (Set.mem_singleton t))
  have hker : RingHom.ker f = J := by
    ext r
    change algebraMap R (S ⧸ I) r = 0 ↔ _
    rw [IsScalarTower.algebraMap_apply R S (S ⧸ I), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact base_mem_principal_iff R K x hx0 r
  let e : (R ⧸ J) ≃ₐ[R] (S ⧸ I) :=
    (Ideal.quotientEquivAlgOfEq R hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  exact hqR.map_of_injective e.symm.toLinearMap e.symm.injective

