/-
Copyright (c) 2026 Claude Agent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Agent
-/

module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Generic étaleness of integral closures

Let `R` be a noetherian integrally closed domain (e.g. a Dedekind domain) with fraction field
`K`, let `L / K` be a finite separable extension and let `S` be the integral closure of `R`
in `L`. We show that there is a nonzero `π : R` such that `S[1/π]` is finite étale over
`R[1/π]`.

## Main results

- `Algebra.exists_etale_isLocalizationAway_of_isIntegralClosure` : the statement for an
  arbitrary `S` with `IsIntegralClosure S R L` and arbitrary localizations `R' = R[1/π]`,
  `S' = S[1/π]`.
- `Algebra.exists_etale_isLocalizationAway_integralClosure` : the special case
  `S = integralClosure R L`.

## Proof

The generic point of `Spec S` lies in the étale locus of `S` over `R`, because the fraction
field `L` of `S` is formally étale over `R` (as a composition of the localization `R → K` and
the separable extension `K → L`). Since `S` is finitely presented over `R`, the étale locus is
open, so it contains a basic open `D(f)` with `f ≠ 0`. As `S` is integral over `R`, `f` divides
some nonzero `π ∈ R`, and then `D(π) ⊆ D(f)`.
-/

@[expose] public section

namespace Algebra

variable {R K L S : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [Algebra R L] [IsScalarTower R K L]
  [CommRing S] [Algebra R S] [Algebra S L] [IsScalarTower R S L] [IsIntegralClosure S R L]

include K L in
/-- The integral closure `S` of a domain `R` in a finite separable extension `L` of its fraction
field is étale over `R` at its generic point, i.e. `Frac(S) = L` is formally étale over `R`. -/
theorem isEtaleAt_bot_of_isIntegralClosure [IsDomain S] : IsEtaleAt R (⊥ : Ideal S) := by
  have : FormallyEtale R K := .of_isLocalization (nonZeroDivisors R)
  have : FormallyEtale K L := .of_isSeparable K L
  have : FormallyEtale R L := .comp R K L
  have : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have : IsLocalization (⊥ : Ideal S).primeCompl L := by
    simpa [Ideal.primeCompl_bot] using this
  exact .of_equiv ((IsLocalization.algEquiv (⊥ : Ideal S).primeCompl L
    (Localization.AtPrime (⊥ : Ideal S))).restrictScalars R)

variable [IsNoetherianRing R] [IsIntegrallyClosed R]

include K L in
/-- **Generic étaleness**: if `S` is the integral closure of a noetherian integrally closed
domain `R` (e.g. a Dedekind domain) in a finite separable extension `L` of its fraction field
`K`, then there is a nonzero `π : R` such that `S' = S[1/π]` is a finite étale domain over
`R' = R[1/π]`. -/
theorem exists_etale_isLocalizationAway_of_isIntegralClosure :
    ∃ π : R, π ≠ 0 ∧ ∀ (R' S' : Type*) [CommRing R'] [CommRing S'] [Algebra R R']
      [Algebra S S'] [Algebra R S'] [Algebra R' S'] [IsScalarTower R R' S']
      [IsScalarTower R S S'] [IsLocalization.Away π R']
      [IsLocalization.Away (algebraMap R S π) S'],
      Module.Finite R' S' ∧ Algebra.Etale R' S' ∧ IsDomain S' := by
  have : IsDomain S := (IsIntegralClosure.algebraMap_injective S R L).isDomain _
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have : FinitePresentation R S := FinitePresentation.of_finiteType.mp inferInstance
  have : IsEtaleAt R (⊥ : Ideal S) := isEtaleAt_bot_of_isIntegralClosure (K := K) (L := L)
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hf, hfU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) ∈ etaleLocus R S from
        ‹IsEtaleAt R (⊥ : Ideal S)›) isOpen_etaleLocus
  have hf0 : f ≠ 0 := by simpa using hf
  have hcomap := Ideal.under_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self f)
    (Algebra.IsIntegral.isIntegral (R := R) f)
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hπ)
  have hinj : Function.Injective (algebraMap R S) := by
    refine Function.Injective.of_comp (f := algebraMap S L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L,
      RingHom.coe_comp]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  refine ⟨π, hπ0, fun R' S' _ _ _ _ _ _ _ _ _ _ ↦ ?_⟩
  have hS : FormallyEtale R (Localization.Away (algebraMap R S π)) := by
    rw [← basicOpen_subset_etaleLocus_iff]
    refine subset_trans ?_ hfU
    rw [← hg, PrimeSpectrum.basicOpen_mul]
    exact inf_le_right
  have : FormallyEtale R S' := .of_equiv <| AlgEquiv.restrictScalars R <|
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R S π))
      (Localization.Away (algebraMap R S π)) S'
  have : IsLocalization (algebraMapSubmonoid S (Submonoid.powers π)) S' := by
    rw [algebraMapSubmonoid_powers]
    infer_instance
  have hfin : Module.Finite R' S' := .of_isLocalization R S (Submonoid.powers π)
  have : FormallyUnramified R R' := .of_isLocalization (Submonoid.powers π)
  have : IsNoetherianRing R' := IsLocalization.isNoetherianRing (Submonoid.powers π) R'
    inferInstance
  have : FormallyEtale R' S' := .of_restrictScalars (R := R)
  refine ⟨hfin, { finitePresentation := FinitePresentation.of_finiteType.mp inferInstance }, ?_⟩
  exact IsLocalization.isDomain_of_le_nonZeroDivisors S' (M := .powers (algebraMap R S π))
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      ((map_ne_zero_iff _ hinj).mpr hπ0))

include K in
/-- **Generic étaleness** for `integralClosure R L`: if `R` is a noetherian integrally closed
domain (e.g. a Dedekind domain) with fraction field `K` and `L / K` is finite separable, then
there is a nonzero `π : R` such that `S' = (integralClosure R L)[1/π]` is a finite étale domain
over `R' = R[1/π]`. -/
theorem exists_etale_isLocalizationAway_integralClosure :
    ∃ π : R, π ≠ 0 ∧ ∀ (R' S' : Type*) [CommRing R'] [CommRing S'] [Algebra R R']
      [Algebra (integralClosure R L) S'] [Algebra R S'] [Algebra R' S']
      [IsScalarTower R R' S'] [IsScalarTower R (integralClosure R L) S']
      [IsLocalization.Away π R']
      [IsLocalization.Away (algebraMap R (integralClosure R L) π) S'],
      Module.Finite R' S' ∧ Algebra.Etale R' S' ∧ IsDomain S' :=
  exists_etale_isLocalizationAway_of_isIntegralClosure (K := K) (L := L)

end Algebra
