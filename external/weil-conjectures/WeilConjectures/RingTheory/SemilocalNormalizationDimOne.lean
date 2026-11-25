/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres

/-!
# Normalization of a one-dimensional semilocal domain

Source: Stacks Project, Varieties, Lemma 09N2, opening normalization clause, and
Algebra, Lemma 09IG (blueprint: lem-sc-semilocal-dim-one-normalization).
-/

@[expose] public section

universe u v

namespace integralClosure

/-- Apply the normalization theorem in one universe and deduce semilocality from its
finite spectral fibres over the maximal ideals of the base. -/
private theorem normalization_same_universe
    (B K : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] [Field K] [Algebra B K] [IsFractionRing B K]
    (hdim : ringKrullDim B = 1) :
    Finite (MaximalSpectrum (integralClosure B K)) ∧
      IsDedekindDomain (integralClosure B K) ∧ ringKrullDim (integralClosure B K) = 1 := by
  classical
  obtain ⟨hD, hdimC, _, hfib, _⟩ :=
    AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres B K K hdim
  let C := integralClosure B K
  let f := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap B C))
  let g : MaximalSpectrum C → MaximalSpectrum B := fun x =>
    ⟨x.asIdeal.comap (algebraMap B C),
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal x.asIdeal⟩
  have hfinite (y : MaximalSpectrum B) : Finite (f ⁻¹' {y.toPrimeSpectrum}) :=
    hfib y.toPrimeSpectrum
  let j : MaximalSpectrum C → Σ y : MaximalSpectrum B, f ⁻¹' {y.toPrimeSpectrum} :=
    fun x => ⟨g x, ⟨x.toPrimeSpectrum, by rfl⟩⟩
  have hj : Function.Injective j := by
    intro x z hxz
    have hp : x.toPrimeSpectrum = z.toPrimeSpectrum := by
      exact congrArg (fun t => t.2.1) hxz
    exact MaximalSpectrum.toPrimeSpectrum_injective hp
  exact ⟨Finite.of_injective j hj, hD, hdimC⟩

/-- The normalization of a semilocal Noetherian domain of dimension one in its fraction
field is semilocal, Noetherian, an integrally closed domain of dimension one, and has
that same fraction field. Mathlib's Dedekind predicate permits dimension zero, so
dimension one is stated separately to retain the node's convention.
Source: Stacks Project, Varieties Lemma 09N2, opening normalization clause, invoking
Algebra Lemma 09IG (`lemma-integral-closure-Dedekind`).
(blueprint: lem-sc-semilocal-dim-one-normalization).

Proof:
1. First use the canonical fraction field `F = FractionRing B`, which lies in the
   universe of `B`. Apply `lem-sc-integral-closure-dedekind-surjective-fibres`
   with both extension fields equal to `F`. The integral closure is Dedekind
   of dimension one and its spectral map has finite fibres. By
   `lem-weil-pbc-integral-maximal-contracts-maximal`, maximal ideals contract to
   maximal ideals under the integral inclusion.
2. Since `B` has finitely many maximal ideals and each spectral fibre is finite,
   the maximal ideals of its integral closure form a finite union of finite sets.
   In Lean, embed its maximal spectrum into the finite sigma type of spectral
   fibres indexed by the maximal spectrum of `B`. Transport semilocality,
   Dedekindness and dimension along the integral-closure equivalence induced by
   the canonical `B`-algebra equivalence `F ≃ₐ[B] K`.
3. The inclusions `B ⊆ integralClosure B K ⊆ K` show that its fraction field is
   contained in `K` and contains the fraction field `K` of `B`, hence equals `K`.
   This is Mathlib's `integralClosure.isFractionRing_of_finite_extension K K`. -/
theorem semilocal_normalization_dim_one
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    (K : Type v) [Field K] [Algebra B K] [IsFractionRing B K] :
    Finite (MaximalSpectrum (integralClosure B K)) ∧
      IsDedekindDomain (integralClosure B K) ∧ ringKrullDim (integralClosure B K) = 1 ∧
      IsFractionRing (integralClosure B K) K := by
  let F := FractionRing B
  obtain ⟨hfinite, hD, hdimF⟩ := normalization_same_universe B F hdim
  have : Finite (MaximalSpectrum (integralClosure B F)) := hfinite
  have : IsDedekindDomain (integralClosure B F) := hD
  let e := (FractionRing.algEquiv B K).mapIntegralClosure
  have : IsNoetherianRing (integralClosure B K) :=
    isNoetherianRing_of_ringEquiv (integralClosure B F) e.toRingEquiv
  have : Ring.DimensionLEOne (integralClosure B K) :=
    Ring.DimensionLEOne.of_ringEquiv e.symm.toRingEquiv
  have : IsIntegrallyClosed (integralClosure B K) :=
    IsIntegrallyClosed.of_equiv e.toRingEquiv
  have hD' : IsDedekindDomain (integralClosure B K) := { }
  let j : MaximalSpectrum (integralClosure B K) →
      MaximalSpectrum (integralClosure B F) := fun x =>
    ⟨x.asIdeal.comap e.toRingHom,
      x.isMaximal.comap_bijective e.toRingHom e.bijective⟩
  have hj : Function.Injective j := by
    intro x z h
    apply MaximalSpectrum.ext
    have h' := congrArg MaximalSpectrum.asIdeal h
    exact (Ideal.relIsoOfBijective e.toRingHom e.bijective).injective h'
  exact ⟨Finite.of_injective j hj, hD',
    (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm.trans hdimF,
    isFractionRing_of_finite_extension K K⟩

end integralClosure
