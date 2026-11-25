/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Spectra of finitely generated algebras over a field

The spectrum of a finitely generated algebra over a field is a Noetherian space: descending chains
of closed subsets stabilize, and there are finitely many irreducible components.

## Main results

- `PrimeSpectrum.finite_irreducibleComponents_of_finiteType`
- `IsArtinianRing.card_primeSpectrum_le_finrank`: a finite-dimensional algebra over a field has
  at most as many prime ideals as its dimension.
- `Ideal.exists_notMem_forall_of_isNoetherianRing`: *Nagata's criterion* for a set of primes of a
  noetherian ring to be open.

## Blueprint

- `lem-wf-affine-noetherian-components`: affine schemes of finite type are Noetherian with
  finitely many irreducible components.
-/

@[expose] public section

namespace PrimeSpectrum

/-- Blueprint `lem-wf-affine-noetherian-components`: the spectrum of a finitely generated algebra
`A` over a field `k` is a Noetherian space with finitely many irreducible components.

The ring `A` is Noetherian by the Hilbert basis theorem (`Algebra.FiniteType.isNoetherianRing`),
so `Spec A` is a Noetherian space (`PrimeSpectrum.instNoetherianSpace`), and a Noetherian space
has finitely many irreducible components. -/
theorem finite_irreducibleComponents_of_finiteType (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] :
    TopologicalSpace.NoetherianSpace (PrimeSpectrum A) ∧
      (irreducibleComponents (PrimeSpectrum A)).Finite := by
  have := Algebra.FiniteType.isNoetherianRing k A
  exact ⟨inferInstance, TopologicalSpace.NoetherianSpace.finite_irreducibleComponents⟩


end PrimeSpectrum

/-- A finite-dimensional algebra over a field has at most as many prime ideals as its
dimension. -/
lemma IsArtinianRing.card_primeSpectrum_le_finrank (K A : Type*) [Field K] [CommRing A]
    [Algebra K A] [Module.Finite K A] :
    Nat.card (PrimeSpectrum A) ≤ Module.finrank K A := by
  have : IsArtinianRing A := .of_finite K A
  have := Fintype.ofFinite (PrimeSpectrum A)
  rw [Nat.card_eq_fintype_card, IsArtinianRing.finrank_eq_sum_primeSpectrum (R := A) K,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  have : Module.Finite K (Localization.AtPrime p.asIdeal) :=
    .of_surjective (Algebra.algHom K A (Localization.AtPrime p.asIdeal)).toLinearMap
      (localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
  exact Module.finrank_pos

/-- **Nagata's criterion for openness** (Matsumura, Theorem 24.2; Stacks, Tag 0541). Let `U` be a
property of primes of a noetherian ring `S` which is stable under generalization and such that
for each `P` with `U P`, the property holds on a neighbourhood of `P` in `V(P)`. Then `U` holds on a
neighbourhood `D(g)` of each prime where it holds. -/
theorem Ideal.exists_notMem_forall_of_isNoetherianRing {S : Type*} [CommRing S]
    [IsNoetherianRing S] (U : Ideal S → Prop)
    (hgen : ∀ P Q : Ideal S, P.IsPrime → Q.IsPrime → Q ≤ P → U P → U Q)
    (hloc : ∀ P : Ideal S, P.IsPrime → U P →
      ∃ g ∉ P, ∀ Q : Ideal S, Q.IsPrime → P ≤ Q → g ∉ Q → U Q)
    (P : Ideal S) [P.IsPrime] (hP : U P) :
    ∃ g ∉ P, ∀ Q : Ideal S, Q.IsPrime → g ∉ Q → U Q := by
  classical
  -- `J` is the intersection of the primes where `U` fails.
  set J : Ideal S := sInf {Q | Q.IsPrime ∧ ¬ U Q}
  have hJ (Q : Ideal S) (hQ : Q.IsPrime) (hUQ : ¬ U Q) : J ≤ Q := sInf_le ⟨hQ, hUQ⟩
  -- Every minimal prime over `J` fails `U`.
  have hmin : ∀ Q₀ ∈ J.minimalPrimes, ¬ U Q₀ := by
    intro Q₀ hQ₀ hU
    have hQ₀p : Q₀.IsPrime := hQ₀.1.1
    obtain ⟨g₀, hg₀, hg₀U⟩ := hloc Q₀ hQ₀p hU
    have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing S J
    set others := hfin.toFinset.erase Q₀
    have hnot : ¬ others.inf id ≤ Q₀ := by
      intro hle
      obtain ⟨Q₁, hQ₁, hQ₁le⟩ := (Ideal.IsPrime.inf_le' (s := others) (f := id) hQ₀p).mp hle
      obtain ⟨hne, hQ₁m⟩ := Finset.mem_erase.mp hQ₁
      rw [Set.Finite.mem_toFinset] at hQ₁m
      exact hne (le_antisymm hQ₁le (hQ₀.2 hQ₁m.1 hQ₁le))
    obtain ⟨h, hh, hhQ₀⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    have hgh : g₀ * h ∉ J := fun hmem ↦
      (hQ₀p.mul_mem_iff_mem_or_mem.mp (hQ₀.1.2 hmem)).elim hg₀ hhQ₀
    have : ¬ ∀ Q ∈ {Q : Ideal S | Q.IsPrime ∧ ¬ U Q}, g₀ * h ∈ Q := fun H ↦
      hgh (Submodule.mem_sInf.mpr H)
    push Not at this
    obtain ⟨Q', ⟨hQ'p, hQ'U⟩, hQ'⟩ := this
    obtain ⟨Q₁, hQ₁, hQ₁le⟩ := Ideal.exists_minimalPrimes_le (hJ Q' hQ'p hQ'U)
    have hhQ' : h ∉ Q' := fun hm ↦ hQ' (Q'.mul_mem_left _ hm)
    have hQ₁eq : Q₁ = Q₀ := by
      by_contra hne
      have : Q₁ ∈ others := Finset.mem_erase.mpr ⟨hne, (Set.Finite.mem_toFinset _).mpr hQ₁⟩
      exact hhQ' (hQ₁le (Finset.inf_le (f := id) this hh))
    subst hQ₁eq
    exact hQ'U (hg₀U Q' hQ'p hQ₁le fun hm ↦ hQ' (Q'.mul_mem_right _ hm))
  -- Hence `U` fails exactly on `V(J)`.
  have hV : ∀ Q : Ideal S, Q.IsPrime → J ≤ Q → ¬ U Q := by
    intro Q hQ hJQ hUQ
    obtain ⟨Q₀, hQ₀, hQ₀le⟩ := Ideal.exists_minimalPrimes_le hJQ
    exact hmin Q₀ hQ₀ (hgen Q Q₀ hQ hQ₀.1.1 hQ₀le hUQ)
  obtain ⟨g, hgJ, hgP⟩ := IsConcreteLE.not_le_iff_exists.mp fun hle ↦ hV P ‹_› hle hP
  refine ⟨g, hgP, fun Q hQ hgQ ↦ ?_⟩
  by_contra hUQ
  exact hgQ (hJ Q hQ hUQ hgJ)
