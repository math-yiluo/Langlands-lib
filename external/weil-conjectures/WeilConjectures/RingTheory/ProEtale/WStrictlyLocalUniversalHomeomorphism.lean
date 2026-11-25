/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.RingTheory.FiniteLocalHenselian
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC

/-!
# w-strictly local rings and universal homeomorphisms

We show that w-strict locality is preserved by universal homeomorphisms of rings.

## Main results

- `HenselianLocalRing.of_isIntegral`: a local ring which is integral over a henselian local ring
  is henselian.
- `IsWLocalRing.of_isUniversalHomeomorphism`: w-locality is preserved by universal
  homeomorphisms.
- `IsWStrictlyLocalRing.of_isUniversalHomeomorphism`: w-strict locality is preserved by
  universal homeomorphisms.
-/

@[expose] public section

universe u v

open IsLocalRing Polynomial

/-- A local ring `B` which is integral over a henselian local ring `A` is henselian.

Given a monic `f : B[X]` with a simple root `a₀` modulo the maximal ideal, the coefficients of `f`
and `a₀` lie in a module-finite `A`-subalgebra `C` of `B`. Every maximal ideal of `C` is the
contraction of the maximal ideal of `B`, so `C` is local, hence henselian by
`finite_local_henselian`; the root of `f` in `C` is the required root in `B`. -/
theorem HenselianLocalRing.of_isIntegral (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [HenselianLocalRing A] [IsLocalRing B] [Algebra A B] [Algebra.IsIntegral A B] :
    HenselianLocalRing B where
  is_henselian f hf a₀ h₁ h₂ := by
    classical
    let C : Subalgebra A B := Algebra.adjoin A (insert a₀ (f.coeffs : Set B))
    have : Module.Finite A C := Module.Finite.iff_fg.mpr <|
      fg_adjoin_of_finite ((Finset.finite_toSet _).insert a₀)
        fun x _ ↦ Algebra.IsIntegral.isIntegral x
    have : Algebra.IsIntegral C B := Algebra.IsIntegral.tower_top A
    have hmax (M : Ideal C) (hM : M.IsMaximal) :
        M = (maximalIdeal B).comap (algebraMap C B) := by
      obtain ⟨Q, hQ, rfl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral M (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
        exact bot_le)
      rw [IsLocalRing.eq_maximalIdeal hQ]
    have : IsLocalRing C := IsLocalRing.of_unique_max_ideal
      ⟨_, Ideal.isMaximal_under_of_isIntegral_of_isMaximal _, fun M hM ↦ hmax M hM⟩
    have hC : maximalIdeal C = (maximalIdeal B).comap (algebraMap C B) :=
      hmax _ inferInstance
    have : HenselianLocalRing C := finite_local_henselian A C
    obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap C B) (p := f)
      (lifts_iff_coeff_lifts _ |>.mpr fun n ↦ by
        by_cases hn : f.coeff n = 0
        · exact ⟨0, by simp [hn]⟩
        · exact ⟨⟨f.coeff n, Algebra.subset_adjoin
            (Set.mem_insert_of_mem _ (coeff_mem_coeffs hn))⟩, rfl⟩) hf
    let b₀ : C := ⟨a₀, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
    have heval (p : C[X]) : algebraMap C B (p.eval b₀) = (p.map (algebraMap C B)).eval a₀ := by
      rw [eval_map, eval, hom_eval₂, RingHom.comp_id]
      rfl
    obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian g hgm b₀
      (by
        rw [hC, Ideal.mem_comap, heval, hg]
        exact h₁)
      (by
        rw [← IsLocalRing.notMem_maximalIdeal, hC, Ideal.mem_comap, heval, ← derivative_map, hg,
          IsLocalRing.notMem_maximalIdeal]
        exact h₂)
    refine ⟨algebraMap C B a, ?_, ?_⟩
    · rw [IsRoot, ← hg, eval_map, eval₂_at_apply, ha.eq_zero, map_zero]
    · rw [hC, Ideal.mem_comap, map_sub] at ha'
      exact ha'

namespace Algebra.IsUniversalHomeomorphism

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  [Algebra.IsUniversalHomeomorphism R R']

/-- The map on prime spectra induced by a universal homeomorphism of rings is a closed
embedding. -/
lemma isClosedEmbedding_comap :
    Topology.IsClosedEmbedding (PrimeSpectrum.comap (algebraMap R R')) :=
  .of_continuous_injective_isClosedMap (PrimeSpectrum.continuous_comap _)
    (AlgebraicGeometry.Algebra.IsUniversalHomeomorphism.comap_injective R R')
    (PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (algebraMap_isIntegral_iff.mpr inferInstance))

/-- Along a universal homeomorphism of rings, inclusion of primes is detected after
contraction. -/
lemma comap_le_comap_iff {P Q : Ideal R'} [P.IsPrime] [Q.IsPrime] :
    P.comap (algebraMap R R') ≤ Q.comap (algebraMap R R') ↔ P ≤ Q := by
  have h := (isClosedEmbedding_comap (R := R) (R' := R')).isInducing.specializes_iff
    (x := ⟨P, ‹_›⟩) (y := ⟨Q, ‹_›⟩)
  rwa [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.le_iff_specializes,
    ← PrimeSpectrum.asIdeal_le_asIdeal, ← PrimeSpectrum.asIdeal_le_asIdeal] at h

end Algebra.IsUniversalHomeomorphism

open Algebra.IsUniversalHomeomorphism in
/-- w-locality is preserved by universal homeomorphisms of rings. -/
theorem IsWLocalRing.of_isUniversalHomeomorphism (R R' : Type u) [CommRing R] [CommRing R']
    [Algebra R R'] [Algebra.IsUniversalHomeomorphism R R'] [IsWLocalRing R] :
    IsWLocalRing R' :=
  ⟨(isClosedEmbedding_comap (R := R)).wLocalSpace⟩

open Algebra.IsUniversalHomeomorphism in
/-- Let `R → R'` be a universal homeomorphism, `m'` a maximal ideal of `R'` and `m` its
contraction. Then `R'_{m'}` is the localization of `R'` at the image of the complement of `m`. -/
lemma Algebra.IsUniversalHomeomorphism.isLocalization_atPrime_of_isMaximal {R R' : Type u}
    [CommRing R] [CommRing R'] [Algebra R R'] [Algebra.IsUniversalHomeomorphism R R']
    (m' : Ideal R') [m'.IsMaximal] (S : Type*) [CommRing S] [Algebra R' S]
    [IsLocalization (Algebra.algebraMapSubmonoid R' (m'.comap (algebraMap R R')).primeCompl) S] :
    IsLocalization.AtPrime S m' := by
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid R'
    (m'.comap (algebraMap R R')).primeCompl) _ ?_ fun s hs ↦ ?_
  · rintro _ ⟨r, hr, rfl⟩
    exact hr
  · by_contra hu
    obtain ⟨M, hM, hsM⟩ := exists_max_ideal_of_mem_nonunits hu
    have hle : (M.comap (algebraMap R' S)).comap (algebraMap R R') ≤
        m'.comap (algebraMap R R') := by
      intro r hr
      by_contra hr'
      refine hM.ne_top (M.eq_top_of_isUnit_mem hr ?_)
      exact IsLocalization.map_units S (⟨algebraMap R R' r, r, hr', rfl⟩ :
        Algebra.algebraMapSubmonoid R' (m'.comap (algebraMap R R')).primeCompl)
    exact hs ((comap_le_comap_iff (R := R)).mp hle hsM)

open Algebra.IsUniversalHomeomorphism in
/-- w-strict locality is preserved by universal homeomorphisms of rings. -/
theorem IsWStrictlyLocalRing.of_isUniversalHomeomorphism (R R' : Type u) [CommRing R]
    [CommRing R'] [Algebra R R'] [Algebra.IsUniversalHomeomorphism R R']
    [IsWStrictlyLocalRing R] :
    IsWStrictlyLocalRing R' where
  __ := IsWLocalRing.of_isUniversalHomeomorphism R R'
  isStrictlyHenselianLocalRing_localization m' _ := by
    let m := m'.comap (algebraMap R R')
    have : m.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m'
    have hR := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization (R := R) m
    let S := Localization (Algebra.algebraMapSubmonoid R' m.primeCompl)
    have : IsLocalization.AtPrime S m' := isLocalization_atPrime_of_isMaximal (R := R) m' S
    have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S m'
    have : Algebra.IsIntegral (Localization.AtPrime m) S :=
      ⟨isIntegral_localization (M := m.primeCompl) (S := R')⟩
    have : HenselianLocalRing S := HenselianLocalRing.of_isIntegral (Localization.AtPrime m) S
    have : HenselianLocalRing (Localization.AtPrime m') :=
      .of_ringEquiv (IsLocalization.algEquiv m'.primeCompl S _).toRingEquiv
    have hpi :=
      AlgebraicGeometry.Algebra.IsUniversalHomeomorphism.isPurelyInseparable_residueField_map
        (A := R) m'
    let := (Ideal.ResidueField.map (m'.under R) m' (algebraMap R R') rfl).toAlgebra
    have : IsPurelyInseparable m.ResidueField m'.ResidueField := hpi
    have : Algebra.IsAlgebraic m.ResidueField m'.ResidueField := IsPurelyInseparable.isAlgebraic _ _
    exact ⟨Algebra.IsAlgebraic.isSepClosed (F := m.ResidueField)⟩
