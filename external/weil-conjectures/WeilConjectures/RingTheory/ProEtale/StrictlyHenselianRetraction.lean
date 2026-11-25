/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Inverse
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale

/-!
# Weakly étale covers of strictly henselian local rings split

A strictly henselian local ring `R` is w-contractible: its spectrum is w-local with a single
closed point, its localization at the maximal ideal is `R` itself, and the space of connected
components of `Spec R` is a point. Hence every faithfully flat ind-étale `R`-algebra has a
retraction, and so does every faithfully flat weakly étale `R`-algebra, which becomes ind-étale
over `R` after a faithfully flat ind-étale extension (Stacks 097Z).

The power series ring `k⟦X⟧` over a separably closed field is strictly henselian, being
complete for its maximal ideal `(X)`.

## Main statements

- `IsStrictlyHenselianLocalRing.isWContractibleRing`
- `IsStrictlyHenselianLocalRing.exists_retraction_of_weaklyEtale`
- `PowerSeries.isStrictlyHenselianLocalRing`
-/

@[expose] public section

universe u

open PrimeSpectrum IsLocalRing

/-- The prime spectrum of a local ring is a w-local space: every point specializes to the
unique closed point, and the set of closed points is the closed singleton of the closed point. -/
theorem IsLocalRing.wLocalSpace_primeSpectrum (R : Type*) [CommRing R] [IsLocalRing R] :
    WLocalSpace (PrimeSpectrum R) where
  eq_of_specializes {_ c c'} hc hc' _ _ := by
    have := (isClosed_singleton_iff_isMaximal c).mp hc
    have := (isClosed_singleton_iff_isMaximal c').mp hc'
    ext1
    rw [eq_maximalIdeal ‹c.asIdeal.IsMaximal›, eq_maximalIdeal ‹c'.asIdeal.IsMaximal›]
  isClosed_closedPoints := by
    convert (isClosed_singleton_iff_isMaximal (closedPoint R)).mpr (maximalIdeal.isMaximal R)
      using 1
    ext x
    rw [mem_closedPoints_iff, isClosed_singleton_iff_isMaximal, Set.mem_singleton_iff]
    refine ⟨fun h ↦ PrimeSpectrum.ext (eq_maximalIdeal h), ?_⟩
    rintro rfl
    exact maximalIdeal.isMaximal R

/-- The space of connected components of the prime spectrum of a local ring is a point: every
point specializes to the closed point. -/
theorem IsLocalRing.subsingleton_connectedComponents (R : Type*) [CommRing R] [IsLocalRing R] :
    Subsingleton (ConnectedComponents (PrimeSpectrum R)) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
  rw [(specializes_closedPoint x).connectedComponents_mk_eq,
    (specializes_closedPoint y).connectedComponents_mk_eq]

/-- A subsingleton space is extremally disconnected. -/
theorem ExtremallyDisconnected.of_subsingleton (X : Type*) [TopologicalSpace X]
    [Subsingleton X] : ExtremallyDisconnected X where
  open_closure U _ := by
    rcases (closure U).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]
      exact isOpen_empty
    · have h : closure U = Set.univ := Set.eq_univ_of_forall fun y ↦ Subsingleton.elim x y ▸ hx
      rw [h]
      exact isOpen_univ

/-- A strictly henselian local ring is w-contractible. -/
theorem IsStrictlyHenselianLocalRing.isWContractibleRing (R : Type u) [CommRing R]
    [IsStrictlyHenselianLocalRing R] : IsWContractibleRing R where
  wLocalSpace_primeSepectrum := IsLocalRing.wLocalSpace_primeSpectrum R
  isStrictlyHenselianLocalRing_localization m hm := by
    obtain rfl := eq_maximalIdeal hm
    refine .of_ringEquiv (IsLocalization.atUnits R (maximalIdeal R).primeCompl
      (S := Localization.AtPrime (maximalIdeal R)) fun x hx ↦ ?_).toRingEquiv
    by_contra h
    exact hx ((mem_maximalIdeal x).mpr h)
  extremallyDisconnected_connectedComponents :=
    have := IsLocalRing.subsingleton_connectedComponents R
    .of_subsingleton _

/-- A faithfully flat weakly étale algebra over a strictly henselian local ring has a
retraction. -/
theorem IsStrictlyHenselianLocalRing.exists_retraction_of_weaklyEtale {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [IsStrictlyHenselianLocalRing R]
    [Algebra.WeaklyEtale R S] [Module.FaithfullyFlat R S] :
    ∃ f : S →+* R, f.comp (algebraMap R S) = RingHom.id R := by
  obtain ⟨T, _, _, _, _, -, _, _⟩ := Algebra.WeaklyEtale.exists_indEtale R S
  have : Module.FaithfullyFlat R T := .trans R S T
  have := isWContractibleRing R
  obtain ⟨g, hg⟩ := IsWContractibleRing.exists_retraction (R := R) T
  refine ⟨g.comp (algebraMap S T), ?_⟩
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hg]

/-- The power series ring over a field is a henselian local ring, being complete for its
maximal ideal `(X)`. -/
instance PowerSeries.henselianLocalRing (k : Type u) [Field k] :
    HenselianLocalRing (PowerSeries k) where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ h₁ h₂ := by
    rw [maximalIdeal_eq_span_X] at h₁ ⊢
    exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

/-- The residue field of `k⟦X⟧` is `k`. -/
noncomputable def PowerSeries.residueFieldEquiv (k : Type u) [Field k] :
    k ≃+* ResidueField (PowerSeries k) :=
  RingEquiv.ofBijective (algebraMap k (ResidueField (PowerSeries k)))
    ⟨(algebraMap k _).injective, fun y ↦ by
      obtain ⟨f, rfl⟩ := residue_surjective y
      refine ⟨constantCoeff f, ?_⟩
      rw [IsScalarTower.algebraMap_apply k (PowerSeries k), ResidueField.algebraMap_eq,
        ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, maximalIdeal_eq_span_X,
        Ideal.mem_span_singleton, X_dvd_iff]
      simp⟩

/-- The power series ring over a separably closed field is a strictly henselian local ring. -/
instance PowerSeries.isStrictlyHenselianLocalRing (k : Type u) [Field k] [IsSepClosed k] :
    IsStrictlyHenselianLocalRing (PowerSeries k) where
  isSepClosed_residueField := .of_ringEquiv (residueFieldEquiv k)
