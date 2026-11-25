/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree

/-! # A finite standard free cover for a finite projective module

Source: Stacks Project, Lemma Tag 00NX, (3)⇒(7), and Definition Tag 00NW
in Section Tag 00NV (blueprint: lem-weil-pbc-finite-projective-standard-free-cover).
-/

@[expose] public section

universe u v

namespace Module

/-- A finite projective module is finite free on a finite standard cover.
Source: Stacks Project, Lemma Tag 00NX, (3)⇒(7), and Definition Tag 00NW
(blueprint: lem-weil-pbc-finite-projective-standard-free-cover).
Proof, step 1: a direct summand of a finite free module is finite projective.
For each prime p, `proposition-projective-line-rational-coefficients--1` gives an element
fₚ outside p such that M localized away from fₚ is finite free.
Step 2: these principal opens cover Spec A. Apply quasi-compactness and the
principal-open/unit-ideal criterion in
`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` to choose finitely many of
them whose elements generate the unit ideal. Each chosen localization remains
finite free by step 1. The ranks may differ between members of the cover. -/
theorem exists_standardFreeCover_of_finite_projective
    (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] :
    ∃ (r : ℕ) (f : Fin r → A), Ideal.span (Set.range f) = ⊤ ∧
      ∀ i : Fin r,
        Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) M) ∧
        Module.Free (Localization.Away (f i)) (LocalizedModule.Away (f i) M) := by
  let hp : ∀ p : PrimeSpectrum A, ∃ f : A, f ∉ p.asIdeal ∧
      ∃ r : ℕ, Nonempty (LocalizedModule.Away f M ≃ₗ[Localization.Away f]
        (Fin r →₀ Localization.Away f)) := fun p =>
    exists_localizationAway_equiv_finsupp_of_finite_projective p.asIdeal
  let g : PrimeSpectrum A → A := fun p => (Classical.choose (hp p))
  have hg : ∀ p : PrimeSpectrum A, g p ∉ p.asIdeal := by
    intro p
    exact (Classical.choose_spec (hp p)).1
  have hcov : (Set.univ : Set (PrimeSpectrum A)) ⊆
      ⋃ p, PrimeSpectrum.basicOpen (g p) := by
    intro p hp
    simp only [Set.mem_iUnion]
    exact ⟨p, (PrimeSpectrum.mem_basicOpen (g p) p).2 (hg p)⟩
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (PrimeSpectrum A))).elim_finite_subcover
      (fun p => PrimeSpectrum.basicOpen (g p)) (fun p => PrimeSpectrum.isOpen_basicOpen) hcov
  let r := Fintype.card t
  let e : Fin r ≃ t := (Fintype.equivFin t).symm
  let f : Fin r → A := fun i => g (e i).1
  refine ⟨r, f, ?_, ?_⟩
  · apply (PrimeSpectrum.iSup_basicOpen_eq_top_iff).mp
    apply top_unique
    intro p hp_top
    have hp' := ht (Set.mem_univ p)
    rcases Set.mem_iUnion.mp hp' with ⟨q, hp'⟩
    rcases Set.mem_iUnion.mp hp' with ⟨hq, hpq⟩
    let j : Fin r := e.symm ⟨q, hq⟩
    have hj : p ∈ PrimeSpectrum.basicOpen (f j) := by
      simpa [f, j] using hpq
    exact (show PrimeSpectrum.basicOpen (f j) ≤ (⨆ i, PrimeSpectrum.basicOpen (f i)) from
      le_iSup (fun i : Fin r => PrimeSpectrum.basicOpen (f i)) j) hj
  · intro i
    obtain ⟨hi, ri, ⟨equiv⟩⟩ := Classical.choose_spec (hp (e i).1)
    have hfi : f i = Classical.choose (hp (e i).1) := rfl
    rw [hfi]
    exact ⟨Module.Finite.equiv equiv.symm, Module.Free.of_equiv equiv.symm⟩
end Module
