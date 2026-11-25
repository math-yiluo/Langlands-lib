/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Finite length from finitely many nonzero maximal localizations

Source: Stacks Project, Algebra, Tag 00PF, the final local-to-global argument.
-/

@[expose] public section

universe u v

namespace Module

/-- Finite local lengths and finite maximal support imply finite length.
Source: Stacks Project, Algebra, Tag 00PF, final paragraph.
(blueprint: lem-sc-finite-length-finite-maximal-support)

Proof: Send a submodule to the family of its localizations at the finitely many
maximal ideals in `S`. This map preserves and reflects inclusion: localization
detects inclusion at all maximal ideals, and the localizations outside `S` are
zero. Thus the submodule lattice embeds in the finite product of the local
submodule lattices. Each factor is both Noetherian and Artinian by its finite
length. The finite product, and hence the embedded lattice, have both ascending
and descending chain conditions. These two conditions imply finite length. -/
theorem length_lt_top_of_finite_maximal_support
    {R : Type u} [CommRing R] {Q : Type v} [AddCommGroup Q] [Module R Q]
    (S : Set (MaximalSpectrum R)) (hS : S.Finite)
    (hzero : ∀ m : MaximalSpectrum R, m ∉ S →
      Subsingleton (LocalizedModule m.asIdeal.primeCompl Q))
    (hlength : ∀ m ∈ S, Module.length (Localization m.asIdeal.primeCompl)
      (LocalizedModule m.asIdeal.primeCompl Q) < ⊤) :
    Module.length R Q < ⊤ := by
  classical
  let : Finite S := hS.to_subtype
  let L (m : S) :=
    Submodule (Localization m.1.asIdeal.primeCompl)
      (LocalizedModule m.1.asIdeal.primeCompl Q)
  have hfin (m : S) :=
    Module.length_ne_top_iff.mp (ne_of_lt (hlength m.1 m.2))
  have (m : S) : IsNoetherian (Localization m.1.asIdeal.primeCompl)
      (LocalizedModule m.1.asIdeal.primeCompl Q) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hfin m)).1
  have (m : S) : IsArtinian (Localization m.1.asIdeal.primeCompl)
      (LocalizedModule m.1.asIdeal.primeCompl Q) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hfin m)).2
  let f : Submodule R Q → ∀ m : S, L m :=
    fun N m ↦ N.localized m.1.asIdeal.primeCompl
  have hf : ∀ N P : Submodule R Q, f N ≤ f P ↔ N ≤ P := by
    intro N P
    constructor
    · intro h
      apply Submodule.le_of_localization_maximal
        (fun (m : Ideal R) [m.IsMaximal] ↦ LocalizedModule m.primeCompl Q)
        (fun (m : Ideal R) [m.IsMaximal] ↦ LocalizedModule.mkLinearMap m.primeCompl Q)
      intro m hm
      by_cases hs : (⟨m, hm⟩ : MaximalSpectrum R) ∈ S
      · exact h ⟨⟨m, hm⟩, hs⟩
      · have := hzero ⟨m, hm⟩ hs
        exact le_of_eq (Subsingleton.elim _ _)
    · intro h m
      exact (Submodule.localized'gi _ _ _).gc.monotone_l h
  let e : Submodule R Q ↪o (∀ m : S, L m) :=
    { toFun := f
      inj' := fun N P h ↦ le_antisymm ((hf N P).mp h.le) ((hf P N).mp h.ge)
      map_rel_iff' := hf _ _ }
  have : WellFoundedLT (Submodule R Q) := e.wellFoundedLT
  have : WellFoundedLT ((∀ m : S, L m)ᵒᵈ) := by
    change WellFoundedLT (∀ m : S, (L m)ᵒᵈ)
    infer_instance
  have : WellFoundedGT (Submodule R Q) := e.dual.wellFoundedLT
  have : IsNoetherian R Q := isNoetherian_iff.mpr inferInstance
  exact Module.length_ne_top.lt_top

end Module
