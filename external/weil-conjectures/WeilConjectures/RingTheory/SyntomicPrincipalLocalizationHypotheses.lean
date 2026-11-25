/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.SyntomicPrincipalLocalizationFibreTransport

/-!
# Syntomic hypotheses after principal localization

Source: Stacks Project, Algebra, Tag 00SY, first sentence of (3) ⇒ (2).
(blueprint: lem-weil-pbc-syntomic-principal-localization-hypotheses).
-/

@[expose] public section

universe u v
namespace Algebra

/-- Principal localization outside the prime preserves the complete-intersection fibre hypothesis.
Source: Stacks Project, Algebra, Tag 00SY, first sentence of (3) ⇒ (2), and Tag 00SA.
(blueprint: lem-weil-pbc-syntomic-principal-localization-hypotheses).

Proof: extend q to S_g; its contraction is q because no power of g lies in q. The local rings
S_q and (S_g)_{qS_g} and their residue fields are canonically isomorphic. The induced base
prime is unchanged. Tensoring S_g with the residue field of the base identifies its fibre with the
localization of the old fibre at 1 tensor g. Its canonical prime contracts to the old canonical
prime, since the maps to the residue fields commute. If h is the element in the fibre
hypothesis, its image remains outside the extended prime. Localizing this new fibre at h
is the localization of F_h at the image of 1 tensor g. This is a global complete intersection
by principal-localization stability (00SA); transport along the canonical algebra
isomorphisms proves the required fibre hypothesis. -/
theorem exists_completeIntersection_fibre_away
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (g : S) (hg : g ∉ q.asIdeal)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ q₁ : PrimeSpectrum (Localization.Away g),
      q₁.comap (algebraMap S (Localization.Away g)) = q ∧
      ∃ h : (q₁.asIdeal.comap (algebraMap R (Localization.Away g))).Fiber
          (Localization.Away g),
        h ∉ (PrimeSpectrum.preimageEquivFiber R (Localization.Away g)
          (q₁.comap (algebraMap R (Localization.Away g))) ⟨q₁, rfl⟩).asIdeal ∧
        IsGlobalCompleteIntersection
          (q₁.asIdeal.comap (algebraMap R (Localization.Away g))).ResidueField
          (Localization.Away h) := by
  have hq : q ∈ Set.range (PrimeSpectrum.comap
      (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact hg
  obtain ⟨q₁, hq₁⟩ := hq
  refine ⟨q₁, hq₁, ?_⟩
  exact exists_completeIntersection_fibre_transport q g hg q₁ hq₁ hci

end Algebra
