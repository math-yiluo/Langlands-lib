/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Artinian.Defs
import WeilConjectures.RingTheory.ArtinianTranscendentalLocalizationProperties
import WeilConjectures.RingTheory.ArtinianTranscendentalLocalizationEvaluation

/-!
# The polynomial localization for a transcendental residue element

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FI, transcendental case.
-/

@[expose] public section

set_option autoImplicit false
universe u v z

namespace Algebra

/-- Localizing D[t] at the inverse image of the target maximal ideal gives an Artinian
local essentially smooth factorization when the residue of x is transcendental.
Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FI, transcendental case,
with flatness justified by Algebra, Tag 00MP.
(blueprint: lem-weil-pbc-artinian-transcendental-localization).

Proof: Let θ : D[t] → S evaluate t at x. The contracted prime P contains m_D[t] because
D → S is local. Modulo m_D[t], its map to the residue field K of S evaluates F[t] at the
residue α of x. Transcendence means that this evaluation is injective, so P = m_D[t].
Thus T = D[t]_P is Noetherian and local, and its maximal ideal equals m_D T and is
nilpotent, making T Artinian. The structure map D → T is local and essentially smooth,
since the polynomial algebra is smooth. Every polynomial outside P evaluates to a unit
of S, so the localization universal property extends θ to g' : T → S. This map is
local, factors D → S, and sends t/1 to x. Its flatness follows from the Noetherian fibre
criterion for D → T → S, M = S: S is flat over D, and T/m_D T = F(t) is a field, so the
fibre module is flat. The statement uses the canonical universe lift of T, preserving
all these properties.
This construction does not require θ to be injective. -/
theorem artinian_transcendental_polynomial_localization
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (hflat : (algebraMap D S).Flat) (x : S)
    (hx : Transcendental (IsLocalRing.ResidueField D) (IsLocalRing.residue S x)) :
    let P : Ideal (Polynomial D) :=
      (IsLocalRing.maximalIdeal S).comap (Polynomial.eval₂RingHom (algebraMap D S) x)
    letI : P.IsPrime := inferInstance
    let T := ULift.{max u v z} (Localization.AtPrime P)
    IsLocalRing T ∧ IsArtinianRing T ∧ IsLocalHom (algebraMap D T) ∧ EssentiallySmooth D T ∧
      ∃ g' : T →+* S, IsLocalHom g' ∧ g'.Flat ∧
        g'.comp (algebraMap D T) = algebraMap D S ∧ x ∈ Set.range g' := by
  dsimp
  have hs := localization_artinian_transcendental_properties D S hflat x hx
  have he := localization_transcendental_evaluation D S hflat x hx
  rcases hs with ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4, he⟩

end Algebra
