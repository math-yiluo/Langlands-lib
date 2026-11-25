/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Artinian.Defs
import WeilConjectures.RingTheory.ArtinianSeparableResidueLiftCore
import WeilConjectures.RingTheory.ArtinianSeparableResidueLiftFlat

/-!
# Lifting a separable residue element across a flat map of Artinian local rings

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FI, finite étale case.
-/

@[expose] public section

set_option autoImplicit false
universe u v z

namespace Algebra

/-- A separable element of the target residue field can be captured by a finite étale
local Artinian extension of the source, with a flat local map to the target.
Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FI, the finite étale extension
and henselian factorization paragraphs; Algebra, Tags 06RS, 04GK, 04GG and 00MP.
(blueprint: lem-weil-pbc-artinian-separable-residue-lift).

Proof: Write F and K for the residue fields of D and S, and E = F(b) inside K. Since b
is separable, E/F is finite separable, hence finite étale. Artinian local rings are
Noetherian, have nilpotent maximal ideal and are henselian. The finite étale equivalence
for D lifts E to a finite étale D-algebra D'. Its reduction modulo m_D D' is the field E;
the ideal m_D D' is nilpotent, so D' is local with this maximal ideal, and is Artinian.
The map D → D' is local. Base change to S gives the étale S-algebra B = S ⊗[D] D'.
The inclusion E → K defines a surjective S-algebra map B → K. Its kernel is a prime over
m_S and has residue field K. Henselian étale retraction gives B → S with this kernel over
m_S. Restriction to D' gives g', factoring D → S and inducing E → K on residue fields.
It is local because D' has only one prime. Lift b ∈ E to d ∈ D' by the quotient
surjection; then residue_S(g'(d)) = b. Finally apply the Noetherian fibre flatness
criterion to D → D' → S and M = S. The fibre D'/m_D D' = E is a field, so the fibre module
is flat; S is flat over D by hypothesis. The criterion gives flatness of g'.
No assertion that a chosen lift of b itself lies in the image is made here: removing
its nilpotent error is a separate Frobenius argument. -/
theorem exists_finiteEtale_artinian_residue_lift
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (hflat : (algebraMap D S).Flat) (b : IsLocalRing.ResidueField S)
    (hb : IsSeparable (IsLocalRing.ResidueField D) b) :
    ∃ (D' : Type (max u v z)) (_ : CommRing D') (_ : Algebra D D') (g' : D' →+* S),
      IsLocalRing D' ∧ IsArtinianRing D' ∧
      IsLocalHom (algebraMap D D') ∧ IsLocalHom g' ∧
      Etale D D' ∧ Module.Finite D D' ∧ g'.Flat ∧
      g'.comp (algebraMap D D') = algebraMap D S ∧
      ∃ d : D', IsLocalRing.residue S (g' d) = b := by
  obtain ⟨D', hD', hDD', g', hlocal, hart, hmap, hg', het, hfin, hcomp, d, hd⟩ :=
    exists_finiteEtale_artinian_residue_lift_core D S b hb
  let : CommRing D' := hD'
  let : Algebra D D' := hDD'
  let : IsLocalRing D' := hlocal
  let : IsArtinianRing D' := hart
  let : IsLocalHom (algebraMap D D') := hmap
  let : IsLocalHom g' := hg'
  let : Etale D D' := het
  let : Module.Finite D D' := hfin
  have hflat' : g'.Flat :=
    flat_of_finiteEtale_artinian_residue_lift_core D S hflat D' g' hcomp
  exact ⟨D', hD', hDD', g', hlocal, hart, hmap, hg', het, hfin, hflat', hcomp, d, hd⟩

end Algebra
