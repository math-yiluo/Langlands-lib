/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.Artinian.Module
import WeilConjectures.RingTheory.ArtinianSeparableResidueLiftCapture

@[expose] public section

set_option autoImplicit false
universe u v z

namespace Algebra

/-- Capture a separable residue element by a finite étale local Artinian extension.
Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FI; Algebra, Tags 06RS,
04GK and 04GG. Unlike the final lifting theorem, this construction needs no flatness.
(blueprint: lem-weil-pbc-artinian-separable-residue-lift-core).

Proof: Let F and K be the residue fields of D and S. The intermediate field E = F(b)
is finite separable over F because b is separable, hence is a finite étale F-algebra.
The Artinian local rings D and S have dimension zero and are henselian (Tag 06RS).
The finite étale equivalence (Tag 04GK) lifts E to a finite étale D-algebra D' together
with an identification D'/m_D D' = E. The ideal I = m_D D' is nilpotent, since m_D
is nilpotent. Every prime of D' contains I and corresponds to the unique prime of E.
Thus D' is local, its maximal ideal is I, and D → D' is local. Since D' is finite
as a module over an Artinian ring it is Artinian.
Put B = S ⊗[D] D'. Étale base change makes B étale over S. The inclusion E → K and
the residue map S → K give a surjective S-algebra map rho : B → K. Its kernel Q is
maximal, contracts to m_S, and B/Q = K, so its induced residue-field map is bijective.
Henselian étale retraction (Tag 04GG) gives an S-algebra map sigma : B → S whose
reduction has kernel Q. This reduction agrees with rho: the resulting S-algebra
endomorphism of K is the identity, since S → K is surjective. Restrict sigma to D'
to obtain g', which factors D → S and induces the inclusion E → K. The contraction
of m_S to D' is prime, and D' has only its maximal ideal as a prime, so g' is local.
Choose d mapping to b in D'/I = E by quotient surjectivity; then residue_S(g'(d)) = b.
Transport D' and the data through ULift to the requested ambient universe. This is
an existential theorem; no definition chooses an unspecified witness from its proof. -/
theorem exists_finiteEtale_artinian_residue_lift_core
    (D : Type u) (S : Type v) [CommRing D] [CommRing S]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    [Algebra D S] [IsLocalHom (algebraMap D S)]
    (b : IsLocalRing.ResidueField S)
    (hb : IsSeparable (IsLocalRing.ResidueField D) b) :
    ∃ (D' : Type (max u v z)) (_ : CommRing D') (_ : Algebra D D') (g' : D' →+* S),
      IsLocalRing D' ∧ IsArtinianRing D' ∧
      IsLocalHom (algebraMap D D') ∧ IsLocalHom g' ∧
      Etale D D' ∧ Module.Finite D D' ∧
      g'.comp (algebraMap D D') = algebraMap D S ∧
      ∃ d : D', IsLocalRing.residue S (g' d) = b := by
  obtain ⟨D', hD', hDD', g', hlocal, hmap, hg', het, hfin, hcomp, d, hd⟩ :=
    exists_finiteEtale_artinian_residue_lift_capture D S b hb
  let : CommRing D' := hD'
  let : Algebra D D' := hDD'
  let : IsLocalRing D' := hlocal
  let : IsLocalHom (algebraMap D D') := hmap
  let : IsLocalHom g' := hg'
  let : Etale D D' := het
  let : Module.Finite D D' := hfin
  have hart : IsArtinianRing D' := IsArtinianRing.of_finite D D'
  exact ⟨D', hD', hDD', g', hlocal, hart, hmap, hg', het, hfin, hcomp, d, hd⟩

end Algebra
