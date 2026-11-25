/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import WeilConjectures.RingTheory.RegularRingEquiv

/-!
# Transporting the G-ring property through a ring isomorphism

Source: Stacks Project, More on Algebra, Definition 07GH and the quotient
presentation in the first paragraph of Proposition 07PV.
(blueprint: lem-weil-pbc-g-ring-ring-equiv).
-/

@[expose] public section

universe u v

/-- The G-ring property is invariant under ring isomorphism.
Source: Stacks Project, More on Algebra, Definition 07GH; Proposition 07PV uses
this invariance when replacing a finite type algebra by a polynomial quotient.
(blueprint: lem-weil-pbc-g-ring-ring-equiv).

Proof: Transport Noetherianity through e. For a prime p of S, put q = e⁻¹(p).
The isomorphism e sends the prime complement of q onto that of p, so its maps
and inverse extend by the universal property of localization to inverse ring
maps R_q ≃ S_p. This local ring isomorphism identifies maximal ideals and all
their powers. On each quotient it therefore induces inverse ring maps, and
on their inverse limits inverse ring maps between the two adic completions.
These commute with the canonical completion maps because their components
on every quotient do. Flatness of the completion map of R_q transports along
these source and target isomorphisms. At each prime of S_p, the isomorphisms
identify its residue field and fibre with the corresponding residue field
and fibre for R_q. Noetherianity of the fibres transports, and after any finite
purely inseparable extension, the induced tensor-product isomorphisms transport
regularity of all prime localizations. Thus every fibre is geometrically regular.
If the universes differ, first lift the fields and algebras to a common universe;
finite purely inseparable extensions can be represented in the original field's
universe using their finite vector-space dimension. The resulting criterion is
independent of the lift. Hence each completion map of S_p is regular, and S is
a G-ring by Definition 07GH. -/
theorem isGRing_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (hR : IsGRing R) : IsGRing S := by
  let : IsNoetherianRing R := hR.1
  refine ⟨isNoetherianRing_of_ringEquiv R e, ?_⟩
  intro p hp
  let q : Ideal R := p.comap e.toRingHom
  let : q.IsPrime := Ideal.comap_isPrime e.toRingHom p
  let a : Localization.AtPrime q ≃+* Localization.AtPrime p :=
    Localization.localRingEquiv q p e rfl
  obtain ⟨b, hb⟩ := AdicCompletion.exists_ringEquiv
    (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)) a
    (IsLocalRing.map_ringEquiv_maximalIdeal a).symm
  exact RingHom.IsRegular.of_ringEquiv _ _ a b hb (hR.2 q)
