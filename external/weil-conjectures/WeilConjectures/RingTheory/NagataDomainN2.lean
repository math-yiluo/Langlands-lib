/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension

/-!
# A Nagata domain is Japanese

Source: Stacks Project, Algebra, Definition Tag 032R and Proposition Tag 0334,
implication (2) to (3), applied to the zero prime
(blueprint: lem-weil-pbc-nagata-domain-n2).
-/

@[expose] public section

universe u

/-- A Nagata domain is N-2.

Source: Stacks Project, Algebra, Definition Tag 032R and Proposition Tag 0334,
implication (2) to (3) (blueprint: lem-weil-pbc-nagata-domain-n2).

Proof: The zero ideal is prime. The Nagata hypothesis makes its quotient N-2.
The quotient is isomorphic to the original domain. Regard that isomorphism as
an injective finite algebra map and apply ascent of N-2 along a finite domain
extension (Tag 032I). Noetherianity comes from the Nagata hypothesis. -/
theorem isN2_of_isNagataRing_domain (S : Type u) [CommRing S] [IsDomain S]
    (hS : IsNagataRing S) : IsN2 S (FractionRing S) := by
  let e := RingEquiv.quotientBot S
  let : Algebra (S ⧸ (⊥ : Ideal S)) S := e.toRingHom.toAlgebra
  let : Module.Finite (S ⧸ (⊥ : Ideal S)) S :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) e.surjective
  let : IsNoetherianRing S := hS.1
  let : IsNoetherianRing (S ⧸ (⊥ : Ideal S)) :=
    isNoetherianRing_of_ringEquiv S e.symm
  exact isN2_of_finite_domain_extension (S ⧸ (⊥ : Ideal S)) S
    (FractionRing (S ⧸ (⊥ : Ideal S))) (FractionRing S) e.injective (hS.2 ⊥)

