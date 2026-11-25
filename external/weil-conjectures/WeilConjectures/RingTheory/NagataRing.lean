/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Universally Japanese and Nagata rings

Source: Stacks Project, Algebra, Definition 10.162.1 (Tag 032R)
(blueprint: def-weil-pbc-nagata-ring).
-/

@[expose] public section

universe u

/-- A commutative ring is universally Japanese if every finite type algebra that is an
integral domain is N-2 (Stacks, Tag 032R) (blueprint: def-weil-pbc-nagata-ring). -/
def IsUniversallyJapanese (R : Type u) [CommRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.FiniteType R S], IsN2 S (FractionRing S)

/-- A commutative ring is Nagata if it is Noetherian and each quotient by a prime ideal
is N-2 (Stacks, Tag 032R) (blueprint: def-weil-pbc-nagata-ring). -/
def IsNagataRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (p : Ideal R) [p.IsPrime], IsN2 (R ⧸ p) (FractionRing (R ⧸ p))
