/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.FiniteType

/-!
# Quasi-finiteness of a ring map at a prime

Source: Stacks Project, Algebra, Definition 10.122.3 (Tag 00PL), using condition (1) of
Lemma 10.122.2 (Tag 00PK) (blueprint: def-weil-pbc-ring-map-quasi-finite-at-prime).
-/

@[expose] public section

universe u v

namespace Algebra

/-- (blueprint: def-weil-pbc-ring-map-quasi-finite-at-prime) For a finite-type map of
commutative rings `R → S`, quasi-finiteness at a prime `q` means that the prime of the
fibre ring `κ(p) ⊗[R] S` corresponding to `q`, where `p` is the contraction of `q`,
is an isolated point of its spectrum (Stacks, Tags 00PL and 00PK).

The fibre prime is supplied canonically by `PrimeSpectrum.preimageHomeomorphFiber`;
its source point lies over `p` by the definition of `p`. The singleton is open in
the Zariski topology of the fibre spectrum. -/
def IsQuasiFiniteAtPrime (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (q : PrimeSpectrum S) : Prop :=
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  IsOpen ({e ⟨q, rfl⟩} : Set (PrimeSpectrum (p.asIdeal.Fiber S)))

end Algebra
