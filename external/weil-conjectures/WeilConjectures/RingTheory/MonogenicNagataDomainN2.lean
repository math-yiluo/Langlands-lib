/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.AlgebraicMonogenicNagataDomainN2
import WeilConjectures.RingTheory.NagataDomainN2
import WeilConjectures.RingTheory.PolynomialRingN2
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Monogenic extensions of Nagata domains are Japanese

Source: Stacks Project, Algebra, Proposition Tag 0334, claim (*) and Steps 3--4
(blueprint: lem-weil-pbc-monogenic-nagata-domain-n2).
-/

@[expose] public section

universe u

/-- An injective monogenic extension of Nagata domains is N-2.

Source: Stacks Project, Algebra, Proposition Tag 0334, claim (*) and Steps 3--4
(blueprint: lem-weil-pbc-monogenic-nagata-domain-n2).

Proof: Write `K = Frac(A)` and `L = Frac(B)` and view `K` inside `L` using
injectivity. If `x` is transcendental over `K`, evaluation identifies `B` with
`A[X]`. The zero prime in the Nagata definition makes `A` N-2, and Tag 032O makes
`A[X]` N-2. Otherwise `L = K(x)` is finite over `K`. For an arbitrary finite field
extension `M/L`, the tower law makes `M/K` finite. The integral closure `A'` of `A`
in `M` is finite over `A` by N-2, normal with fraction field `M`, and Nagata by
Tag 032T. Put `T = A'[x]` inside `M`. Module generators of `A'` over `A` generate
`T` over `B`, so `T/B` is finite. Its fraction field is `M` since it contains `A'`.
Integrality transitivity identifies the integral closure of `B` in `M` with the
integral closure of `T` in `M`. Claim (***) of Tag 0334, namely normalization
finiteness for a monogenic subalgebra of the fraction field of a normal Nagata
domain, makes this closure finite over `T`. Finiteness transitivity makes it finite
over `B`. This proves N-2 for every finite extension `M/L`.

The cases `x = 0` and `x` in the image of `A` fall in the algebraic case, where
`B` equals the image of `A`; no nonzero or transcendence hypothesis is required. -/
theorem isN2_of_monogenic_nagata_domain (A B : Type u) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] (hA : IsNagataRing A)
    (hinj : Function.Injective (algebraMap A B)) (x : B)
    (hgen : Algebra.adjoin A ({x} : Set B) = ⊤) : IsN2 B (FractionRing B) := by
  classical
  by_cases hx : IsAlgebraic A x
  · exact isN2_of_algebraic_monogenic_nagata_domain A B hA hinj x hgen hx
  · have hi : Function.Injective (Polynomial.aeval x : Polynomial A →ₐ[A] B) :=
      transcendental_iff_injective.mp hx
    have hs : Function.Surjective (Polynomial.aeval x : Polynomial A →ₐ[A] B) := by
      rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
      exact hgen
    have hpoly : IsN2 (Polynomial A) (FractionRing (Polynomial A)) := by
      let : IsNoetherianRing A := hA.1
      exact isN2_polynomial A (isN2_of_isNagataRing_domain A hA)
    let : Algebra (Polynomial A) B := (Polynomial.aeval x).toRingHom.toAlgebra
    let : Module.Finite (Polynomial A) B :=
      Module.Finite.of_surjective (Algebra.linearMap _ _) hs
    let : IsNoetherianRing A := hA.1
    exact isN2_of_finite_domain_extension (Polynomial A) B
      (FractionRing (Polynomial A)) (FractionRing B) hi hpoly

