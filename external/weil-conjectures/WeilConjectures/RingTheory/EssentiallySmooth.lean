/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic

/-!
# Essentially smooth ring maps

Source: Stacks Project, Smoothing Ring Maps, Section 07FF, where the term is used in
Lemmas 07FH and 07FI; modelled on Algebra, Definition 00QM
(blueprint: def-weil-pbc-essentially-smooth-ring-map).
-/

@[expose] public section

universe u v

namespace Algebra

/-- (blueprint: def-weil-pbc-essentially-smooth-ring-map) A commutative `R`-algebra `D` is
essentially smooth when it is isomorphic, as an `R`-algebra, to the localization of a smooth
`R`-algebra `P` at a multiplicative subset. Stacks Project, Smoothing Ring Maps, Section 07FF;
compare Algebra, Definition 00QM.

The node's first step uses the usual fraction operations: `Localization S` is a commutative
ring, and the composite `R → P → Localization S` gives its `R`-algebra structure. Thus the
condition depends only on the `R`-algebra isomorphism class of `D`.

For remark (a), if `R → D` is smooth, take `P = D` and `S = {1}`. The canonical map to this
localization is an `R`-algebra isomorphism. An étale map of affine schemes gives an étale ring
map by `lem-weil-pbc-etale-ring-map-iff-etale-affine`. Its cotangent homology and differentials
vanish, so it is smooth by `def-weil-pbc-smooth-ring-map`, hence essentially smooth.

For remark (b), if `D` is local with maximal ideal `m`, contract `m` along `P → D` to a prime
`p`. Every element outside `p` maps to a unit of `D`, and `S` lies outside `p`. The fraction
map from `P` localized outside `p` to `D` is therefore defined, surjective because `D` is
already a localization at `S`, and injective by the fraction equality rule. This identifies
`D` with `Localization.AtPrime p` as an `R`-algebra. These remarks are consequences, not
conditions of the definition. -/
def EssentiallySmooth (R : Type u) (D : Type v) [CommRing R] [CommRing D] [Algebra R D] :
    Prop :=
  ∃ (P : Type (max u v)) (hP : CommRing P),
    letI : CommRing P := hP
    ∃ (hRP : Algebra R P),
      letI : Algebra R P := hRP
      Smooth R P ∧ ∃ (S : Submonoid P), Nonempty (D ≃ₐ[R] Localization S)

end Algebra
