/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.DimensionAtPointComponents

/-!
# Dimension at a closed point of an affine scheme over a field

Source: Stacks Project, Algebra, Lemma 00OU, a specialization of Lemma 00OT
(blueprint: lem-weil-pbc-closed-point-dimension-local-ring).
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Lemma 00OU (using the proof of Lemma 00OT).
(blueprint: lem-weil-pbc-closed-point-dimension-local-ring).
The local topological dimension of the spectrum of a finitely generated algebra over a field,
at a maximal ideal, equals the Krull dimension of the localization at that ideal.

Proof:
1. A field is Noetherian (`def-weil-pbc-noetherian-ring`), hence so is its finite type algebra
   (`lem-weil-pbc-finite-type-algebra-noetherian`). Thus there are finitely many minimal primes
   (`lem-weil-pbc-noetherian-finitely-many-minimal-primes`).
2. Every open neighbourhood of the maximal ideal contains every prime below it, since the
   maximal ideal is in the closure of that prime
   (`lem-weil-pbc-spec-irreducible-closed-subsets-primes`).
3. A chain of primes below the maximal ideal gives a reversed chain of irreducible closed
   subsets in every such neighbourhood by taking closures of the points there
   (`lem-weil-pbc-irreducible-closure`, `lem-weil-pbc-spec-irreducible-closed-subsets-primes`).
   The inclusions stay strict because the corresponding prime points distinguish them.
   Taking suprema gives the lower bound by the dimension of the localization
   (`lem-weil-pbc-localization-dimension-chains-below-prime`).
4. Remove the finitely many components corresponding to minimal primes not below the maximal
   ideal. Their union is closed, so its complement is an open neighbourhood of the point.
5. Closing a chain of irreducible closed subsets of this neighbourhood in the whole spectrum
   preserves strictness. The resulting chain of primes contains a minimal prime q
   (`lem-weil-pbc-prime-contains-minimal-prime`), which must lie below the maximal ideal,
   since its component meets this neighbourhood. In the finite type domain S/q, the chain
   length is bounded by dim(S/q), which equals the dimension at its induced maximal ideal
   (`lem-weil-pbc-finite-type-domain-dimension-local-ring`). Chains below this induced ideal
   lift to chains below the original maximal ideal, bounding that local ring dimension by
   dim(S_m) (`lem-weil-pbc-localization-dimension-chains-below-prime`). This gives the upper bound.
6. The infimum defining the local topological dimension
   (`def-kun-topological-dimension-at-point`) is at least dim(S_m) by step 3, and at most it
   by the neighbourhood in steps 4 and 5. Therefore the two dimensions are equal. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    (hfg : ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] S), Function.Surjective f)
    (m : Ideal S) [m.IsMaximal] :
    topologicalKrullDimAt (⟨m, inferInstance⟩ : Spec (CommRingCat.of S)) =
      ringKrullDim (Localization.AtPrime m) := by
  have : Algebra.FiniteType k S := Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr hfg
  obtain ⟨qs, hqs, hne, n, hdim, hcomponents, hattained, hquotients, hquotient,
    hlower, m', hm', hle, hlocal⟩ := dimension_at_point_components (k := k) m
  have hmax : m = m' := Ideal.IsMaximal.eq_of_le inferInstance hm'.ne_top hle
  subst m'
  exact hdim.trans hlocal.symm

end AlgebraicGeometry
