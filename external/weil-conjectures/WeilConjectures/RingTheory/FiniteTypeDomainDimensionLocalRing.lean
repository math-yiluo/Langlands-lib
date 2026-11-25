/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.RelSeries
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingLocalization
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingChains

/-!
# Dimension of local rings of finite type domains over fields

Source: Stacks Project, Algebra, Lemma Tag 00OS (label lemma-dimension-spell-it-out,
line 27763) (blueprint: lem-weil-pbc-finite-type-domain-dimension-local-ring).
-/

@[expose] public section

universe u v

/-- A finite type domain over a field has the dimension of each of its local rings at
maximal ideals, and all maximal prime chains have this common finite length.

Source: Stacks Project, Algebra, Lemma Tag 00OS (label lemma-dimension-spell-it-out,
line 27763) (blueprint: lem-weil-pbc-finite-type-domain-dimension-local-ring).

Proof, following the six steps of the blueprint:
1. By `def-weil-pbc-finite-type-algebra`, choose a surjection from
   P = k[x₁, ..., xₙ] (`def-weil-pbc-mv-polynomial-ring`) to S with prime kernel a.
   Ideal correspondence identifies primes and maximal ideals of S with those of P
   containing a, preserving strict inclusion. Since S is a domain, (0) is prime.
2. Every prime chain in P ends below a maximal ideal by
   `lem-weil-pbc-proper-ideal-contained-in-maximal`. Its length is bounded by the
   dimension of that localization by `lem-weil-pbc-localization-dimension-chains-below-prime`.
   This dimension is n by `lem-weil-pbc-polynomial-ring-maximal-localization-dimension`.
   Thus all prime chains in S have length at most n, and 0 ≤ dim S ≤ n.
3. The same localization-chain correspondence shows that each maximal ideal M of P
   has height n. The height of a is a finite integer at most n, as in
   `lem-weil-pbc-polynomial-ring-maximal-chain-height-difference`.
4. For a maximal ideal m of S, the bounded supremum of lengths of chains below m
   is attained. A longest chain starts at (0), ends at m, and admits no insertion.
   Its preimage is a saturated chain from a to the maximal ideal M above m.
   By `lem-weil-pbc-polynomial-ring-maximal-chain-height-difference`, its length is
   height M - height a = n - height a. By
   `lem-weil-pbc-localization-dimension-chains-below-prime`, this is dim S_m,
   using `def-weil-pbc-localization-at-prime` and `def-weil-pbc-krull-dimension-ring`.
5. S is nonzero, hence has a maximal ideal by
   `lem-weil-pbc-proper-ideal-contained-in-maximal`, and step 4 supplies a chain of
   length n - height a. Conversely every chain ends below some maximal ideal and
   has length at most its localization dimension. Hence dim S = n - height a,
   a nonnegative integer equal to dim S_m for every maximal m.
6. Any maximal prime chain in S starts at (0), ends at a maximal ideal, and is
   saturated. Its preimage in P has length n - height a by
   `lem-weil-pbc-polynomial-ring-maximal-chain-height-difference`, hence length dim S.
   Conversely the longest chain below each maximal m in step 4 is maximal in S;
   the common-length formulation therefore gives dim S_m = dim S.

`LTSeries` counts strict inclusions, and `IsMaxChain` of its range means precisely
that no prime can be inserted before, between, or after its entries.
-/
theorem finiteTypeDomain_ringKrullDim_localizationAtMaximal
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S] :
    (∀ (m : Ideal S) [m.IsMaximal],
      ringKrullDim (Localization.AtPrime m) = ringKrullDim S) ∧
    (∃ (d : ℕ), ringKrullDim S = (d : WithBot ℕ∞) ∧
      ∀ (p : LTSeries (PrimeSpectrum S)),
        IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r) (Set.range p) →
          p.length = d) := by
  exact ⟨finiteTypeDomain_ringKrullDim_localizationAtMaximal_localization (k := k) (S := S),
    finiteTypeDomain_ringKrullDim_localizationAtMaximal_chains (k := k) (S := S)⟩
