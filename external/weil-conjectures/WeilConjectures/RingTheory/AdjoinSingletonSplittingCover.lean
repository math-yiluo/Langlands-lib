/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import WeilConjectures.RingTheory.AdjoinSingletonSplittingPolynomialCover
import Mathlib.RingTheory.Ideal.Operations

/-! # Splitting cover before constructing the normal principal open
Source: Stacks Project, Algebra, Tag 0334, Step 5. -/

@[expose] public section

universe u v

/-- The splitting construction supplies one normal Nagata coefficient ring and a localized
fractional monogenic algebra, finite over the original maximal localization. Its maximal
ideals contract to maximal ideals containing z-r for a coefficient r in that ring.
Source: Stacks Project, Algebra, Tag 0334, Step 5, residue-polynomial splitting reduction.
(blueprint: lem-weil-pbc-monogenic-splitting-cover).

Proof: Contract m to R. The residue of x is algebraic over the fraction field of R/(m ∩ R)
by Zariski's lemma. Lift its monic minimal polynomial, clearing all coefficient denominators
by a product s outside m ∩ R. Over R_s its evaluation at x belongs to mS_s. Take a finite
splitting extension L of K, and let R' be the integral closure of R_s in L. Localization
preserves Nagata rings, and the N-2 clause makes R' finite over R_s. Thus R' is normal and
Nagata, and L is its fraction field. Set z to the image of x and T = R'[z]. The finite module
generators of R' over R_s also generate T over S_s. Let M be the image in T of S minus m,
and put B = Localization M. The denominator s is already a unit in S_m, so localization
of that finite extension makes B finite over S_m. All maps embed in L, so M contains no
zero and the map S_m to B is injective. A maximal q of B contracts to a maximal n0 of T:
B is integral over the local ring S_m, so q contracts to its unique maximal ideal; n0 lies
over the maximal ideal of S_s and is maximal by integrality of T over S_s. The lifted monic
polynomial evaluates into n0 and splits into linear factors with roots in R'. Its positive
degree and primality of n0 imply z-r belongs to n0 for one root r. The conclusion records
this root r and the maximality of n0. Use universe lifts
of R_s and L as needed to place both coefficient rings in Type(max u v).
No normal principal open of B is asserted here; that follows separately by clearing a
denominator of z over R'. -/
theorem exists_adjoin_singleton_splitting_cover
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : IsNagataRing R) (x : K)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal] :
    ∃ (R' K' : Type (max u v)) (_ : CommRing R') (_ : IsDomain R')
      (_ : IsIntegrallyClosed R') (_ : Field K') (_ : Algebra R' K')
      (_ : IsFractionRing R' K'),
      IsNagataRing R' ∧ ∃ (z : K') (M : Submonoid (Algebra.adjoin R' ({z} : Set K'))),
        M ≤ nonZeroDivisors (Algebra.adjoin R' ({z} : Set K')) ∧
        ∃ (_ : Algebra (Localization.AtPrime m) (Localization M)),
          Function.Injective (algebraMap (Localization.AtPrime m) (Localization M)) ∧
          Module.Finite (Localization.AtPrime m) (Localization M) ∧
          ∀ (q : Ideal (Localization M)) [q.IsMaximal],
            (q.comap (algebraMap (Algebra.adjoin R' ({z} : Set K'))
              (Localization M))).IsMaximal ∧
            ∃ r : R',
              (⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩ :
                Algebra.adjoin R' ({z} : Set K')) -
                algebraMap R' (Algebra.adjoin R' ({z} : Set K')) r ∈
                q.comap (algebraMap (Algebra.adjoin R' ({z} : Set K'))
                  (Localization M)) := by
  obtain ⟨R', K', hCR, hDom, hNorm, hField, hAlg, hFrac, hNag, z, M, hM,
      hA, hinj, hfin, d, roots, hd, hpoly⟩ :=
    exists_adjoin_singleton_splitting_polynomial_cover R K hR x m
  let : CommRing R' := hCR
  let : IsDomain R' := hDom
  let : IsIntegrallyClosed R' := hNorm
  let : Field K' := hField
  let : Algebra R' K' := hAlg
  let : IsFractionRing R' K' := hFrac
  refine ⟨R', K', hCR, hDom, hNorm, hField, hAlg, hFrac, hNag, z, M, hM, hA,
    hinj, hfin, ?_⟩
  intro q hq
  obtain ⟨hmax, hprod⟩ := hpoly q
  refine ⟨hmax, ?_⟩
  have : (q.comap (algebraMap (Algebra.adjoin R' ({z} : Set K'))
    (Localization M))).IsPrime := hmax.isPrime
  obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
  exact ⟨roots i, hi⟩
