/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Finite products of normal rings

Source: Stacks Project, Algebra, Lemma Tag 0CYA
(blueprint: lem-weil-pbc-finite-product-normal).

Normality is the prime-localization condition of `def-weil-pbc-normal-ring`, expressed
using its Mathlib match `IsDomain`, `IsIntegrallyClosed`, and `Localization.AtPrime`.
-/

@[expose] public section

universe u v

namespace Pi

/-- A finite product of commutative normal rings is normal.
Source: Stacks Project, Algebra, Lemma Tag 0CYA
(blueprint: lem-weil-pbc-finite-product-normal).

Proof:
1. Given a prime ideal of the finite product, `lem-weil-pbc-product-prime-factor`
   supplies an index and a prime of that factor whose inverse image is the given prime.
   In particular the empty product has no prime ideals, so its normality is vacuous.
2. By `lem-weil-pbc-product-prime-localization`, projection onto this factor induces
   an isomorphism from the product's prime localization to the factor's prime localization.
   The latter is an integrally closed domain by the hypothesis and
   `def-weil-pbc-normal-ring` (Stacks Tags 0309 and 00GV).
3. Transport normal-domain structure across this isomorphism using
   `lem-weil-pbc-normal-domain-ring-equivalence`. Since the prime was arbitrary,
   the product satisfies `def-weil-pbc-normal-ring`. -/
theorem isNormalRing_of_finite {I : Type u} [Finite I] (R : I → Type v)
    [∀ i : I, CommRing (R i)]
    (hR : ∀ (i : I) (p : Ideal (R i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal (∀ i : I, R i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  intro p hp
  obtain ⟨i, q, hq⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq (⟨p, hp⟩ : PrimeSpectrum (∀ i, R i))
  have hpq : q.asIdeal.comap (Pi.evalRingHom R i) = p :=
    congrArg PrimeSpectrum.asIdeal hq
  subst p
  obtain ⟨hd, hc⟩ := hR i q.asIdeal
  let e := RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
    (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
  exact ⟨e.toMulEquiv.isDomain_iff.mpr hd, IsIntegrallyClosed.of_equiv e.symm⟩

end Pi
