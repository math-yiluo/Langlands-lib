/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Finite ring maps are quasi-finite at every prime

Source: Stacks Project, Algebra, Tags 00PM and 0H8X
(blueprint: lem-weil-pbc-finite-ring-map-quasi-finite).
-/

@[expose] public section

universe u v

namespace Algebra

/-- (blueprint: lem-weil-pbc-finite-ring-map-quasi-finite) A finite map of commutative
rings is of finite type and quasi-finite at every prime, in the isolated-fibre-point sense
of Stacks Project, Algebra, Tags 00PL, 00PM and 0H8X.

Proof:
1. Choose finitely many module generators (`def-weil-finitely-generated-module`). The
   subalgebra they generate contains all their linear combinations, hence the whole
   target. This gives finite type (`def-weil-pbc-finite-type-algebra`); an empty list
   covers the zero ring.
2. For a prime p of R, base change the generators to the residue field k of p. Every
   pure tensor is a k-linear combination of their images, so the fibre ring is finite
   over k (`def-weil-pbc-ring-map-quasi-finite-at-prime`).
3. The field k is local with only the zero prime. Apply
   `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum` to the finite k-algebra:
   its spectrum is finite and discrete, so each point is open. This also covers an
   empty spectrum, when the fibre ring is zero.
4. For any prime q of T, let p be its contraction. By
   `lem-weil-pbc-fibre-ring-primes-bijection`, q corresponds to a unique prime of the
   fibre over p. Step 3 makes its singleton open. Together with step 1 this is exactly
   `def-weil-pbc-ring-map-quasi-finite-at-prime`, for every q.

The finite-type witness in the conclusion supplies the instance required by the
recorded quasi-finiteness definition. -/
theorem finiteType_and_isQuasiFiniteAtPrime_of_finite
    (R : Type u) (T : Type v) [CommRing R] [CommRing T] [Algebra R T]
    [Module.Finite R T] :
    ∃ hft : Algebra.FiniteType R T,
      letI := hft
      ∀ q : PrimeSpectrum T, Algebra.IsQuasiFiniteAtPrime R T q := by
  refine ⟨inferInstance, ?_⟩
  intro q
  unfold IsQuasiFiniteAtPrime
  exact isOpen_discrete _

end Algebra
