/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
import WeilConjectures.RingTheory.SmoothAtPrimeOfDifferentialsDimensionBound
import WeilConjectures.RingTheory.RegularLocalFibreFinrank

/-!
# Regularity with separable residue field characterizes smoothness over a field

Source: Stacks Project, Algebra, Lemma Tag 00TV (lemma-separable-smooth, line 38740)
(blueprint: lem-weil-pbc-regular-local-separable-residue-smooth).
-/

@[expose] public section

universe u v

namespace Algebra

/-- For a finite type algebra over a field, smoothness at a prime is equivalent to
regularity of the local ring when the residue field is separable over the base.
Source: Stacks Project, Algebra, Lemma Tag 00TV (lemma-separable-smooth, line 38740)
(blueprint: lem-weil-pbc-regular-local-separable-residue-smooth).
Proof steps (from the cited Stacks proof) are: (1) localize at `q`, observe that the
result is Noetherian local and that its residue field is finitely generated and
separable over `k`; (2) apply the Jacobi--Zariski sequence and injectivity for a
separable residue field to obtain a short exact cotangent sequence; (3) compute its
dimension using the regular-local cotangent criterion and the transcendence-degree
formula for separably generated fields; (4) identify differentials after localization
and tensoring with the residue field; (5) compare this dimension with the dimension
of `Spec S` at `q`, with equality exactly when the local ring is regular; (6) use the
dimension criterion for smoothness to deduce smoothness from regularity; and (7) use
the converse smoothness dimension criterion to deduce regularity. These steps use the
dependency nodes `lem-weil-pbc-jacobi-zariski-differential-maps`,
`lem-weil-pbc-separable-residue-cotangent-injective`,
`lem-weil-pbc-regular-local-cotangent-dimension`,
`lem-weil-pbc-separably-generated-differentials-dimension`,
`lem-weil-pbc-kahler-differentials-localization`,
`lem-weil-pbc-dimension-at-point-local-ring-trdeg`,
`lem-weil-pbc-differentials-dimension-bound-smooth-at-prime`, and
`lem-weil-pbc-smooth-over-field-dimension-differentials` (along with the cited
localization, separability, and regular-local definitions).
-/
theorem regularLocal_iff_smoothAtPrime
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hsep : Algebra.IsSeparableExtension k q.ResidueField) :
    Algebra.IsSmoothAtPrime k ⟨q, inferInstance⟩ ↔
      IsRegularLocalRing (Localization.AtPrime q) := by
  let q' : PrimeSpectrum S := ⟨q, inferInstance⟩
  rw [regularLocal_iff_fibre_finrank_eq_dimension k S q hsep]
  constructor
  · intro hsm
    exact (finiteDimensional_and_finrank_kaehlerDifferential_eq_of_isSmoothAtPrime q' hsm).2
  · intro heq
    exact isSmoothAtPrime_of_finrank_kaehlerDifferential_le q' heq.le

end Algebra
