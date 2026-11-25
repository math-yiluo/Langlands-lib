/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.SmoothNormalRing

/-!
# Normality ascends along etale ring maps

Source: Stacks Project, Algebra, Lemma Tag 033C, applied as in More on Algebra,
Lemma Tag 06DI (blueprint: lem-weil-pbc-etale-over-normal-ring-normal).

A normal ring (`def-weil-pbc-normal-ring`, Stacks Tags 0309 and 00GV) is written out
as in the landed `CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit`:
every localization at a prime ideal is an integrally closed domain.
-/

@[expose] public section

universe uA uB

namespace RingHom

/-- An etale algebra over a normal ring is normal: if `f : A →+* B` is etale and every
localization of `A` at a prime is an integrally closed domain, then so is every
localization of `B` at a prime.
Source: Stacks Project, Algebra, Tag 033C; More on Algebra, proof of Tag 06DI
(blueprint: lem-weil-pbc-etale-over-normal-ring-normal).

Proof:
1. The morphism of affine schemes induced by the ring map is etale
   (`def-weil-etale-morphism`), hence smooth by
   `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`, in the sense of
   `def-sbc-smooth-morphisms`.
2. By `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`, the ring map is smooth in
   the sense of `def-weil-pbc-smooth-ring-map`.
3. Apply `lem-weil-pbc-smooth-over-normal-ring-normal` (Stacks Tag 033C) to the smooth
   ring map and the normal base ring (`def-weil-pbc-normal-ring`). This gives normality
   of the target ring. The affine etale equivalence is Stacks Tag 02GJ (2). -/
theorem Etale.isNormalRing {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.Etale)
    (hA : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal B) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  exact ((etale_iff_formallyUnramified_and_smooth f).mp hf).2.isNormalRing hA

end RingHom
