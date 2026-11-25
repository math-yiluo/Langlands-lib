/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RegularLocalOfFormallySmoothAdic

/-!
# Smooth algebras over fields have regular local rings

Source: Stacks Project, Algebra, Lemma Tag 00TT (blueprint:
lem-weil-pbc-smooth-over-field-regular-local).
-/

@[expose] public section

universe u v

namespace Algebra

/-- If `A` is a smooth algebra over a field, every localization at a prime ideal
is a regular local ring (blueprint: lem-weil-pbc-smooth-over-field-regular-local).

Source: Stacks Project, Algebra, Lemma Tag 00TT, final assertion.
Proof:
1. Smoothness gives finite type, so `A` is Noetherian. Localization makes `A_q`
   Noetherian and local.
2. Smoothness gives formal smoothness over `k`, which is preserved by localization.
   Its square-zero lifting property applies to every algebra map, hence in particular
   to the maps killing a power of the maximal ideal. Thus `A_q` is formally smooth
   for the maximal-ideal-adic topology.
3. Apply Stacks Project, More on Algebra, Lemma Tag 07EI, as stated in
   `Algebra.isRegularLocalRing_of_formallySmoothAdic`. This is a generic local-algebra
   regularity criterion; no dimension or residue-field comparison is necessary.
-/
theorem smooth_over_field_regular_local
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  apply isRegularLocalRing_of_formallySmoothAdic k (Localization.AtPrime q)
  intro D _ _ J hJ g _
  exact FormallySmooth.comp_surjective k (Localization.AtPrime q) J hJ g

end Algebra
