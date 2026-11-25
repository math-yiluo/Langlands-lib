/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Analytically unramified local rings and prime ideals

Source: Stacks Project, Algebra, Definition 032X
(blueprint: def-weil-pbc-analytically-unramified).

## Main definitions

* `IsAnalyticallyUnramified`: the maximal-ideal-adic completion is reduced.
* `Ideal.IsAnalyticallyUnramified`: the quotient by a prime ideal is analytically unramified.
-/

@[expose] public section

universe u

/-- (blueprint: def-weil-pbc-analytically-unramified) A Noetherian local ring is
analytically unramified when its maximal-ideal-adic completion has no nonzero nilpotents
(Stacks Project, Algebra, Definition 032X). -/
def IsAnalyticallyUnramified (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : Prop :=
  IsReduced (AdicCompletion (IsLocalRing.maximalIdeal R) R)

namespace Ideal

/-- (blueprint: def-weil-pbc-analytically-unramified) A prime ideal of a Noetherian local ring
is analytically unramified when the quotient local ring is analytically unramified. Its maximal
ideal is the image of the maximal ideal of the original ring (Stacks Project, Algebra,
Definition 032X). -/
def IsAnalyticallyUnramified {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : Ideal R) : Prop :=
  p.IsPrime ∧
    IsReduced (AdicCompletion ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk p))
      (R ⧸ p))

end Ideal
