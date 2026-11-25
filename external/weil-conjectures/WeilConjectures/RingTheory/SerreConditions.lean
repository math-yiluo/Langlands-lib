/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Height

/-!
# Serre's conditions for Noetherian rings

Source: Stacks Project, Algebra, Definition 10.157.1 (Tag 031P), parts (1) and (2);
height as local dimension, Definition 10.60.3 (Tag 00KF)
(blueprint: def-weil-pbc-serre-conditions-rk-sk).

## Main definitions

- `Ring.IsSerreR`: regularity in codimension at most `k`.
- `Ring.IsSerreS`: depth at least the minimum of `k` and local dimension.
-/

@[expose] public section

universe u

namespace Ring

/-- Serre's condition `(R_k)` for a Noetherian ring (Stacks, Tag 031P, part (1);
(blueprint: def-weil-pbc-serre-conditions-rk-sk)). The height of a prime is the
dimension of its localization (Stacks, Tag 00KF). -/
def IsSerreR (R : Type u) [CommRing R] [IsNoetherianRing R] (k : ℕ) : Prop :=
  ∀ (p : Ideal R) [p.IsPrime], p.height ≤ (k : ℕ∞) →
    IsRegularLocalRing (Localization.AtPrime p)

/-- Serre's condition `(S_k)` for a Noetherian ring (Stacks, Tag 031P, part (2);
(blueprint: def-weil-pbc-serre-conditions-rk-sk)). The depth is that of the local
ring as a module over itself, and `p.height` is its Krull dimension (Tag 00KF). -/
def IsSerreS (R : Type u) [CommRing R] [IsNoetherianRing R] (k : ℕ) : Prop :=
  ∀ (p : Ideal R) [p.IsPrime],
    min (k : ℕ∞) p.height ≤
      IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p)

end Ring
