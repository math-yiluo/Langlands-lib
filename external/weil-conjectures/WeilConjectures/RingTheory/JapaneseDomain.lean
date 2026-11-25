/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# N-1 and Japanese domains

Source: Stacks Project, Algebra, Definition 10.161.1 (Tag 032F)
(blueprint: def-weil-pbc-japanese-domain).
-/

@[expose] public section

universe u v

/-- An integral domain `R` with fraction field `K` is N-1 when its integral closure in `K`
is finite as an `R`-module (Stacks, Tag 032F)
(blueprint: def-weil-pbc-japanese-domain). -/
def IsN1 (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] : Prop :=
  Module.Finite R (integralClosure R K)

/-- An integral domain `R` with fraction field `K` is N-2, or Japanese, when for every
finite field extension `L/K`, the integral closure of `R` in `L` is finite as an `R`-module.
The `R`-algebra structure on `L` is required to be the composite through `K`.
(Stacks, Tag 032F) (blueprint: def-weil-pbc-japanese-domain). -/
def IsN2 (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] : Prop :=
  ∀ (L : Type v) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L], Module.Finite R (integralClosure R L)

/-- Taking `L = K` in the definition of N-2 gives the N-1 condition
(Stacks, Tag 032F) (blueprint: def-weil-pbc-japanese-domain). -/
theorem isN1_of_isN2 (R : Type u) (K : Type v) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (h : IsN2 R K) : IsN1 R K := by
  exact h K
