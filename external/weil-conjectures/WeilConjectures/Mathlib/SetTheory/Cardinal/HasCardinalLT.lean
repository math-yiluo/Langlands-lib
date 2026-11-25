/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# The type of finite subsets of a type of cardinality `< κ`

If `κ` is an infinite cardinal and a type `X` has cardinality `< κ`, then so does the type
`Finset X` of finite subsets of `X`.

## Main results

- `hasCardinalLT_finset`.
-/

@[expose] public section

universe w

lemma hasCardinalLT_finset {X : Type w} {κ : Cardinal.{w}} (hκ : Cardinal.aleph0 ≤ κ)
    (h : HasCardinalLT X κ) : HasCardinalLT (Finset X) κ := by
  rcases finite_or_infinite X with _ | hX
  · have : Fintype X := Fintype.ofFinite X
    exact hasCardinalLT_of_finite _ _ hκ
  · rw [hasCardinalLT_iff_cardinal_mk_lt] at h ⊢
    rwa [Cardinal.mk_finset_of_infinite]
