/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Unramified.Field

/-!
# Differentials of algebraic elements

- `KaehlerDifferential.D_eq_zero_of_isAlgebraic`: over a perfect field `k`, the differential of
  an element algebraic over `k` vanishes.
-/

@[expose] public section

open IntermediateField

namespace KaehlerDifferential

/-- Over a perfect field `k`, the differential `d s ∈ Ω[K⁄k]` of an element `s` algebraic over
`k` vanishes: it comes from `Ω[k⟮s⟯⁄k] = 0`, since `k⟮s⟯` is a finite separable extension
of `k`. -/
theorem D_eq_zero_of_isAlgebraic {k K : Type*} [Field k] [PerfectField k] [Field K]
    [Algebra k K] {s : K} (hs : IsAlgebraic k s) : D k K s = 0 := by
  have : Algebra.IsAlgebraic k k⟮s⟯ :=
    IntermediateField.isAlgebraic_adjoin_simple hs.isIntegral
  have : Algebra.IsSeparable k k⟮s⟯ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyUnramified k k⟮s⟯ := .of_isSeparable k _
  rw [← IntermediateField.AdjoinSimple.algebraMap_gen k s, ← map_D k k k⟮s⟯ K,
    Subsingleton.elim (D k k⟮s⟯ _) 0, map_zero]

end KaehlerDifferential
