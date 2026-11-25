/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-! # Countable coproducts for tensor totalizations -/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.GradedObject

/-- Build the coproducts of a totalization before specializing its summands. -/
lemma projection_hasCountableMap {C : Type*} [Category* C] [HasCountableCoproducts C]
    (X : GradedObject (ℤ × ℤ) C) (p : ℤ × ℤ → ℤ) : X.HasMap p :=
  fun _ ↦ inferInstance

end CategoryTheory.GradedObject
