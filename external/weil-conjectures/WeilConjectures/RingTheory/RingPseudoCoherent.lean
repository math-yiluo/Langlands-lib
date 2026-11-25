/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Free

/-!
# Pseudo-coherent objects of the derived category of a ring

Source: Stacks Project, More on Algebra, Definition 15.66.1 (2), Tag 064P in Section 064N
(blueprint: def-pc-ring-pseudo-coherent-complex).

The fixed-degree notion is `DerivedCategory.IsMPseudoCoherent`
(blueprint: def-pc-ring-m-pseudo-coherent).

## Main definitions

* `DerivedCategory.IsPseudoCoherent`: a bounded above finite free representative.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

/-- An object of the derived category of a commutative ring is pseudo-coherent if it is
isomorphic in the derived category to a bounded above complex of finite free modules. An
isomorphism in the localization expresses quasi-isomorphism, without requiring a particular
representative of the object.
Source: Stacks Project, Tag 064P, Definition 15.66.1 (2)
(blueprint: def-pc-ring-pseudo-coherent-complex). -/
def IsPseudoCoherent {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    (C : DerivedCategory (ModuleCat.{v} A)) : Prop :=
  ∃ (E : CochainComplex (ModuleCat.{v} A) ℤ) (b : ℤ), E.IsStrictlyLE b ∧
    (∀ j : ℤ, Module.Free A (E.X j) ∧ Module.Finite A (E.X j)) ∧
    Nonempty (Q.obj E ≅ C)

end DerivedCategory
