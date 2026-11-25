/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Free

/-!
# Pseudo-coherence through degree m over a ring

Source: Stacks Project, More on Algebra, Definition 15.66.1 (Tag 064Q)
(blueprint: def-pc-ring-m-pseudo-coherent).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

/-- An object of the derived category of a commutative ring is `m`-pseudo-coherent if a
bounded complex of finite free modules maps to it, inducing cohomology isomorphisms above
`m` and a surjection in degree `m` (Stacks, Tag 064Q).
(blueprint: def-pc-ring-m-pseudo-coherent) -/
def IsMPseudoCoherent {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ) (C : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  ∃ (E : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ),
    E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
    (∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) ∧
    ∃ f : Q.obj E ⟶ C,
      (∀ i : ℤ, m < i → IsIso ((homologyFunctor (ModuleCat.{v} R) i).map f)) ∧
      Epi ((homologyFunctor (ModuleCat.{v} R) m).map f)

end DerivedCategory
