/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle

/-!
# Pseudo-coherence in a distinguished triangle

Source: Stacks Project, `more-algebra.tex`, Tag 064R, label
`lemma-cone-pseudo-coherent` (blueprint: lem-sc-cone-pseudo-coherent).
-/

@[expose] public section

universe u v w

open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory (IsMPseudoCoherent)

namespace CategoryTheory

/-- If `K ⟶ L ⟶ M ⟶ K[1]` is distinguished in the derived category of a ring,
then `(m + 1)`-pseudo-coherence of `K` and `m`-pseudo-coherence of `L` imply
`m`-pseudo-coherence of `M` (Stacks, Tag 064R).
(blueprint: lem-sc-cone-pseudo-coherent)

Proof: apply the first clause of the ring-level distinguished-triangle lemma
(lem-pc-ring-pseudo-coherent-distinguished-triangle, Tag 064R) to the triangle `T`:
if `T.obj₁` is `(m + 1)`-pseudo-coherent and `T.obj₂` is `m`-pseudo-coherent, then
`T.obj₃` is `m`-pseudo-coherent.
-/
theorem isMPseudoCoherent_cone
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ)
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} R))) :
    IsMPseudoCoherent (m + 1) T.obj₁ →
      IsMPseudoCoherent m T.obj₂ → IsMPseudoCoherent m T.obj₃ := by
  exact (isMPseudoCoherent_of_distinguished_triangle R m T hT).1

end CategoryTheory
