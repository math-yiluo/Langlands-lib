/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import WeilConjectures.RingTheory.ProjectiveResolutionExtAllDegrees

/-!
# Bounded projective resolutions and Ext vanishing

Source: Stacks Project, Algebra, Lemma 065R, parts (1)--(3)
(blueprint: lem-weil-pbc-projective-dimension-ext-characterization).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ModuleCat

/-- A resolution of length at most `n` is equivalent both to vanishing of Ext in degree
`n + 1` against every module and to vanishing in every degree at least `n + 1`.
Source: Stacks Project, Algebra, Lemma 065R, parts (1)--(3)
(blueprint: lem-weil-pbc-projective-dimension-ext-characterization).

Proof: first induct on the resolution bound. For bound zero, exactness identifies `X`
with its projective degree-zero term (`def-weil-pbc-exact-sequence` and
`def-weil-pbc-projective-module`), and `lem-weil-pbc-projective-ext-criterion` gives
vanishing in every positive degree. For bound `n + 1`, the kernel `K` of `P₀ → X`
has a resolution of length at most `n` (`def-weil-pbc-finite-global-dimension`).
The contravariant long exact Ext sequence for `0 → K → P₀ → X → 0`
(`lem-weil-pbc-ext-long-exact-first-variable`) gives the segment
`Ext^(i-1)(K,Y) → Ext^i(X,Y) → Ext^i(P₀,Y)`. For `i ≥ n + 2`, the outer
terms vanish by induction and projectivity, so the middle term vanishes.
Vanishing in every degree at least `n + 1` implies vanishing in degree `n + 1`.
Conversely, induct on `n`. For `n = 0`, the Ext-one criterion makes `X` projective,
and its identity gives a length-zero resolution. At the next bound, take the free
module on the underlying set of `X` and its surjection to `X`
(`def-weil-pbc-free-module`, `lem-weil-pbc-free-module-projective`), with kernel `K`.
The same long exact sequence gives
`Ext^(n+1)(F,Y) → Ext^(n+1)(K,Y) → Ext^(n+2)(X,Y)`.
Both outer groups vanish, so induction supplies a length-`n` resolution of `K`.
Append `F → X` to it. The inclusion of `K` in `F` preserves exactness at its
preceding term, and its image is precisely the kernel of `F → X`; hence the
appended resolution is exact and has length at most `n + 1`.
The explicit `HasExt.standard` term merely chooses the small model of the Ext
of `def-pc-ext`. The module universe `max u v` contains the ring, so categorical
projectivity agrees with module projectivity and free resolutions stay in this universe. -/
theorem hasProjectiveResolutionLE_iff_ext_vanishing
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    (HasProjectiveResolutionLE X n ↔
      ∀ Y : ModuleCat.{max u v} R,
        Subsingleton
          (@Abelian.Ext _ _ _ (HasExt.standard (ModuleCat.{max u v} R)) X Y (n + 1))) ∧
    (HasProjectiveResolutionLE X n ↔
      ∀ (Y : ModuleCat.{max u v} R) (i : ℕ), n + 1 ≤ i →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard (ModuleCat.{max u v} R)) X Y i)) := by
  let := HasExt.standard (ModuleCat.{max u v} R)
  refine ⟨?_, projective_resolution_ext_all_degrees X n⟩
  constructor
  · intro h Y
    let := (hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X n).mp h
    exact HasProjectiveDimensionLT.subsingleton X (n + 1) (n + 1) le_rfl Y
  · intro h
    exact (hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X n).mpr
      (hasProjectiveDimensionLT_of_enoughInjectives X (n + 1) h)

end ModuleCat
