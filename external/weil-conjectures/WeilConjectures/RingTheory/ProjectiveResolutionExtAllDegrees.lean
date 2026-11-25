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
@[expose] public section
universe u v
open CategoryTheory
namespace ModuleCat
/-- One component of Stacks 065R. Induct on the resolution bound. A bounded projective
resolution gives a long exact Ext sequence whose projective term contributes no positive
Ext; shifting along the sequence and applying the induction hypothesis yields vanishing
in every degree at least `n + 1`. Conversely, the all-degrees hypothesis includes the
degree `n + 1` case, and the kernel of a free epimorphism onto `X` inherits the shifted
vanishing needed by the induction hypothesis. Splicing the resulting shorter resolution
with that epimorphism gives a resolution of `X` of length at most `n`. The argument is
performed in `ModuleCat`; `HasExt.standard` merely chooses the standard small Ext model.
Source: Stacks Project, Algebra, Lemma 065R.
(blueprint: lem-weil-pbc-projective-resolution-ext-all-degrees). -/
theorem projective_resolution_ext_all_degrees
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    (HasProjectiveResolutionLE X n ↔
      ∀ (Y : ModuleCat.{max u v} R) (i : ℕ), n + 1 ≤ i →
        Subsingleton
          (@Abelian.Ext _ _ _ (HasExt.standard (ModuleCat.{max u v} R)) X Y i)) := by
  let := HasExt.standard (ModuleCat.{max u v} R)
  constructor
  · intro h Y i hi
    let := (hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X n).mp h
    exact HasProjectiveDimensionLT.subsingleton X (n + 1) i hi Y
  · intro h
    apply (hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE X n).mpr
    apply HasProjectiveDimensionLT.mk
    intro i hi Y e
    exact (h Y i hi).elim _ _
end ModuleCat
