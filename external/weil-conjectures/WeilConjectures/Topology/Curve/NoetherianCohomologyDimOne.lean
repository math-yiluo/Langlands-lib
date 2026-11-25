/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Topology.NoetherianTopologicalCohomologyVanishing

/-!
# Second cohomology on Noetherian spaces of dimension at most one

Source: Stacks Project, Cohomology, Proposition 02UZ, specialized to `d = 1` and `p = 2`
(blueprint: lem-sc-noetherian-cohomology-vanishing-abelian-dim-one).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.Sheaf

/-- The second cohomology of every abelian sheaf on a Noetherian topological space of
Krull dimension at most one is zero.
Source: Stacks Project, Cohomology, Proposition 02UZ, with `d = 1` and `p = 2`
(blueprint: lem-sc-noetherian-cohomology-vanishing-abelian-dim-one).

Proof: apply `lem-sc-noetherian-topological-cohomology-vanishing` with `d = 1` and `q = 2`.
Its hypotheses are precisely that `X` is Noetherian, its topological Krull dimension is at
most one (`def-kun-topological-krull-dimension`), and `F` is an abelian sheaf on `X`.
Since `2 > 1`, its conclusion gives `H²(X,F) = 0`, with cohomology as in
`def-sc-topological-abelian-cohomology`. The dimension bound includes dimension zero and
the empty space; no nonemptiness or separation assumption is used. -/
theorem isZero_secondCohomology_of_noetherian_dim_le_one
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsZero (CategoryTheory.Sheaf.H' F 2 (⊤ : Opens X)) := by
  exact TopCat.isZero_noetherian_topological_cohomology_of_dimension_bound
    X 1 hdim F 2 (by decide)

end TopCat.Sheaf
