/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB

import WeilConjectures.Topology.FiniteClosedCoverCohomologyVanishing
import WeilConjectures.Topology.IrreducibleIntegerExtensionVanishing
import WeilConjectures.Topology.NoetherianExtensionByZeroReduction

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Fixed-bound version of the finite irreducible closed-cover reduction. -/
private theorem vanishing_at_bound_of_irreducible
    (d q : ℕ)
    (hIrred : ∀ (Y : Type u) [TopologicalSpace Y] [NoetherianSpace Y]
      [IrreducibleSpace Y], topologicalKrullDim Y ≤ (d : WithBot ℕ∞) →
      ∀ G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u},
        IsZero (Sheaf.H' G q (⊤ : Opens Y)))
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsZero (Sheaf.H' F q (⊤ : Opens X)) := by
  obtain ⟨S, hS, hcover⟩ := NoetherianSpace.exists_finset_irreducible (⊤ : Closeds X)
  apply cohomology_vanishing_of_finite_closed_cover X S hcover.symm q _ F
  intro Z hZ G
  have : IrreducibleSpace (Z : Set X) := Subtype.irreducibleSpace (hS ⟨Z, hZ⟩)
  exact hIrred (Z : Set X) ((topologicalKrullDim_subspace_le X _).trans hdim) G

/-- The irreducible case of Grothendieck vanishing for Noetherian spaces.
Source: literature/stacks-project/cohomology.tex, Proposition 02UZ, irreducible case
(blueprint: new-node-noetherian-irreducible).
Proof (numbered, following Proposition 02UZ and Lemma 02UX). (1) Induct on d.
The induction assertion quantifies over every Noetherian space X with dim X <= d,
every abelian sheaf F, and every degree q > d.
The empty space is immediate from the empty-cover sheaf axiom. (2) In the
irreducible case and d = 0, every nonempty open is all of X: a proper closed
irreducible component would give a chain of length one. Hence sections identify F
with the constant sheaf F(X), and `lem-sc-irreducible-noetherian-constant-acyclic`
gives vanishing for q > 0. (3) For d > 0, Noetherianity gives quasi-compact X,
quasi-compact opens as a basis, and quasi-compact intersections, verifying the first
three hypotheses of `lem-sc-noetherian-extension-by-zero-reduction`. (4) For a
quasi-compact open j : U -> X, if U is empty then j_!Z_U = 0. Otherwise U is dense;
for Z = X \\ U, the closed subspace is Noetherian and has dimension at most d-1.
The open-closed sequence (`lem-sc-noetherian-open-closed-cohomology-sequence`) for
the constant sheaf gives 0 -> j_!Z_U -> Z_X -> i_*Z_Z -> 0. The constant-sheaf
acyclicity node kills H^p(X,Z_X), and the closed-immersion comparison
`lem-sc-cohomology-closed-immersion-pushforward` plus outer induction kills
H^(p-1)(X,i_*Z_Z) = H^(p-1)(Z,Z_Z), since p-1 > d-1 >= dim Z. Thus the exact
segment H^(p-1)(Z,Z_Z) -> H^p(X,j_!Z_U) -> H^p(X,Z_X), from
`def-sc-topological-abelian-cohomology`, kills the middle term. This verifies the
fourth hypothesis of 02UX, so the reduction gives vanishing for every F on an
irreducible X.
(5) At this fixed d, prove the assertion for all Noetherian spaces by induction
on their number of irreducible components, supplied by
`lem-sc-noetherian-finite-irreducible-components`. Zero components means the empty
space; one component uses the irreducible result just established at d. Otherwise
choose a component Z, put U = X \ Z and Zprime = closure(U). The latter is the
union of the remaining components. Both closed subspaces are Noetherian, have
dimension at most d, and have fewer components. Apply
`lem-sc-noetherian-open-closed-cohomology-sequence` to F and U. Its support clause
expresses j_!j^*F as a closed pushforward from Zprime. Component induction and
`lem-sc-cohomology-closed-immersion-pushforward` kill its degree-q cohomology and
that of i_*i^*F. The long exact sequence from
`def-sc-topological-abelian-cohomology` then kills H^q(X,F). This completes the
outer induction. This repeats the fixed-d component argument directly: the
component theorem below cannot yet be applied because its hIrred quantifies over
all dimension bounds. (blueprint: new-node-noetherian-irreducible) -/
theorem noetherian_vanishing_irreducible
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    [IrreducibleSpace X] (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) :
    IsZero (Sheaf.H' F q (⊤ : Opens X)) := by
  have hall : ∀ (e : ℕ) (Y : Type u) [TopologicalSpace Y] [NoetherianSpace Y],
      topologicalKrullDim Y ≤ (e : WithBot ℕ∞) →
      ∀ (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
        (r : ℕ), e < r → IsZero (Sheaf.H' G r (⊤ : Opens Y)) := by
    intro e
    induction e using Nat.strong_induction_on with
    | h e ih =>
      intro Y _ _ hdimY G r hr
      apply vanishing_at_bound_of_irreducible e r ?_ Y hdimY G
      intro Z _ _ _ hdimZ H
      apply noetherian_extensionByZero_reduction (TopCat.of Z) e ?_ ?_ ?_ H r hr
      · intro U hU z hz
        exact ⟨U, hU, NoetherianSpace.isCompact U, hz, Set.Subset.rfl⟩
      · intro U V _ _ _ _
        exact NoetherianSpace.isCompact (U ∩ V)
      · exact irreducible_integer_extension_vanishing (TopCat.of Z) e hdimZ ih
  exact hall d X hdim F q hq

-- Preserve the existing names of the unused binders inside `hIrred`.
set_option linter.unusedVariables false in
/-- The component induction step in Grothendieck vanishing for Noetherian spaces.
Source: literature/stacks-project/cohomology.tex, Proposition 02UZ, proof by induction
on the finite number of irreducible components (blueprint: new-node-noetherian-components).
Proof (numbered, following Proposition 02UZ). (1) Fix d and q and induct on the
finite number of irreducible components supplied by
`lem-sc-noetherian-finite-irreducible-components`; the zero-component (empty) case
is the empty-cover case, and the one-component case is exactly `hIrred`. (2) For
several components choose an irreducible component Z, put U = X \\ Z and
Z' = closure(U). The space Z' is the union of the remaining components, hence has
fewer components; both Z and Z' are closed Noetherian subspaces and inherit
dim <= d. (3) Apply `lem-sc-noetherian-open-closed-cohomology-sequence` to the
open-closed decomposition. Its closed-support clause, together with
`lem-sc-cohomology-closed-immersion-pushforward`, identifies the relevant terms on
Z and Z'. Exactness of the resulting long exact sequence reduces H^q(X,F) to the
vanishing statements for Z (where `hIrred` is applied, since Z is irreducible) and
for Z' (where the component induction hypothesis applies). The hypotheses
`q > d` and dim <= d are preserved throughout, so the middle term is zero. -/
theorem noetherian_vanishing_of_irreducible_components
    (hIrred : ∀ (Y : Type u) [TopologicalSpace Y] [NoetherianSpace Y]
      [IrreducibleSpace Y] (d : ℕ)
      (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
      (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
      (q : ℕ) (hq : d < q),
      IsZero (Sheaf.H' F q (⊤ : Opens Y)))
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) :
    IsZero (Sheaf.H' F q (⊤ : Opens X)) := by
  apply vanishing_at_bound_of_irreducible d q ?_ X hdim F
  intro Y _ _ _ hdimY G
  exact hIrred Y d hdimY G q hq

end TopCat
