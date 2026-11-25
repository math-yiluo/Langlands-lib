/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB

import WeilConjectures.Topology.EmptySpaceCohomologyVanishing
import WeilConjectures.Topology.ClosedUnionCohomologyVanishing
import WeilConjectures.Topology.WholeSpaceClosedSubtypeCohomologyVanishing

/-! # Vanishing over a finite closed cover

Source: Stacks Project, Cohomology, Proposition 02UZ, component-reduction paragraph.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- Vanishing in a fixed degree for every sheaf on each member of a finite closed
cover implies vanishing in that degree on the ambient Noetherian space.
Source: Stacks Project, Cohomology, Proposition 02UZ, component-reduction paragraph
(https://stacks.math.columbia.edu/tag/02UZ).
(blueprint: new-node-finite-closed-cover-cohomology-vanishing).

Proof: Induct on the size of the finite closed cover. For the empty cover the
space is empty. The empty-cover sheaf axiom makes every abelian sheaf zero;
its cohomology is zero in every degree. For a nonempty cover choose one closed
member Z and let W be the union of the others. Put U = X \ Z. In the open-closed
short exact sequence for F, the right term is the closed pushforward of F|Z.
The left term is supported on closure(U), which is contained in W. It is therefore
the closed pushforward of an abelian sheaf G on W (use the stalkwise isomorphism
criterion for the adjunction unit). Restricting the remaining cover to W gives a
smaller finite closed cover. The induction hypothesis applies to every G on W.
Closed-pushforward cohomology comparison kills both outer degree-q terms of the
short exact sequence's long exact sequence, so its middle degree-q term is zero.
This argument needs no vanishing in degree q-1 on intersections: the hypothesis
quantifies over every sheaf on each closed member, including supported sheaves.
It applies to q=0 as well as positive q, and permits empty or repeated members. -/
theorem cohomology_vanishing_of_finite_closed_cover
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (S : Finset (Closeds X)) (hcover : S.sup id = ⊤) (q : ℕ)
    (hvanish : ∀ Z ∈ S,
      ∀ G : Sheaf (Opens.grothendieckTopology (Z : Set X)) AddCommGrpCat.{u},
        IsZero (Sheaf.H' G q (⊤ : Opens (Z : Set X))))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsZero (Sheaf.H' F q (⊤ : Opens X)) := by
  classical
  have hsup : ∀ G : Sheaf (Opens.grothendieckTopology ((S.sup id : Closeds X) : Set X))
      AddCommGrpCat.{u}, IsZero (Sheaf.H' G q (⊤ : Opens ((S.sup id : Closeds X) : Set X))) := by
    clear hcover F
    revert hvanish
    induction S using Finset.induction_on with
    | empty =>
        intro _ G
        let : IsEmpty ↥(⊥ : Closeds X) := ⟨fun x ↦ x.property⟩
        exact cohomology_vanishing_of_isEmpty (↑(⊥ : Closeds X)) q G
    | @insert Z S hZS ih =>
        intro hvanish
        rw [Finset.sup_insert]
        apply cohomology_vanishing_of_closed_union X Z (S.sup id) q
        · exact hvanish Z (Finset.mem_insert_self Z S)
        · exact ih (fun W hW ↦ hvanish W (Finset.mem_insert_of_mem hW))
  rw [hcover] at hsup
  exact cohomology_vanishing_of_whole_closed_subtype X q hsup F

end TopCat
