/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.Topology.IrreducibleConstantSections

import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import WeilConjectures.Topology.FlasqueZariskiAcyclic
public import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u w'

namespace TopCat

/-! # Constant sheaves are acyclic on irreducible Noetherian spaces
Source: literature/stacks-project/cohomology.tex, Lemma 02UW
(blueprint: lem-sc-irreducible-noetherian-constant-acyclic) -/

/-- The constant abelian sheaf on an irreducible Noetherian space has no higher cohomology.
Source: literature/stacks-project/cohomology.tex, Lemma 02UW
(blueprint: lem-sc-irreducible-noetherian-constant-acyclic)
Proof:
1. Every nonempty open is irreducible; `irreducible_constant_sections` identifies constant
   sections and restrictions, while the empty open has the zero group. Hence the sheaf is flasque.
2. Apply flasque acyclicity on the topological opens site.
-/
theorem irreducible_noetherian_constant_acyclic
    (X : TopCat.{u}) [IrreducibleSpace X] [NoetherianSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{w'} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (A : Type u) [AddCommGroup A] :
    ∀ (q : ℕ), 0 < q →
      Subsingleton (CategoryTheory.Sheaf.H' ((constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)) q ⊤) := by
  let F := (constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of A)
  obtain ⟨e, he⟩ := irreducible_constant_sections X A
  have : TopCat.Sheaf.IsFlasque F := by
    constructor
    intro U V i
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro s
    by_cases hV : (V.unop : Set X).Nonempty
    · have hU : (U.unop : Set X).Nonempty := Set.Nonempty.mono i.unop.le hV
      refine ⟨(e U.unop hU).symm (e V.unop hV s), ?_⟩
      apply (e V.unop hV).injective
      have h := congrFun (he U.unop V.unop i.unop.le hV)
        ((e U.unop hU).symm (e V.unop hV s))
      have hi : (homOfLE i.unop.le).op = i := Subsingleton.elim _ _
      rw [hi] at h
      simpa using h
    · have hbot : V.unop = ⊥ := by
        apply Opens.ext
        exact Set.not_nonempty_iff_eq_empty.mp hV
      have : Subsingleton (F.obj.obj V) :=
        AddCommGrpCat.subsingleton_of_isZero (Sheaf.isTerminalOfEqEmpty F hbot).isZero
      exact ⟨0, Subsingleton.elim _ _⟩
  intro q hq
  have : Subsingleton (CategoryTheory.Sheaf.H'.{u} F q ⊤) :=
    Sheaf.IsFlasque.subsingleton_H'_top F q hq
  let eH : CategoryTheory.Sheaf.H'.{w'} F q ⊤ ≃
      CategoryTheory.Sheaf.H'.{u} F q ⊤ := CategoryTheory.Abelian.Ext.chgUniv
  exact eH.injective.subsingleton

end TopCat
