/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Flasque
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Topology.Sheaves.Flasque
import WeilConjectures.AlgebraicGeometry.InjectiveRestrictionSurjective

/-!
# Flasque sheaves are acyclic

Source: literature/stacks-project/cohomology.tex, Lemma Tag 09SY (lemma-flasque-acyclic)
(blueprint: lemma-uniform-bounds-pro-etale-affines).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

/-- A flasque abelian sheaf on a topological space `X` has vanishing cohomology
`H^q(X, F) = Sheaf.H' F q ⊤` in every positive degree `q`.
Source: Stacks Project, `cohomology.tex`, Tag 09SY (`lemma-flasque-acyclic`)
(blueprint: lemma-uniform-bounds-pro-etale-affines).

Proof:
1. Apply the source library's `IsFlasque.subsingleton_H` in degree `q = n + 1`.
   It proves flasque acyclicity by embedding into injectives and dimension shifting;
   enough injectives on the opens site is provided by Mathlib.
2. The representable presheaf of the top open has exactly one element at every open.
   The free abelian group on this singleton is canonically `ℤ`, hence `ULift ℤ`.
   These component isomorphisms are natural because every generator maps to `1`.
3. Sheafify this isomorphism and use `Ext.precompAddEquiv` to identify `H' F q ⊤`
   with `H F q`. Transport the subsingleton instance along the equivalence. 
(blueprint: lem-sc-topological-flasque-acyclic)
-/
theorem IsFlasque.subsingleton_H'_top {X : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque F] (q : ℕ) (hq : 0 < q) :
    Subsingleton (CategoryTheory.Sheaf.H' F q ⊤) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have : Subsingleton (CategoryTheory.Sheaf.H.{u} F (n + 1)) :=
    IsFlasque.subsingleton_H n F
  let e : yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free ≅
      (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun U ↦ by
      letI : Unique (U.unop ⟶ (⊤ : Opens X)) :=
        ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
      exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro U V f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro a
        simp [FreeAbelianGroup.uniqueEquiv])
  let eS := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso e
  let eH : CategoryTheory.Sheaf.H' F (n + 1) ⊤ ≃+
      CategoryTheory.Sheaf.H.{u} F (n + 1) :=
    (CategoryTheory.Abelian.Ext.precompAddEquiv eS F (n + 1)).symm
  exact eH.injective.subsingleton

end TopCat.Sheaf
