/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Topology.Sheaves.Presheaf

/-!
# Restriction maps of presheaves along an equality of opens

A restriction map `F(U) ⟶ F(V)` of a presheaf with values in a concrete category is bijective
when `U = V`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Presheaf

/-- The restriction map `F(U) ⟶ F(V)` of a presheaf with values in a concrete category is
bijective when `U = V`. -/
lemma bijective_map_of_eq {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {X : TopCat}
    (F : TopCat.Presheaf C X) {U V : Opens X} (i : op U ⟶ op V) (h : U = V) :
    Function.Bijective (F.map i) := by
  have : IsIso i := ⟨⟨(homOfLE h.le).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  exact ConcreteCategory.bijective_of_isIso _

end TopCat.Presheaf
