/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# The functor of preimages of open subsets is final

For a continuous map `f : X ⟶ Y`, the functor `TopologicalSpace.Opens.map f` is final:
the comma category of open subsets of `Y` whose preimage contains a given open subset of `X`
has `⊤` as a terminal object.

We also record that `TopologicalSpace.Opens.map f` preserves finite products: taking preimages
commutes with `⊤` and with binary intersections.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace TopologicalSpace.Opens

variable {X Y : TopCat.{u}}

instance (f : X ⟶ Y) : (Opens.map f).Final where
  out U := isConnected_of_isTerminal _ (IsTerminal.ofUniqueHom
    (X := StructuredArrow.mk (S := U) (Y := (⊤ : Opens Y))
      (homOfLE (by simp) : U ⟶ (Opens.map f).obj ⊤))
    (fun _ ↦ StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _))
    (fun _ _ ↦ StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)))

variable (X) in
lemma terminal_eq_top : (⊤_ (Opens X)) = ⊤ :=
  le_antisymm le_top (leOfHom (terminalIsTerminal.from ⊤))

instance isIso_prodComparison_map (f : X ⟶ Y) (U V : Opens Y) :
    IsIso (prodComparison (Opens.map f) U V) :=
  ⟨homOfLE (by rw [CompleteLattice.prod_eq_inf, CompleteLattice.prod_eq_inf]; exact le_rfl),
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Taking preimages of open sets along a continuous map preserves binary products, i.e.
binary intersections. -/
instance preservesBinaryProducts_map (f : X ⟶ Y) :
    PreservesLimitsOfShape (Discrete WalkingPair) (Opens.map f) :=
  preservesBinaryProducts_of_isIso_prodComparison _

instance isIso_terminalComparison_map (f : X ⟶ Y) :
    IsIso (terminalComparison (Opens.map f)) :=
  ⟨homOfLE (by rw [terminal_eq_top, terminal_eq_top]; exact le_of_eq (Opens.map_top f).symm),
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Taking preimages of open sets along a continuous map preserves the terminal object. -/
instance preservesTerminal_map (f : X ⟶ Y) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Opens.map f) :=
  have : PreservesLimit (Functor.empty.{0} (Opens Y)) (Opens.map f) :=
    PreservesTerminal.of_iso_comparison _
  preservesLimitsOfShape_pempty_of_preservesTerminal _

end TopologicalSpace.Opens

end
