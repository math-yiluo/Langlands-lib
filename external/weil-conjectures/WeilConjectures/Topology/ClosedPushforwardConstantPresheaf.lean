/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The section presheaf of a constant sheaf pushed forward from a closed subset

Source: Stacks Project, Sheaves on Spaces, Tags 006W and 00AE
(blueprint: def-weil-pbc-closed-pushforward-constant-presheaf).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- The presheaf of locally constant maps on intersections with a closed subset, with
restriction of functions. The subtypes carry their subspace topologies.
Source: Stacks Project, Tags 006W and 00AE
(blueprint: def-weil-pbc-closed-pushforward-constant-presheaf).
The construction makes sense for every subset; closedness is needed for the off-subset
stalk assertion, rather than for defining the section presheaf. -/
def closedPushforwardConstantPresheaf (X : TopCat.{u}) (C : Set X) (R : Type u) :
    X.Presheaf (Type u) where
  obj V := LocallyConstant {y : X // y ∈ unop V ∧ y ∈ C} R
  map {U V} i := TypeCat.ofHom (LocallyConstant.comap
    ⟨fun y : {y : X // y ∈ unop V ∧ y ∈ C} ↦
      ⟨y.1, i.unop.le y.2.1, y.2.2⟩,
      continuous_subtype_val.subtype_mk _⟩)
  map_id := by intros; rfl
  map_comp := by intros; rfl

end TopCat
