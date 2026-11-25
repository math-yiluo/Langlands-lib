/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Stalk functor for presheaves of modules

Source: Stacks Project, Sheaves, Section 007I and Lemma 007J
(blueprint: def-weil-pbc-module-stalk).

The objects and scalar action are Mathlib's stalks, not a second germ construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace PresheafOfModules

/-- Stalk module carrier over the stalk of the ring presheaf.
Source: Stacks Project, Sheaves, Section 007I and Lemma 007J.
(blueprint: def-weil-pbc-module-stalk) -/
abbrev stalkObj {X : TopCat.{u}} (R : TopCat.Presheaf RingCat.{u} X) (x : X)
    (M : PresheafOfModules.{u} R) :
    ModuleCat.{u} (R.stalk x) :=
  ModuleCat.of (R.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) M.presheaf x)

/-- Additive map on stalks induced by a presheaf-module morphism.
Source: Stacks Project, Sheaves, Section 007I and Lemma 007J.
(blueprint: def-weil-pbc-module-stalk) -/
def stalkAddMap {X : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} X} {x : X}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) M.presheaf x →+
      TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) N.presheaf x :=
  ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map f))

/-- The induced stalk map is linear over the stalk ring.
Represent the scalar and vector by germs, restrict them to a common neighborhood,
apply the sectionwise linearity of f, and use germ_ringCat_smul on source and target.
Source: Stacks Project, Sheaves, Section 007I and Lemma 007J.
(blueprint: def-weil-pbc-module-stalk) -/
theorem stalkMap_linear {X : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} X} {x : X}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) :
    ∀ (r : R.stalk x) (m : TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) M.presheaf x),
      stalkAddMap f (r • m) = r • stalkAddMap f m := by
  intro r m
  obtain ⟨U, hxU, r, rfl⟩ := R.exists_germ_eq r
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← R.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
    ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m,
    ← germ_ringCat_smul]
  dsimp only [stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ N.presheaf (U ⊓ V) x hx
      ((f.app (Opposite.op (U ⊓ V))) (_ • _)) = _
  rw [map_smul, germ_ringCat_smul]
  rfl

/-- Linear stalk map induced by a presheaf-module morphism.
Source: Stacks Project, Sheaves, Section 007I and Lemma 007J.
(blueprint: def-weil-pbc-module-stalk) -/
def stalkMap {X : TopCat.{u}} {R : TopCat.Presheaf RingCat.{u} X} {x : X}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) :
    stalkObj R x M ⟶ stalkObj R x N :=
  ModuleCat.ofHom
    { toFun := stalkAddMap f
      map_add' := (stalkAddMap f).map_add
      map_smul' := fun r m => stalkMap_linear f r m }

/-- Stalk maps preserve identities.
The underlying additive stalk map is the image of an identity under toPresheaf
and the abelian-group stalk functor, so it is the identity on every germ.
Source: Stacks Project, Sheaves, Section 007I and Lemma 007J.
(blueprint: def-weil-pbc-module-stalk) -/
theorem stalkMap_id {X : TopCat.{u}}
    {R : TopCat.Presheaf RingCat.{u} X} {x : X}
    (M : PresheafOfModules.{u} R) :
    stalkMap (𝟙 M) = 𝟙 (stalkObj R x M) := by
  ext m
  change stalkAddMap (𝟙 M) m = m
  simp [stalkAddMap]
  rfl

/-- Stalk maps preserve composition.
The underlying additive maps are the images under toPresheaf and the abelian-group
stalk functor. Both functors preserve composition, so the maps agree on every germ.
Source: Stacks Project, Sheaves, Section 007I and Lemma 007J.
(blueprint: def-weil-pbc-module-stalk) -/
theorem stalkMap_comp {X : TopCat.{u}}
    {R : TopCat.Presheaf RingCat.{u} X} {x : X}
    {M N P : PresheafOfModules.{u} R}
    (f : M ⟶ N) (g : N ⟶ P) :
    stalkMap (x := x) (f ≫ g) = stalkMap (x := x) f ≫ stalkMap (x := x) g := by
  ext m
  change stalkAddMap (f ≫ g) m = stalkAddMap g (stalkAddMap f m)
  simp [stalkAddMap]
  rfl

/-- The stalk functor on presheaves of modules used in the statement.
Source: Stacks Project, Sheaves, Section 007I and Lemma 007J.
(blueprint: def-weil-pbc-module-stalk) -/
def moduleStalkFunctor {X : TopCat.{u}}
    (R : TopCat.Presheaf RingCat.{u} X) (x : X) :
    PresheafOfModules.{u} R ⥤ ModuleCat.{u} (R.stalk x) where
  obj M := stalkObj R x M
  map f := stalkMap f
  map_id M := stalkMap_id M
  map_comp f g := stalkMap_comp f g

end PresheafOfModules

end
