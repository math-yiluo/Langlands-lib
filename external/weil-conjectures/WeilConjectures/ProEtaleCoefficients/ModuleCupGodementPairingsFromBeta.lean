/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel

@[expose] public section
-- This module only keeps private proof helpers.
set_option linter.privateModule false
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private theorem stalk_id (X : Scheme.{u}) (F : X.Modules) (x : X) :
    (𝟙 F : F ⟶ F).stalkLinearMap x = LinearMap.id := by
  ext m
  obtain ⟨V, hx, s, rfl⟩ := F.presheaf.exists_germ_eq m
  rw [Hom.stalkLinearMap_germ]
  rfl

private theorem stalk_comp (X : Scheme.{u}) {F G H : X.Modules}
    (f : F ⟶ G) (g : G ⟶ H) (x : X) :
    (f ≫ g).stalkLinearMap x = g.stalkLinearMap x ∘ₗ f.stalkLinearMap x := by
  ext m
  obtain ⟨V, hx, s, rfl⟩ := F.presheaf.exists_germ_eq m
  simp only [Hom.stalkLinearMap_germ, LinearMap.comp_apply, Hom.comp_app,
    ConcreteCategory.comp_apply]

private def proj (X : Scheme.{u}) (F : X.Modules) (x : X) :
    moduleCup_godementObject X F ⟶ skyscraper x (F.presheaf.stalk x) :=
  Pi.π (fun y : X ↦ skyscraper y (F.presheaf.stalk y)) x

private def stalkEval (X : Scheme.{u}) (F : X.Modules) (x : X) :
    (moduleCup_godementObject X F).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x :=
  skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ (proj X F x).stalkLinearMap x

private theorem proj_map (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) (x : X) :
    moduleCup_godementMap X f ≫ proj X G x =
      toSkyscraper (f.stalkLinearMap x ∘ₗ stalkEval X F x) := by
  simp only [moduleCup_godementMap, proj, Pi.lift_comp_π, comp_toSkyscraper, stalkEval,
    LinearMap.comp_assoc]

private theorem eval_toSkyscraper (X : Scheme.{u}) (F : X.Modules) (x : X)
    {P : X.Modules} (l : P.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x) :
    skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ (toSkyscraper l).stalkLinearMap x = l :=
  (skyscraperHomEquiv x (F.presheaf.stalk x) P).left_inv l

private theorem eval_map (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) (x : X) :
    stalkEval X G x ∘ₗ (moduleCup_godementMap X f).stalkLinearMap x =
      f.stalkLinearMap x ∘ₗ stalkEval X F x := by
  change (skyscraperStalkEval x (G.presheaf.stalk x) ∘ₗ
    (proj X G x).stalkLinearMap x) ∘ₗ (moduleCup_godementMap X f).stalkLinearMap x = _
  rw [LinearMap.comp_assoc, ← stalk_comp, proj_map, eval_toSkyscraper]

private theorem map_id (X : Scheme.{u}) (F : X.Modules) :
    moduleCup_godementMap X (𝟙 F) = 𝟙 _ := by
  apply Pi.hom_ext
  intro x
  change moduleCup_godementMap X (𝟙 F) ≫ proj X F x = (𝟙 _ : _ ⟶ _) ≫ proj X F x
  rw [proj_map, stalk_id, LinearMap.id_comp, Category.id_comp]
  exact (skyscraperHomEquiv x (F.presheaf.stalk x) _).right_inv _

private theorem map_comp (X : Scheme.{u}) {F G H : X.Modules}
    (f : F ⟶ G) (g : G ⟶ H) :
    moduleCup_godementMap X (f ≫ g) =
      moduleCup_godementMap X f ≫ moduleCup_godementMap X g := by
  apply Pi.hom_ext
  intro x
  change moduleCup_godementMap X (f ≫ g) ≫ proj X H x =
    (moduleCup_godementMap X f ≫ moduleCup_godementMap X g) ≫ proj X H x
  rw [Category.assoc, proj_map, proj_map, comp_toSkyscraper, stalk_comp,
    LinearMap.comp_assoc, LinearMap.comp_assoc, eval_map]

end
end AlgebraicGeometry.Scheme.Modules
