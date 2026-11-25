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
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorCoordinates

@[expose] public section
-- This module only keeps private proof helpers.
set_option linter.privateModule false
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private lemma tensor_hom_ext (X : Scheme.{u}) (H K L : X.Modules)
    (f g : H ⊗ K ⟶ L)
    (h : moduleCup_sectionTensor X H K ≫ f.val =
      moduleCup_sectionTensor X H K ≫ g.val) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have he : (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H K).inv ≫ f =
      (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H K).inv ≫ g := by
    apply (adj.homEquiv _ L).injective
    change adj.unit.app _ ≫ ((SheafOfModules.tensorObjIsoSheafification
      (R := X.sheaf) H K).inv ≫ f).val = adj.unit.app _ ≫
        ((SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) H K).inv ≫ g).val
    simpa only [SheafOfModules.comp_val, Category.assoc, moduleCup_sectionTensor] using h
  exact (cancel_epi _).1 he

private def proj (X : Scheme.{u}) (H : X.Modules) (x : X) :
    moduleCup_godementObject X H ⟶ skyscraper x (H.presheaf.stalk x) :=
  CategoryTheory.Limits.Pi.π (fun y : X ↦ skyscraper y (H.presheaf.stalk y)) x

private def eval (X : Scheme.{u}) (H : X.Modules) (x : X) :
    (moduleCup_godementObject X H).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      H.presheaf.stalk x :=
  skyscraperStalkEval x (H.presheaf.stalk x) ∘ₗ (proj X H x).stalkLinearMap x

end
end AlgebraicGeometry.Scheme.Modules
