/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all WeilConjectures.SecSmoothPurity.CochainInverseComparison
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence

set_option linter.privateModule false

/-! # Module adjunction for an independently sized inverse image
Source: Stacks Project, Modules on Sites, Tags 03D3 and 03D7.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.CochainInversePairing
open CochainGeometricConstruction GeometricConstruction CochainScalarConstruction
attribute [local irreducible] monoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

private noncomputable def restrictHomEquiv
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) [F.Faithful] [G.Faithful]
    {X₁ X₂ : C₁} {Y₁ Y₂ : C₃}
    (E : (F.obj X₁ ⟶ F.obj X₂) ≃ (G.obj Y₁ ⟶ G.obj Y₂))
    (h : ∀ α, (∃ f : X₁ ⟶ X₂, F.map f = α) ↔
      ∃ g : Y₁ ⟶ Y₂, G.map g = E α) :
    (X₁ ⟶ X₂) ≃ (Y₁ ⟶ Y₂) where
  toFun f := Classical.choose ((h (F.map f)).mp ⟨f, rfl⟩)
  invFun g := Classical.choose ((h (E.symm (G.map g))).mpr
    ⟨g, (E.apply_symm_apply _).symm⟩)
  left_inv f := by
    apply F.map_injective
    have hf := Classical.choose_spec ((h (F.map f)).mp ⟨f, rfl⟩)
    have hg := Classical.choose_spec ((h (E.symm (G.map
      (Classical.choose ((h (F.map f)).mp ⟨f, rfl⟩))))).mpr
        ⟨_, (E.apply_symm_apply _).symm⟩)
    rw [hg, hf, E.symm_apply_apply]
  right_inv g := by
    apply G.map_injective
    have hg := Classical.choose_spec ((h (E.symm (G.map g))).mpr
      ⟨g, (E.apply_symm_apply _).symm⟩)
    have hf := Classical.choose_spec ((h (F.map (Classical.choose
      ((h (E.symm (G.map g))).mpr ⟨g, (E.apply_symm_apply _).symm⟩)))).mp ⟨_, rfl⟩)
    rw [hf, hg, E.apply_symm_apply]

private theorem restrictHomEquiv_map
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) [F.Faithful] [G.Faithful]
    {X₁ X₂ : C₁} {Y₁ Y₂ : C₃}
    (E : (F.obj X₁ ⟶ F.obj X₂) ≃ (G.obj Y₁ ⟶ G.obj Y₂))
    (h : ∀ α, (∃ f : X₁ ⟶ X₂, F.map f = α) ↔
      ∃ g : Y₁ ⟶ Y₂, G.map g = E α) (f : X₁ ⟶ X₂) :
    G.map (restrictHomEquiv F G E h f) = E (F.map f) :=
  Classical.choose_spec ((h (F.map f)).mp ⟨f, rfl⟩)

end SheafOfModules.CochainInversePairing
