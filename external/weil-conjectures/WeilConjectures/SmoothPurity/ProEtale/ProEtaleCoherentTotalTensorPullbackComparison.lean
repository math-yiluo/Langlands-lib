/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedTensorComparisonAssociativity
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleOrdinaryTensorPullbackNaturalComparison
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleTotalTensorPullbackComparisonNormalization

/-! # Coherent natural total tensor pullback comparison
Source: Stacks 03EL and 07A4; signed total tensor, 06YN.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u b vb a va
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.RingedForgetTensorTransposition
namespace WeilConjectures
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso
attribute [local implicit_reducible] coefficientTotalTensor

private theorem inverse_assoc {B : Type b} [Category.{vb} B] [MonoidalCategory B]
    {A : Type a} [Category.{va} A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    (X Y Z : B)
    (h : F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (𝟙 (F.obj X) ⊗ₘ μ.hom.app (Y, Z)) =
      μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ⊗ₘ 𝟙 (F.obj Z)) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom) :
    (μ.inv.app (X, Y) ▷ F.obj Z) ≫ μ.inv.app (X ⊗ Y, Z) ≫ F.map (α_ X Y Z).hom =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        (F.obj X ◁ μ.inv.app (Y, Z)) ≫ μ.inv.app (X, Y ⊗ Z) := by
  apply (cancel_epi (μ.hom.app (X ⊗ Y, Z) ≫
    (μ.hom.app (X, Y) ▷ F.obj Z))).1
  apply (cancel_mono (μ.hom.app (X, Y ⊗ Z) ≫
    (F.obj X ◁ μ.hom.app (Y, Z)))).1
  have hr : (μ.hom.app (X, Y) ▷ F.obj Z) ≫ (μ.inv.app (X, Y) ▷ F.obj Z) = 𝟙 _ := by
    rw [← comp_whiskerRight, Iso.hom_inv_id_app, id_whiskerRight]
  have hl : (F.obj X ◁ μ.inv.app (Y, Z)) ≫ (F.obj X ◁ μ.hom.app (Y, Z)) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app,
      MonoidalCategory.whiskerLeft_id]
  simp only [Category.assoc, reassoc_of% hr, hl,
    Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  erw [Category.comp_id]
  erw [id_tensorHom, tensorHom_id] at h
  exact h

-- Totalization identifies the two standard tensor functor presentations.
/-- The natural total comparison retains its component normalization and associativity.
Source: Stacks 03EL, 07A4 and 06YN
(blueprint: lem-pur-coherent-total-tensor-pullback-comparison).
Proof: take the existing natural total pullback comparison. Its components are the
specified total comparison, hence satisfy the summand formula. Ordinary pullback
associativity gives inverse associativity. The general ringed chain comparison
lemma then proves the asserted equation for every pure-triple model associator. -/
theorem proEtaleCoherentTotalTensorPullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (R' : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ R') :
    let L := proEtaleRingModulePullback f R R' c
    ∃ e : ((L.mapHomologicalComplex (.up ℤ)).prod
        (L.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) R' ≅
      coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology Y) R ⋙
        L.mapHomologicalComplex (.up ℤ),
      (∀ P Q, e.inv.app (P, Q) = (proEtaleTensorPullbackTotalIso f R R' c P Q).inv) ∧
      RingedTensorComparisonCoherence.{u + 1, u, u, u + 1, u, u}
        (Scheme.ProEt.topology Y) R (Scheme.ProEt.topology X) R' L e.symm := by
  let L := proEtaleRingModulePullback f R R' c
  obtain ⟨ν, hμ, hforward⟩ := proEtaleOrdinaryTensorPullbackNaturalComparison f R R' c
  obtain ⟨e, he, hδ⟩ := proEtaleTotalTensorPullbackComparisonNormalization f R R' c ν hμ
  refine ⟨e, he, ?_⟩
  have hν : letI := SheafOfModules.monoidalCategory R
      letI := SheafOfModules.monoidalCategory R'
      ∀ M N H : proEtaleRingModules Y R,
        (ν.inv.app (M, N) ▷ L.obj H) ≫ ν.inv.app (M ⊗ N, H) ≫
            L.map (α_ M N H).hom =
          (α_ (L.obj M) (L.obj N) (L.obj H)).hom ≫
            (L.obj M ◁ ν.inv.app (N, H)) ≫ ν.inv.app (M, N ⊗ H) := by
    intro M N H
    exact inverse_assoc L ν M N H (hforward M N H)
  exact ringed_tensorComparison_associativity.{u + 1, u, u, u + 1, u, u}
    (Scheme.ProEt.topology Y) R (Scheme.ProEt.topology X) R'
    L ν hν e.symm hδ

end WeilConjectures
