/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedTensorAssociatorDetection

/-! # Associativity of ordinary pro-étale tensor pullback
Source: Stacks 03EL and 07A4.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction SheafOfModules.tensorObjIsoSheafification
  proEtaleOrdinaryTensorPullback proEtaleRingModuleAdjunction

/-- The unit-normalized ordinary pullback tensor comparison respects reassociation.
Source: Stacks 03EL and 07A4 (blueprint: lem-pur-ordinary-pullback-tensor-associativity).
Proof: take adjuncts, which makes both maps start at the ordinary triple tensor.
Move the source associator through the adjunction unit by naturality. Maps out of
that tensor are determined by local pure triples. The two binary unit formulas,
tensor-map formula, and ordinary associator formula identify both images with
the same reassociated triple of unit sections. -/
theorem proEtaleOrdinaryTensorPullback_associativity {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M N H : proEtaleRingModules Y R) :
    let L := proEtaleRingModulePullback f R S c
    let μ := proEtaleOrdinaryTensorPullback f R S c
    L.map (α_ M N H).hom ≫ (μ M (N ⊗ H)).hom ≫
      (𝟙 (L.obj M) ⊗ₘ (μ N H).hom) =
    (μ (M ⊗ N) H).hom ≫ ((μ M N).hom ⊗ₘ 𝟙 (L.obj H)) ≫
      (α_ (L.obj M) (L.obj N) (L.obj H)).hom := by
  let L := proEtaleRingModulePullback f R S c
  let μ := proEtaleOrdinaryTensorPullback f R S c
  let adj := proEtaleRingModuleAdjunction f R S c
  have hμ (A B : proEtaleRingModules Y R) (U : Y.ProEt)
      (x : A.val.obj (Opposite.op U)) (y : B.val.obj (Opposite.op U)) :
      (μ A B).hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          ((adj.unit.app (A ⊗ B)).val.app (Opposite.op U)
            (proEtaleTensorPair Y R A B (Opposite.op U) x y)) =
        proEtaleTensorPair X S (L.obj A) (L.obj B)
          (Opposite.op ((proEtaleBaseChange f).obj U))
          ((adj.unit.app A).val.app (Opposite.op U) x)
          ((adj.unit.app B).val.app (Opposite.op U) y) := by
    dsimp only [μ, L, adj]
    unfold proEtaleOrdinaryTensorPullback
    exact (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists.choose_spec.2
      A B U x y
  have hpure (W : Scheme.{u}) (A : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
      (M N H : proEtaleRingModules W A) (U : W.ProEtᵒᵖ)
      (x : M.val.obj U) (y : N.val.obj U) (z : H.val.obj U) :
      (α_ M N H).hom.val.app U
        (proEtaleTensorPair W A (M ⊗ N) H U
          (proEtaleTensorPair W A M N U x y) z) =
      proEtaleTensorPair W A M (N ⊗ H) U x
        (proEtaleTensorPair W A N H U y z) := by
    unfold proEtaleTensorPair
    exact CochainPullback.moduleTmul_associator M N H U x y z
  have hmap (W : Scheme.{u}) (A : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
      {M M' N N' : proEtaleRingModules W A} (a : M ⟶ M') (b : N ⟶ N')
      (U : W.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
      (a ⊗ₘ b).val.app U (proEtaleTensorPair W A M N U x y) =
        proEtaleTensorPair W A M' N' U (a.val.app U x) (b.val.app U y) := by
    unfold proEtaleTensorPair
    exact CochainPullback.moduleTmul_map a b U x y
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  have hu := adj.unit.naturality (α_ M N H).hom
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← Category.assoc, ← hu]
  apply RingedForgetTensorTransposition.pure_ext₃.{u+1, u, u} (ProEt.topology Y) R M N H _
  intro U x y z
  let V := Opposite.op ((proEtaleBaseChange f).obj U.unop)
  change ((𝟙 (L.obj M) ⊗ₘ (μ N H).hom).val.app V)
      ((μ M (N ⊗ H)).hom.val.app V
        ((adj.unit.app (M ⊗ (N ⊗ H))).val.app U
          ((α_ M N H).hom.val.app U
            (proEtaleTensorPair Y R (M ⊗ N) H U
              (proEtaleTensorPair Y R M N U x y) z)))) =
    (α_ (L.obj M) (L.obj N) (L.obj H)).hom.val.app V
      (((μ M N).hom ⊗ₘ 𝟙 (L.obj H)).val.app V
        ((μ (M ⊗ N) H).hom.val.app V
          ((adj.unit.app ((M ⊗ N) ⊗ H)).val.app U
            (proEtaleTensorPair Y R (M ⊗ N) H U
              (proEtaleTensorPair Y R M N U x y) z))))
  rw [hpure Y R M N H U x y z]
  erw [hμ, hμ]
  erw [hmap, hmap]
  dsimp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  rw [hμ N H U.unop y z, hμ M N U.unop x y]
  exact (hpure X S (L.obj M) (L.obj N) (L.obj H) V _ _ _).symm

end WeilConjectures
