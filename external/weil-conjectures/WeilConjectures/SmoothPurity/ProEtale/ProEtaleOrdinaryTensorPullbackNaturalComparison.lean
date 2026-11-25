/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleOrdinaryTensorPullbackAssociativity

/-! # Natural ordinary tensor pullback comparison with associativity
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
  proEtaleOrdinaryTensorPullback

/-- Package the prescribed ordinary comparisons naturally, retaining their associativity.
Source: Stacks 03EL and 07A4
(blueprint: lem-pur-natural-ordinary-tensor-pullback-comparison).
Proof: naturality of the given binary comparisons constructs a natural isomorphism
with exactly those components. Its forward associativity is the ordinary pure-triple
calculation, since evaluation of the constructed natural isomorphism returns the
given comparison. No flatness or derived localization is involved. -/
theorem proEtaleOrdinaryTensorPullbackNaturalComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ R') :
    let L := proEtaleRingModulePullback f R R' c
    ∃ ν : MonoidalCategory.tensor (proEtaleRingModules Y R) ⋙ L ≅
        (L.prod L) ⋙ MonoidalCategory.tensor (proEtaleRingModules X R'),
      (∀ M N, ν.hom.app (M, N) = (proEtaleOrdinaryTensorPullback f R R' c M N).hom) ∧
      letI := SheafOfModules.monoidalCategory R
      letI := SheafOfModules.monoidalCategory R'
      ∀ M N H : proEtaleRingModules Y R,
        L.map (α_ M N H).hom ≫ ν.hom.app (M, N ⊗ H) ≫
            (𝟙 (L.obj M) ⊗ₘ ν.hom.app (N, H)) =
          ν.hom.app (M ⊗ N, H) ≫ (ν.hom.app (M, N) ⊗ₘ 𝟙 (L.obj H)) ≫
            (α_ (L.obj M) (L.obj N) (L.obj H)).hom := by
  let L := proEtaleRingModulePullback f R R' c
  let μ := proEtaleOrdinaryTensorPullback f R R' c
  let ν : MonoidalCategory.tensor (proEtaleRingModules Y R) ⋙ L ≅
      (L.prod L) ⋙ MonoidalCategory.tensor (proEtaleRingModules X R') :=
    NatIso.ofComponents (fun Z ↦ μ Z.1 Z.2) (by
      intro Z W v
      simpa only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj,
        MonoidalCategory.tensor_map, L, μ, proEtaleOrdinaryTensor,
        MonoidalCategory.curriedTensor, MonoidalCategory.tensorHom_def, Category.assoc] using
        proEtaleOrdinaryTensorPullback_naturality f R R'
          c _ _ _ _ v.1 v.2)
  refine ⟨ν, (fun _ _ ↦ rfl), ?_⟩
  intro M N H
  exact proEtaleOrdinaryTensorPullback_associativity f R R' c M N H

end WeilConjectures
