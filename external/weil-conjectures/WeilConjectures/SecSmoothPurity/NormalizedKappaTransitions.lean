/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SecSmoothPurity.NormalizedCoefficientDiagram
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrows

set_option linter.privateModule false

/-! # Normalized coefficient transition formulas

Source: Stacks Project, Modules on Sites, Tags 03CY, 03D2 and 03EL.
(auxiliary; not a blueprint node).

The scalar-extension associator multiplies coefficients. The normalized kappa
comparison transports arbitrary generalized inverse-image sections, and its
inverse contracts the coefficient through the recorded ring square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules
open scoped TensorProduct ChangeOfRings
namespace CategoryTheory.CochainPullback.StrictCoefficient.KappaCalculation

attribute [local irreducible] extensionAdjunction
attribute [local irreducible] generator
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
set_option Elab.async false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem extension_unit {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M : Modules A) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((extensionAdjunction a).unit.app M).val.app U x = extensionTmul a M U 1 x := by
  unfold extensionAdjunction
  exact (Classical.choose_spec (extensionAdjunction_existsUnique a)).1 M U x

private theorem extension_smul {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M : Modules A) (U : Cᵒᵖ) (b : B.obj.obj U) (x : M.val.obj U) :
    extensionTmul a M U b x = b • extensionTmul a M U 1 x := by
  let t := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
      (changeOfRingsPresheaf a M)).app U
  have h := t.hom.map_smul b ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)
  change t ((b * 1) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) =
    b • t ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) at h
  simpa only [mul_one, extensionTmul, extensionFunctor, SheafOfModules.changeOfRings] using h

private theorem extension_map {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {M N : Modules A} (f : M ⟶ N) (U : Cᵒᵖ) (b : B.obj.obj U) (x : M.val.obj U) :
    ((extensionFunctor a).map f).val.app U (extensionTmul a M U b x) =
      extensionTmul a N U b (f.val.app U x) := by
  have h := congrArg (fun z ↦ z.val.app U x) ((extensionAdjunction a).unit.naturality f)
  change ((extensionAdjunction a).unit.app N).val.app U (f.val.app U x) =
    ((extensionFunctor a).map f).val.app U
      (((extensionAdjunction a).unit.app M).val.app U x) at h
  rw [extension_unit, extension_unit] at h
  rw [extension_smul a M, extension_smul a N, map_smul, h]

attribute [local irreducible] extensionFunctor

end CategoryTheory.CochainPullback.StrictCoefficient.KappaCalculation
