/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.StrictCoefficient.NormalizedCoefficientDiagramSupplement
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement

/-! # Normalized coefficient transition formulas

Source: Stacks Project, Modules on Sites, Tags 03CY, 03D2 and 03EL.
(blueprint: lem-pur-normalized-kappa-transition-calculus).

The scalar-extension associator multiplies coefficients. The normalized kappa
comparison transports arbitrary generalized inverse-image sections, and its
inverse contracts the coefficient through the recorded ring square.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


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

attribute [local irreducible] scalarComp scalarUnit extensionAdjunction
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

private theorem extension_hom_ext {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M : Modules A) (N : Modules B) {f g : (extensionFunctor a).obj M ⟶ N}
    (h : ∀ U x, f.val.app U (extensionTmul a M U 1 x) =
      g.val.app U (extensionTmul a M U 1 x)) : f = g := by
  apply ((extensionAdjunction a).homEquiv M N).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  change f.val.app U (((extensionAdjunction a).unit.app M).val.app U x) =
    g.val.app U (((extensionAdjunction a).unit.app M).val.app U x)
  simpa only [extension_unit] using h U x

private theorem scalarComp_unit {A B H : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (b : B ⟶ H) (c : A ⟶ H) (hc : c = a ≫ b)
    (P : Complex A) (p : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) :
    (((scalarComp a b c hc).hom.app P).f p).val.app U
      (extensionTmul b ((extensionFunctor a).obj (P.X p)) U 1
        (extensionTmul a (P.X p) U 1 x)) = extensionTmul c (P.X p) U 1 x := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((extensionAdjunction a).comp (extensionAdjunction b)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition a b c hc))
    (extensionAdjunction c) (P.X p)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  have h' := congrArg (fun z ↦ z.val.app U x) h
  change (((extensionAdjunction a).homEquiv (P.X p) _
    ((extensionAdjunction b).homEquiv _ _
      ((Adjunction.leftAdjointUniq
        (((extensionAdjunction a).comp (extensionAdjunction b)).ofNatIsoRight
          (SheafOfModules.systemScalarRestrictionComposition a b c hc))
        (extensionAdjunction c)).hom.app (P.X p)))).val.app U x) =
    ((extensionAdjunction c).unit.app (P.X p)).val.app U x at h'
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at h'
  unfold scalarComp
  dsimp only [NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex]
  change ((Adjunction.leftAdjointUniq
    (((extensionAdjunction a).comp (extensionAdjunction b)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition a b c hc))
    (extensionAdjunction c)).hom.app (P.X p)).val.app U
    (((extensionAdjunction b).unit.app ((extensionFunctor a).obj (P.X p))).val.app U
      (((extensionAdjunction a).unit.app (P.X p)).val.app U x)) =
    ((extensionAdjunction c).unit.app (P.X p)).val.app U x at h'
  rw [extension_unit, extension_unit, extension_unit] at h'
  change ((Adjunction.leftAdjointUniq
    (((extensionAdjunction a).comp (extensionAdjunction b)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition a b c hc))
    (extensionAdjunction c)).hom.app (P.X p)).val.app U
      (extensionTmul b ((extensionFunctor a).obj (P.X p)) U 1
        (extensionTmul a (P.X p) U 1 x)) = extensionTmul c (P.X p) U 1 x
  exact h'

attribute [local irreducible] extensionFunctor Comparisons.pullArrow squareArrow

end CategoryTheory.CochainPullback.StrictCoefficient.KappaCalculation
