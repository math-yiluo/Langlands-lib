/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

set_option linter.privateModule false

/-! # Localization part of supported cup functoriality

The actual closed/open coefficient sequence is functorial under exact inverse image.
The independent cup algebra and comparison results supply the remaining clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u c v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

set_option allowUnsafeReducibility true in
attribute [local reducible] catToReflQuiver functorialCupSingle
  functorialCupSourceObject functorialCupTarget

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupConstant functorialCupRestriction
  functorialCupFullSupportIso constant constantEtale functorialCupComparisonFunctor

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_full (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    P.functorialCupRestriction pro (𝟙 X) = (P.functorialCupFullSupportIso pro X).inv := by
  cases pro with
  | false =>
    change Etale.closedConstantSectionMap P.Coefficient (𝟙 X) = _
    unfold Etale.closedConstantSectionMap
    rw [(Etale.constantModulePushforwardMap_id_comp P.Coefficient
      (ModuleCat.of P.Coefficient P.Coefficient)).1]
    erw [Category.comp_id]
    rfl
  | true =>
    let : HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient) :=
      P.functorialCupTopologySheafify true X
    let : HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient) :=
      HasSheafify.isRightAdjoint
    let := Scheme.ProEt.isContinuous_overPullback (𝟙 X)
    change ProEtale.cupCoefficientRestriction P (𝟙 X) = _
    have h : ProEtale.cupCoefficientRestriction P (𝟙 X) =
        (ProEtale.cupConstantIso P X).hom ≫
          Functor.LaxMonoidal.ε
            (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 X)) ≫
          (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 X)).map
            (ProEtale.cupConstantIso P X).inv := by
      unfold ProEtale.cupCoefficientRestriction
      congr 1
      congr 1
      apply ((constantSheafAdj (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.isTerminalMkId X)).homEquiv _ _).injective
      rw [Equiv.apply_symm_apply]
      exact (Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (𝟙 X))
        (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.topology X)
        (Scheme.ProEt.topology X) (op (Scheme.ProEt.mk (𝟙 X)))).symm
    rw [h]
    have hε : Functor.LaxMonoidal.ε
        (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 X)) =
        (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).inv.app (𝟙_ _) := by
      let := Scheme.ProEt.isContinuous_overPullback (𝟙 X)
      exact Functor.ε_sheafPushforwardContinuous_of_iso_id
        (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.topology X)
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X)
    erw [hε]
    have hn := (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).inv.naturality
      (ProEtale.cupConstantIso P X).inv
    dsimp only [Functor.id_map] at hn
    calc
      _ = (ProEtale.cupConstantIso P X).hom ≫
          (ProEtale.cupConstantIso P X).inv ≫
          (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).inv.app
            (P.constant X) := congrArg (fun k ↦ (ProEtale.cupConstantIso P X).hom ≫ k)
              hn.symm
      _ = _ := by rw [Iso.hom_inv_id_assoc]; rfl

end WeilConjectures.PurityFiniteSetting
