/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData

import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece

/-! # Invertibility of the derived open-extension unit -/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

universe u

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall in
/-- The derived open-extension unit is invertible.

Source: Stacks Tags 03DI and 08BS; the slice-presentation and subterminality
argument used in `openProjectionInverse_isIso`.
(blueprint: lem-sf-ring-open-map-open-unit).

Proof: identify `openExtension` with a localized module extension on the
pro-etale slice. The localized module extension has invertible unit by
subterminality. Transport full faithfulness across the slice presentation and
apply `Adjunction.unit_isIso_of_L_fully_faithful` to the specified derived
adjunction. This applies to empty and identity open immersions as well. -/
theorem openDerivedAdjunction_unit_isIso
    (R : Coefficients.{u}) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] :
    IsIso (openDerivedAdjunction R j).unit := by
  obtain ⟨e, ⟨he⟩⟩ := proEtaleOpen_slicePresentation j (R.ring V) (R.ring U) (R.pull j)
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let he' := Functor.mapDerivedCategoryNatIso he ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  let L := (SheafOfModules.localizedModuleExtension.{u} (R.ring V)
    (ProEt.mk j)).mapDerivedCategory
  let adjL := SheafOfModules.localizedModuleDerivedAdjunction.{u} (R.ring V) (ProEt.mk j)
  have : IsIso adjL.unit := SheafOfModules.localizedDerivedUnit_isIso j (R.ring V)
  have : L.Full := adjL.fullyFaithfulLOfIsIsoUnit.full
  have : L.Faithful := adjL.fullyFaithfulLOfIsIsoUnit.faithful
  have : (openExtension R j).mapDerivedCategory.Full := Functor.Full.of_iso he'.symm
  have : (openExtension R j).mapDerivedCategory.Faithful := Functor.Faithful.of_iso he'.symm
  exact (openDerivedAdjunction R j).unit_isIso_of_L_fully_faithful

end WeilConjectures.PurCompactSupport
