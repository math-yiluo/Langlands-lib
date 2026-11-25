/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelUpperStarUnit
public import WeilConjectures.TateTwist.TateTwistPowerDatum

/-! # The model comparison preserves the named Tate unit datum -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] {X : Scheme.{u}}

/-- The existing unit comparison, with the unit datum fixed independently of
the monoidal instance search in a later importing module. -/
lemma purity_upperStarUnit_tateUnitDatum (f : X ⟶ X) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).map
        (adicSheafEquivCondensedModTensorUnitIso ℓ X).inv ≫
      (adicUpperStarCompCondensedModIso ℓ f).inv.app (AdicSheaf.unit ℓ X) ≫
      (adicSheafEquivCondensedMod ℓ X).functor.map (adicUpperStarUnitIso ℓ f).hom ≫
        (adicSheafEquivCondensedModTensorUnitIso ℓ X).hom = tateUnitDatum ℓ f :=
  upperStar_map_inv_comp_adicUpperStarCompCondensedModIso_inv_app_unit (l := ℓ) f

end AlgebraicGeometry.ProEtale
