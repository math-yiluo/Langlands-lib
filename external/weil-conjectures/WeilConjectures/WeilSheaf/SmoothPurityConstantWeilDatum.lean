/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitDatumTransport
public import WeilConjectures.WeilSheaf.SmoothPurityUnitConstraint
public import WeilConjectures.WeilSheaf.SmoothPurityDescentUnit
public import WeilConjectures.WeilSheaf.ConstantTwistCondensed
import WeilConjectures.Tactic.ExactModProofs

/-! # The constant Weil datum is the canonical pullback-unit datum -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The scalar and tensor comparisons use the same isomorphism on the unit. -/
lemma purity_adicUnitIso_eq_tensorUnitIso (X : Scheme.{u}) :
    adicSheafEquivCondensedModUnitIso l X = adicSheafEquivCondensedModTensorUnitIso l X := by
  apply Iso.ext
  apply Mod.hom_ext
  rw [adicSheafEquivCondensedModUnitIso_hom_hom,
    adicSheafEquivCondensedModTensorUnitIso_hom_hom]

/-- The comparison with condensed modules carries the inverse-pushforward unit
map to the canonical pullback-unit map through the pullback/pushforward isomorphism. -/
lemma purity_adicLowerStarUnit_condensed {X : Scheme.{u}} (e : X ≅ X) :
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) e.inv).map
          (adicSheafEquivCondensedModTensorUnitIso l X).inv ≫
        (adicLowerStarCompCondensedModIso l e.inv).inv.app (AdicSheaf.unit l X) ≫
        (adicSheafEquivCondensedMod l X).functor.map (adicLowerStarUnitIso l e.symm).hom ≫
        (adicSheafEquivCondensedModTensorUnitIso l X).hom =
      (CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj l) e).inv.app
          (𝟙_ _) ≫
        tateUnitDatum l e.hom := by
  have h := purity_unitDatum_transport_of_square (adicSheafEquivCondensedMod l X).functor
    (e.hom)^*ᵃ[l] (e.inv)_*ᵃ[l]
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) e.hom)
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) e.inv)
    (adicUpperStarCompCondensedModIso l e.hom).inv
    (adicLowerStarCompCondensedModIso l e.inv).inv
    (adicUpperStarIsoLowerStarInv l e)
    (CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj l) e)
    (adicSheafEquivCondensedModTensorUnitIso l X)
    (adicUpperStarUnitIso l e.hom).hom (adicLowerStarUnitIso l e.symm).hom
    (tateUnitDatum l e.hom)
    (adicUpperStarCompCondensedModIso_inv_of_iso l e)
    (adicUpperStarIsoLowerStarInv_hom_comp_unit (l := l) e)
    (purity_upperStarUnit_tateUnitDatum l e.hom)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The constant native Weil sheaf has the canonical unit datum in condensed
pullback coordinates. -/
lemma purity_adicConstantCondensedStr_hom :
    (adicConstantCondensedStr k₀ l X).hom =
      (CondensedRing.upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app (𝟙_ _) ≫
        tateUnitDatum l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom := by
  rw [adicConstantCondensedStr_hom, toCondensed_obj_obj_str, adicConstant_obj_str]
  simp only [condensedFrobeniusComparison, Iso.symm_hom,
    purity_adicUnitIso_eq_tensorUnitIso, Category.assoc]
  exact purity_adicLowerStarUnit_condensed l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso

end AlgebraicGeometry.ProEtaleWeilSheaf
