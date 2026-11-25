/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeBaseChange.NativeBaseChangeForgetComparison
import all WeilConjectures.AlgebraicGeometry.NativeBaseChange.NativeBaseChangeForgetComparison
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonUnit
public import WeilConjectures.WeilSheaf.Localization

/-!
# Forgetting the Weil structure and the units of `f^* ⊣ Rf_*`

For a morphism `f : X ⟶ Y` of `k₀`-schemes, forgetting the Weil structures carries the unit
`K ⟶ Rf_* f^* K` of the derived adjunction of pro-étale Weil sheaves to the unit of the derived
adjunction `f̄^* ⊣ Rf̄_*` of `ℓ`-adic sheaves on the geometric fibres, up to the comparison
isomorphisms `AlgebraicGeometry.NativeBaseChange.pullForget` and
`AlgebraicGeometry.NativeBaseChange.pushForget`
(`AlgebraicGeometry.NativeBaseChange.forget_map_unit_app_comp_pushForget_hom_app`). Since
forgetting the Weil structures reflects isomorphisms, the unit is invertible at `K` as soon as the
geometric unit is invertible at the underlying complex of `K`
(`AlgebraicGeometry.NativeBaseChange.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isIso`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Endofunctor

namespace AlgebraicGeometry.NativeBaseChange

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]

/-- The direct-image forgetting comparison `AlgebraicGeometry.NativeBaseChange.pushForget` is the
mate of the inverse of the pullback forgetting comparison
`AlgebraicGeometry.NativeBaseChange.pullForget` (the public form of the private lemma
`AlgebraicGeometry.NativeBaseChange.pushForget_mate`). -/
theorem mateEquiv_pullForget_inv :
    (mateEquiv
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f))
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ f)))
      (TwoSquare.mk _ _ _ _ (pullForget k₀ l f).inv)) =
        (pushForget k₀ l f).hom :=
  pushForget_mate k₀ l f

/-- **Forgetting the Weil structure carries the unit to the geometric unit**: the image under the
forgetful functor of the unit `K ⟶ Rf_* f^* K` of pro-étale Weil sheaves, followed by the
comparisons `pushForget` and `pullForget`, is the unit of the derived adjunction `f̄^* ⊣ Rf̄_*`
of `ℓ`-adic sheaves on the geometric fibres at the underlying complex of `K`. -/
theorem forget_map_unit_app_comp_pushForget_hom_app
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :
    (forget k₀ l Y).map ((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l f).unit.app
        K) ≫
      (pushForget k₀ l f).hom.app ((ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory.obj K) ≫
      (ProEtale.adicLowerStar l (geometricMap k₀ f)).rightDerivedFunctor.map
        ((pullForget k₀ l f).hom.app K) =
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ f))).unit.app
        ((forget k₀ l Y).obj K) := by
  refine Adjunction.map_unit_comp_eq_unit _ _ (pullForget k₀ l f) (pushForget k₀ l f).hom
    (fun M ↦ ?_) K
  have hc := mateEquiv_counit
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f))
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ f)))
    (TwoSquare.mk _ _ _ _ (pullForget k₀ l f).inv) M
  have hβ := NatTrans.congr_app (mateEquiv_pullForget_inv k₀ l f) M
  erw [hβ] at hc
  erw [hc, Iso.hom_inv_id_app_assoc]
  rfl

/-- The unit `K ⟶ Rf_* f^* K` of the derived adjunction of pro-étale Weil sheaves is invertible as
soon as the unit of the derived adjunction `f̄^* ⊣ Rf̄_*` of `ℓ`-adic sheaves on the geometric
fibres is invertible at the underlying complex of `K`. -/
theorem isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isIso
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l Y))
    (h : IsIso ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ f))).unit.app
        ((forget k₀ l Y).obj K))) :
    IsIso ((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l f).unit.app K) := by
  rw [← forget_map_unit_app_comp_pushForget_hom_app] at h
  have : IsIso ((forget k₀ l Y).map
      ((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l f).unit.app K)) :=
    IsIso.of_isIso_comp_right _ ((pushForget k₀ l f).hom.app _ ≫
      (ProEtale.adicLowerStar l (geometricMap k₀ f)).rightDerivedFunctor.map
        ((pullForget k₀ l f).hom.app K))
  exact IsoAlgebra.isIso_of_isIso_forget_mapDerivedCategory_map _

end AlgebraicGeometry.NativeBaseChange
