/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMateIsIso
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Forgetting the Weil structure commutes with the derived pushforward, as a base change map

Let `p : Z ⟶ Y` be a morphism of `k₀`-schemes, with base change `p̄ : Z̄ ⟶ Ȳ` to the geometric
fibers. The forgetful functors `U : D(ProEtaleWeilSheaf) ⥤ D(AdicSheaf)` commute with the
pullbacks, `α : U_Y ⋙ D(p̄^*) ≅ D(p^*) ⋙ U_Z`
(`AlgebraicGeometry.ProEtaleWeilSheaf.forgetCompUpperStarIso`), the pullback of a pro-étale
Weil sheaf having underlying sheaf the pullback of the underlying sheaf. The mate of `α` under
the derived adjunctions `D(p^*) ⊣ Rp_*` and `D(p̄^*) ⊣ Rp̄_*` is the derived base change map
`U_Y (Rp_* M) ⟶ Rp̄_* (U_Z M)`, and it is an isomorphism for every `M`
(`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_mateEquiv_forgetCompUpperStarIso_app`).

The underived base change map `U_Y (p_* F) ⟶ p̄_* (U_Z F)` is the identity, the adjunction
`p^* ⊣ p_*` of pro-étale Weil sheaves having the unit and the counit of `p̄^* ⊣ p̄_*`; and
`U_Z` preserves K-injective complexes, having an exact left adjoint
(`CategoryTheory.Endofunctor.IsoAlgebra.preservesKInjectiveComplexes_forget`). So the claim is
`CategoryTheory.Adjunction.isIso_derivedBaseChange_app`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

namespace ProEtaleWeilSheaf

variable (k₀ l) (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

/-- The forgetful functors from pro-étale Weil sheaves commute with the pullbacks:
`U_Y ⋙ p̄^* ≅ p^* ⋙ U_Z`, the pullback of a pro-étale Weil sheaf having underlying sheaf the
pullback of the underlying sheaf. -/
noncomputable def forgetCompAdicUpperStarIso :
    IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y) ⋙
        (Scheme.Hom.geometricFiberMap p (comp_over p _))^*ᵃ[l] ≅
      ProEtaleWeilSheaf.upperStar k₀ l p ⋙
        IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z) :=
  Iso.refl _

omit [Fact (ringChar k₀ ≠ l)] in
/-- The underived base change map `p_* ⋙ U_Y ⟶ U_Z ⋙ p̄_*` for the forgetful functors from
pro-étale Weil sheaves, the mate of
`AlgebraicGeometry.ProEtaleWeilSheaf.forgetCompAdicUpperStarIso`,
is an isomorphism: it is the identity, the adjunction `p^* ⊣ p_*` having the unit and the
counit of `p̄^* ⊣ p̄_*`. -/
instance isIso_mateEquiv_forgetCompAdicUpperStarIso :
    IsIso (mateEquiv (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l p)
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap p (comp_over p _)))
      (TwoSquare.mk _ _ _ _ (forgetCompAdicUpperStarIso k₀ l p).hom)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  suffices h : (mateEquiv (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l p)
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap p (comp_over p _)))
      (TwoSquare.mk _ _ _ _ (forgetCompAdicUpperStarIso k₀ l p).hom)).app F = 𝟙 _ by
    rw [h]
    infer_instance
  simp only [Functor.comp_obj, IsoAlgebra.forget_obj, mateEquiv_apply, NatTrans.comp_app,
    Functor.id_obj, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.comp_map, IsoAlgebra.forget_map, upperStarLowerStarAdjunction_counit_app_hom_f,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp]
  erw [Category.id_comp]
  exact (ProEtale.adicUpperStarLowerStarAdjunction l
    (Scheme.Hom.geometricFiberMap p (comp_over p _))).right_triangle_components F.carrier

/-- The forgetful functors from the derived categories of pro-étale Weil sheaves commute with
the pullbacks: `α : U_Y ⋙ D(p̄^*) ≅ D(p^*) ⋙ U_Z`, induced by
`AlgebraicGeometry.ProEtaleWeilSheaf.forgetCompAdicUpperStarIso`. -/
noncomputable def forgetCompUpperStarIso :
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory ⋙
        (Scheme.Hom.geometricFiberMap p (comp_over p _))^*ᵃ[l].mapDerivedCategory ≅
      (ProEtaleWeilSheaf.upperStar k₀ l p).mapDerivedCategory ⋙
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (forgetCompAdicUpperStarIso k₀ l p)

omit [Fact (ringChar k₀ ≠ l)] in
/-- **Forgetting the Weil structure commutes with the derived pushforward.** The derived base
change map `U_Y (Rp_* M) ⟶ Rp̄_* (U_Z M)`, the mate of
`AlgebraicGeometry.ProEtaleWeilSheaf.forgetCompUpperStarIso` under the derived adjunctions
`D(p^*) ⊣ Rp_*` and `D(p̄^*) ⊣ Rp̄_*`, is an isomorphism for every complex `M` of pro-étale Weil
sheaves on `Z`. -/
theorem isIso_mateEquiv_forgetCompUpperStarIso_app
    (M : DerivedCategory (ProEtaleWeilSheaf k₀ l Z)) :
    IsIso ((mateEquiv (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l p)
      (ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap p (comp_over p _))).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (forgetCompUpperStarIso k₀ l p).hom)).app M) := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  exact Adjunction.isIso_derivedBaseChange_app _ _ _ M

end ProEtaleWeilSheaf

end AlgebraicGeometry
