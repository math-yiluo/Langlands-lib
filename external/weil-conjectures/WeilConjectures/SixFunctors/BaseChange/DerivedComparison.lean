/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-!
# The two derived base-change morphisms agree

For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

this repository constructs the derived base-change morphism `g^* Rf_* ⟶ Rf'_* g'^*` on the
bounded below derived categories twice:

- `AlgebraicGeometry.Etale.baseChange`, the composite of the unit of `Lf'^* ⊣ Rf'_*`, the
  pullback comparison `θ_sq` and the counit of `Lf^* ⊣ Rf_*`, that is, the mate of `θ_sq`;
- `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, the natural transformation out of the
  right derived functor which is computed by the underived base change map on complexes.

This file shows that they are equal
(`AlgebraicGeometry.Etale.baseChange_eq_derivedBaseChangeMapPlus`), so that the pasting laws
and the computations available for `derivedBaseChangeMapPlus` apply to `baseChange`. The
proof identifies the derived adjunction used by `baseChange` with `Adjunction.derivedPlus`
(`Adjunction.derivedAdjunctionPlus_eq_derivedPlus`), computes `θ_sq` on complexes
(`AlgebraicGeometry.Etale.pullbackSquareComparison_hom_app_factorsh`) and applies the
general computation of derived mates `Adjunction.derivedPlus_mateEquiv_app_fac`. In particular
`AlgebraicGeometry.Etale.baseChange` commutes with the shifts
(`AlgebraicGeometry.Etale.commShift_baseChange`).

This is the identification of the base-change map of blueprint
`definition-derived-base-change-map--1` with the derived exchange morphism of the proper base change
chapter.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

omit [HasSmallSiteSheafify A] in
/-- The composition isomorphism `AlgebraicGeometry.Etale.upperStarCompDerivedPlus` along a
morphism `h₁₂` equal to `h₁ ≫ h₂` is the one along `h₁ ≫ h₂`, transported along the equality. -/
lemma Etale.upperStarCompDerivedPlus_eq_eqToIso_trans {T S R : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂) :
    Etale.upperStarCompDerivedPlus A h₁ h₂ h₁₂ hh₁₂ =
      eqToIso (by rw [hh₁₂]) ≪≫ Etale.upperStarPlusComp A h₁ h₂ := by
  subst hh₁₂
  ext K
  simp [Etale.upperStarCompDerivedPlus, Etale.upperStarPlusComp]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

omit [HasSmallSiteSheafify A] in
/-- The pullback comparison `θ_sq` of a commutative square is the composite of the inverse of the
composition isomorphism along `f' ≫ g` and the composition isomorphism along `g' ≫ f`, both taken
along the diagonal `g' ≫ f`. -/
lemma Etale.pullbackSquareComparison_eq (sq : CommSq g' f' f g) :
    Etale.pullbackSquareComparison A sq =
      (Etale.upperStarCompDerivedPlus A f' g (g' ≫ f) sq.w).symm ≪≫
        Etale.upperStarCompDerivedPlus A g' f := by
  apply Iso.ext
  rw [Etale.upperStarCompDerivedPlus_eq_eqToIso_trans A f' g (g' ≫ f) sq.w]
  simp only [Etale.pullbackSquareComparison, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    eqToIso.inv, eqToIso.hom, Category.assoc]
  rfl

omit [HasSmallSiteSheafify A] in
/-- **The pullback comparison is computed by the underived square isomorphism on complexes**:
on the image of a bounded below complex `N`, the comparison `θ_sq` of the derived pullbacks is
the square isomorphism `AlgebraicGeometry.Etale.squareUpperStarIso` applied levelwise, modulo
the isomorphisms `Functor.mapDerivedCategoryPlusFactorsh`. -/
lemma Etale.pullbackSquareComparison_hom_app_factorsh (sq : CommSq g' f' f g)
    (N : HomotopyCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
    (Etale.pullbackSquareComparison A sq).hom.app (DerivedCategory.Plus.Qh.obj N) ≫
        ((g')^*[A]).mapDerivedCategoryPlus.map
          (((f)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        ((g')^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((f)^*[A]).mapHomotopyCategoryPlus.obj N) =
      ((f')^*[A]).mapDerivedCategoryPlus.map
          (((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        ((f')^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((g)^*[A]).mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.squareUpperStarIso A sq).hom).app N) := by
  have h₁ := Etale.upperStarCompDerivedPlus_hom_app_factorsh A f' g (g' ≫ f) sq.w N
  have h₂ := Etale.upperStarCompDerivedPlus_hom_app_factorsh A g' f (g' ≫ f) rfl N
  have h₁' : ((f')^*[A]).mapDerivedCategoryPlus.map
        (((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app N) ≫
      ((f')^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((g)^*[A]).mapHomotopyCategoryPlus.obj N) =
      (Etale.upperStarCompDerivedPlus A f' g (g' ≫ f) sq.w).inv.app
          (DerivedCategory.Plus.Qh.obj N) ≫
        ((g' ≫ f)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app N ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A f' g (g' ≫ f) sq.w).hom).app N) := by
    rw [← h₁, Iso.inv_hom_id_app_assoc]
  have hσ : DerivedCategory.Plus.Qh.map
      ((NatTrans.mapHomotopyCategoryPlus (Etale.squareUpperStarIso A sq).hom).app N) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A f' g (g' ≫ f) sq.w).inv).app N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A g' f (g' ≫ f) rfl).hom).app N) := by
    rw [← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp]
    rfl
  have hc : DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A f' g (g' ≫ f) sq.w).hom).app N) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.upperStarComp A f' g (g' ≫ f) sq.w).inv).app N) = 𝟙 _ := by
    rw [← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp,
      Iso.hom_inv_id, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
  rw [Etale.pullbackSquareComparison_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, h₂]
  erw [reassoc_of% h₁', hσ, reassoc_of% hc]

section

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

omit [HasSmallSiteSheafify A] in
/-- The bounded below derived adjunction `Lf^* ⊣ Rf_*` obtained by restricting the unbounded
one is the bounded below derived adjunction `Adjunction.derivedPlus`. -/
lemma Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus (f : X ⟶ Y) :
    Etale.derivedUpperStarLowerStarAdjunctionPlus A f =
      (Etale.upperStarLowerStarAdjunction A f).derivedPlus :=
  (Etale.upperStarLowerStarAdjunction A f).derivedAdjunctionPlus_eq_derivedPlus

omit [HasSmallSiteSheafify A] in
/-- The derived base-change morphism `AlgebraicGeometry.Etale.baseChange` is the mate of the
pullback comparison `θ_sq` with respect to the derived adjunctions `Lf^* ⊣ Rf_*` and
`Lf'^* ⊣ Rf'_*`. -/
lemma Etale.baseChange_app_eq_mateEquiv (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.baseChange A sq).app K =
      (mateEquiv (Etale.upperStarLowerStarAdjunction A f).derivedPlus
        (Etale.upperStarLowerStarAdjunction A f').derivedPlus
        (TwoSquare.mk _ _ _ _ (Etale.pullbackSquareComparison A sq).hom)).app K := by
  rw [Etale.baseChange_app, Etale.baseChangeUnitStep_app, Etale.baseChangeSquareStep_hom_app,
    Etale.baseChangeCounitStep_app, Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus]
  simp [mateEquiv_apply]

omit [HasSmallSiteSheafify A] in
/-- **The two derived base-change morphisms agree.** The derived base-change morphism
`AlgebraicGeometry.Etale.baseChange`, built from the units and counits of the derived
adjunctions, is the derived base change map `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`,
characterised by being computed by the underived base change map on complexes.
(blueprint: `definition-derived-base-change-map`) -/
theorem Etale.baseChange_eq_derivedBaseChangeMapPlus (sq : CommSq g' f' f g) :
    Etale.baseChange A sq = Etale.derivedBaseChangeMapPlus A sq := by
  refine Etale.derivedBaseChangeMapPlus_ext A sq _ fun K => ?_
  rw [Etale.baseChange_app_eq_mateEquiv]
  exact Adjunction.derivedPlus_mateEquiv_app_fac (Etale.upperStarLowerStarAdjunction A f)
    (Etale.upperStarLowerStarAdjunction A f')
    (TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq).hom)
    (TwoSquare.mk _ _ _ _ (Etale.pullbackSquareComparison A sq).hom)
    (Etale.pullbackSquareComparison_hom_app_factorsh A sq) K

omit [HasSmallSiteSheafify A] in
/-- The derived base-change morphism `AlgebraicGeometry.Etale.baseChange` commutes with the
shifts: it is `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`
(`AlgebraicGeometry.Etale.commShift_derivedBaseChangeMapPlus`). -/
instance Etale.commShift_baseChange (sq : CommSq g' f' f g) :
    NatTrans.CommShift (Etale.baseChange A sq) ℤ := by
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  infer_instance

end

end AlgebraicGeometry
