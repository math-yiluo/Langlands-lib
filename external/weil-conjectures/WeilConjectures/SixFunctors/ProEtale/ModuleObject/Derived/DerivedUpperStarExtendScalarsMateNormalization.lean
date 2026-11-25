/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarCompNormalization
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullCounit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompNatIsoCounit

/-! The one-arrow derived scalar pullback mate normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
  (a : A ⟶ B) [IsMonHom a]

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Mod.derivedExtendMapDerivedCategoryAdjunction

private theorem derived_unique_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    {q : C ⥤ D} {F : C ⥤ E} (W : MorphismProperty C) [q.IsLocalization W]
    (LF LF' : D ⥤ E) (c : q ⋙ LF ⟶ F) (c' : q ⋙ LF' ⟶ F)
    [LF.IsLeftDerivedFunctor c W] [LF'.IsLeftDerivedFunctor c' W] (K : C) :
    (Functor.leftDerivedUnique LF' LF c c' W).hom.app (q.obj K) ≫ c'.app K = c.app K := by
  simpa only [Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
    Functor.leftDerivedNatTrans_app LF LF' c c' W (𝟙 _) K

private theorem Qh_mapHomotopyCategoryCompIso_refl_hom_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Abelian E] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K) =
      𝟙 _ := by
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  exact DerivedCategory.Qh.map_id _

private theorem comp_Qh_mapHomotopyCategoryCompIso_refl_hom_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Abelian E] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) {X : DerivedCategory E}
    (f : X ⟶ DerivedCategory.Qh.obj
      ((F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ)).obj K)) :
    f ≫ DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K) =
      f := by
  rw [Qh_mapHomotopyCategoryCompIso_refl_hom_app]
  exact Category.comp_id f

private theorem Qh_mapHomotopyCategoryCompIso_refl_hom_app_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Abelian E] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) {X : DerivedCategory E}
    (f : DerivedCategory.Qh.obj (((F ⋙ G).mapHomotopyCategory (.up ℤ)).obj K) ⟶ X) :
    DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K) ≫ f =
      f := by
  rw [Qh_mapHomotopyCategoryCompIso_refl_hom_app]
  exact Category.id_comp f

/-- The specified nonflat derived scalar pullback comparison has the specified restriction mate.

Source: proof step 2 of `lem-sp-original-integral-finite-quotient-mate-transport`, above
`def-exchange-projection` in the latest blueprint.

Proof in words. Apply the existing derived mate/counit theorem to the underived identity
`mateEquiv_pullIso_hom`. The scalar adjunction counits have the required normalization
on Qh. For the left comparison, expand the chosen construction of the derived scalar
pullback isomorphism. Derived natural-transformation counit compatibility handles its
underived comparison factor, and uniqueness of left derived functors handles its two
exact composition factors. Naturality moves scalar transitivity to the complex input.
Factor the underived comparison into scalar transitivity and pullIso, apply
`scalarCompNormalization`, and cancel transitivity with its inverse. The last factor is
the counit equation for `leftDerivedUpperStarIso`. This one-arrow calculation has no
properness, constructibility, or nonzero-ring hypothesis.
(blueprint: lem-sp-derived-upper-star-extend-scalars-mate-normalization) -/
theorem derivedUpperStarExtendScalarsMateNormalization {U V : Scheme.{u}} (h : U ⟶ V) :
    mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a V))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
      (TwoSquare.mk _ _ _ _ (derivedUpperStarExtendScalarsIso a h).hom) =
      (derivedComapLeftDerivedUpperStarIso a h).hom := by
  let β := (pullIso a h).symm
  let e := (comapUpperStarIso a h).symm
  let Lβ := (derivedUpperStarExtendScalarsIso a h).symm
  let Γ := derivedComapLeftDerivedUpperStarIso a h
  refine Adjunction.mateEquiv_leftDerived_inv_eq
    (Mod.extendRestrictAdjunction (coefficientMap a V))
    (Mod.extendRestrictAdjunction (coefficientMap a U)) β e
    (mateEquiv_pullIso_hom a h)
    (Functor.mapHomotopyCategoryCompNatIso (pullIso a h) _).symm
    (Functor.mapHomotopyCategoryCompNatIso_hom (pullIso a h) _)
    _ _ _ _
    ((h)^*⟦A⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac)
    _ _ ((h)^*⟦B⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a V))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq _)
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq _)
    Lβ _ rfl _ rfl (fun K => ?_) Γ (by rfl)
  simp only [Lβ, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.mapHomotopyCategoryCompNatIso_hom,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  simpa only [comp_Qh_mapHomotopyCategoryCompIso_refl_hom_app,
    Qh_mapHomotopyCategoryCompIso_refl_hom_app_comp] using
    derivedUpperStarExtendScalarsIso_hom_app_comp_counit a h K


end AlgebraicGeometry.ProEtale.CondensedRing
