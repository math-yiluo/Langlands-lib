/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.PushHomComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# Compatibility of the (Push) comparison with the composition of coefficient changes

Let `a : Λ ⟶ Λ'` and `b : Λ' ⟶ Λ''` be morphisms of commutative condensed rings, with composite
`c = a ≫ b`, along which the coefficient changes are flat, and `f : X ⟶ Y` a morphism of
schemes. The (Push) comparisons `Rf_* ⋙ T^Y ⟶ T^X ⋙ Rf_*`
(`ProEtale.CondensedRing.derivedPushHom`) compose: the comparison for `c` is the composite of the
comparisons for `a` and `b`, up to the transitivity isomorphisms
`T_c ≅ T_a ⋙ T_b` of the derived extensions of scalars (`Mod.derivedExtendScalarsCompIso`)
(`ProEtale.CondensedRing.derivedPushHom_comp_app`).

This is formal: the transitivity isomorphisms are the conjugates of the composition isomorphisms
of the restrictions of scalars, so by `Adjunction.pushHomOfComapIso_app_eq_comp` it suffices that
the isomorphisms `Rf_* ⋙ D(Res) ≅ D(Res) ⋙ Rf_*` (`ProEtale.CondensedRing.derivedComapLowerStarIso`)
compose (`ProEtale.CondensedRing.derivedComapLowerStarIso_hom_app_comp`). These are the right
derived isomorphisms of the strict isomorphisms `ProEtale.CondensedRing.comapLowerStarIso`, which
compose on the nose (`ProEtale.CondensedRing.comapLowerStarIso_hom_app_of_comp_eq`), and the derived
isomorphisms compose by `Functor.rightDerivedFunctorCommIso_hom_app_comp`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b] (c : Λ ⟶ Λ'') [IsMonHom c]

omit [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] [MonObj Λ''] [IsCommMonObj Λ'']
  [IsMonHom a] [IsMonHom b] [IsMonHom c] in
/-- The coefficient changes compose: `a_X ≫ b_X = c_X` for `a ≫ b = c`. -/
lemma coefficientMap_comp_eq (hc : a ≫ b = c) (X : Scheme.{u}) :
    coefficientMap a X ≫ coefficientMap b X = coefficientMap c X := by
  rw [← coefficientMap_comp, hc]

/-- The composition isomorphism `Res_b ⋙ Res_a ≅ Res_c` of the restrictions of scalars along the
coefficient changes, for `a ≫ b = c`. -/
noncomputable abbrev comapCoefficientMapCompIso (hc : a ≫ b = c) (X : Scheme.{u}) :
    (Mod.comap (coefficientMap b X) :
        Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ'' X) ⥤
          Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) ⋙
        Mod.comap (coefficientMap a X) ≅ Mod.comap (coefficientMap c X) :=
  (Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
    Mod.comapCongr (coefficientMap_comp_eq a b c hc X)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] [IsCommMonObj Λ''] in
/-- The isomorphisms `f_* ⋙ Res ≅ Res ⋙ f_*` compose: the one for `c = a ≫ b` is the composite of
those for `a` and `b`. All of them are the identity on the underlying sheaves. -/
lemma comapLowerStarIso_hom_app_of_comp_eq (hc : a ≫ b = c)
    (K : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ'' X)) :
    (comapLowerStarIso c f).hom.app K =
      (comapCoefficientMapCompIso a b c hc Y).inv.app ((f)_*⟦Λ''⟧.obj K) ≫
        (Mod.comap (coefficientMap a Y)).map ((comapLowerStarIso b f).hom.app K) ≫
        (comapLowerStarIso a f).hom.app ((Mod.comap (coefficientMap b X)).obj K) ≫
        (f)_*⟦Λ⟧.map ((comapCoefficientMapCompIso a b c hc X).hom.app K) := by
  apply Mod.hom_ext
  simp only [lowerStar, Functor.comp_obj, comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom,
    Iso.trans_inv, Mod.comapCongr, Iso.symm_inv, NatTrans.comp_app, NatIso.ofComponents_inv_app,
    Iso.trans_hom, Iso.symm_hom, NatIso.ofComponents_hom_app, Functor.comp_map, Functor.mapMod_map,
    Mod.comp_hom', Mod.comapComp_inv_app_hom, Mod.isoMk_hom_hom, Iso.refl_hom, Category.comp_id,
    Category.assoc, Mod.isoMk_inv_hom, Iso.refl_inv, Mod.comapComp_hom_app_hom, Mod.comap_map_hom,
    Mod.homMk_hom]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.id_comp,
    Category.id_comp]
  rfl


section Derived

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b X))]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap c X))]

omit [IsCommMonObj Λ''] in
/-- The isomorphisms `Rf_* ⋙ D(Res) ≅ D(Res) ⋙ Rf_*` compose: the one for `c = a ≫ b` is the
composite of those for `a` and `b`, up to the composition isomorphisms
`Mod.mapDerivedCategoryComapCompIso` of the restrictions of scalars. -/
theorem derivedComapLowerStarIso_hom_app_comp (hc : a ≫ b = c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ'' X))) :
    (derivedComapLowerStarIso c f).hom.app K =
      (Mod.mapDerivedCategoryComapCompIso (coefficientMap a Y) (coefficientMap b Y)
          (coefficientMap c Y) (coefficientMap_comp_eq a b c hc Y)).inv.app
          (R((f)_*⟦Λ''⟧).obj K) ≫
        D(Mod.comap (coefficientMap a Y)).map ((derivedComapLowerStarIso b f).hom.app K) ≫
        (derivedComapLowerStarIso a f).hom.app (D(Mod.comap (coefficientMap b X)).obj K) ≫
        R((f)_*⟦Λ⟧).map ((Mod.mapDerivedCategoryComapCompIso (coefficientMap a X)
          (coefficientMap b X) (coefficientMap c X)
          (coefficientMap_comp_eq a b c hc X)).hom.app K) :=
  Functor.rightDerivedFunctorCommIso_hom_app_comp (comapLowerStarIso a f) (comapLowerStarIso b f)
    (comapLowerStarIso c f) (comapCoefficientMapCompIso a b c hc X)
    (comapCoefficientMapCompIso a b c hc Y) (comapLowerStarIso_hom_app_of_comp_eq a b c f hc) K


/-- The (Push) comparisons are the transposes, along `L(Ext) ⊣ D(Res)`, of the isomorphisms
`Rf_* ⋙ D(Res) ≅ D(Res) ⋙ Rf_*`, and these compose (`derivedComapLowerStarIso_hom_app_comp`); so
for `c = a ≫ b` the comparison for `c` is the composite of the comparisons for `a` and `b`, up to
the transitivity isomorphisms `T_c ≅ T_a ⋙ T_b` of the derived extensions of scalars on `Y` and
on `X`. -/
theorem derivedPushHom_app_eq_comp_of_comp_eq (hc : a ≫ b = c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (derivedPushHom c f).app K =
      (Mod.derivedExtendScalarsCompIso (coefficientMap a Y) (coefficientMap b Y)
          (coefficientMap c Y) (coefficientMap_comp_eq a b c hc Y)).hom.app
          (R((f)_*⟦Λ⟧).obj K) ≫
        L(Mod.extendScalars (coefficientMap b Y)).map ((derivedPushHom a f).app K) ≫
        (derivedPushHom b f).app (L(Mod.extendScalars (coefficientMap a X)).obj K) ≫
        R((f)_*⟦Λ''⟧).map ((Mod.derivedExtendScalarsCompIso (coefficientMap a X)
          (coefficientMap b X) (coefficientMap c X)
          (coefficientMap_comp_eq a b c hc X)).inv.app K) :=
  Adjunction.pushHomOfComapIso_app_eq_comp
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c Y))
    (derivedComapLowerStarIso a f) (derivedComapLowerStarIso b f) (derivedComapLowerStarIso c f)
    (Mod.mapDerivedCategoryComapCompIso _ _ _ (coefficientMap_comp_eq a b c hc X))
    (Mod.mapDerivedCategoryComapCompIso _ _ _ (coefficientMap_comp_eq a b c hc Y))
    (derivedComapLowerStarIso_hom_app_comp a b c f hc) K

/-- **(Push) is compatible with the composition of coefficient changes.** For `c = a ≫ b`, the
comparison `Rf_* ⋙ T_c ⟶ T_c ⋙ Rf_*` is the composite of the comparisons for `a` and `b`, up to
the transitivity isomorphisms `T_c ≅ T_a ⋙ T_b` of the derived extensions of scalars
(`Mod.derivedExtendScalarsCompIso`) on `Y` and on `X`. -/
theorem derivedPushHom_comp_app (hc : a ≫ b = c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (derivedPushHom c f).app K =
      (Mod.derivedExtendScalarsCompIso (coefficientMap a Y) (coefficientMap b Y)
          (coefficientMap c Y) (coefficientMap_comp_eq a b c hc Y)).hom.app
          (R((f)_*⟦Λ⟧).obj K) ≫
        L(Mod.extendScalars (coefficientMap b Y)).map ((derivedPushHom a f).app K) ≫
        (derivedPushHom b f).app (L(Mod.extendScalars (coefficientMap a X)).obj K) ≫
        R((f)_*⟦Λ''⟧).map ((Mod.derivedExtendScalarsCompIso (coefficientMap a X)
          (coefficientMap b X) (coefficientMap c X)
          (coefficientMap_comp_eq a b c hc X)).inv.app K) :=
  derivedPushHom_app_eq_comp_of_comp_eq a b c f hc K

end Derived

end AlgebraicGeometry.ProEtale.CondensedRing
