/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# Restriction of scalars, the adjunctions `f^* ⊣ f_*` and the composition isomorphisms

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. Restriction of scalars along `a` commutes with the pullback and the pushforward of
module objects (`ProEtale.CondensedRing.comapUpperStarIso`,
`ProEtale.CondensedRing.comapLowerStarIso`). This file shows that these commutation
isomorphisms are compatible with the adjunctions `f^* ⊣ f_*`: the units are compatible with them
(`ProEtale.CondensedRing.squareCompatible_upperStarLowerStarAdjunction_unit`), so that the
commutation of `f_*` is the mate of that of `f^*`
(`ProEtale.CondensedRing.isMateSquare_comapUpperStarIso_comapLowerStarIso`). Moreover they are
compatible with the composition isomorphisms `f_* ⋙ g_* ≅ (f ≫ g)_*` (on underlying sheaves both
are the composition isomorphism of the pushforwards of sheaves) and, by conjugation,
`(f ≫ g)^* ≅ g^* ⋙ f^*` (`ProEtale.CondensedRing.squareCompatible_upperStarComp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

/-- The unit of `Adjunction.ofNatIsoRight`. -/
lemma CategoryTheory.Adjunction.unit_ofNatIsoRight_app {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (e : G ≅ H) (x : C) :
    (adj.ofNatIsoRight e).unit.app x = adj.unit.app x ≫ e.hom.app _ := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y Z : Scheme.{u}} (f : X ⟶ Y)
  (g : Y ⟶ Z)

omit [IsCommMonObj Λ] in
/-- The identification `Res_{α_f} ⋙ (linear f_*) ≅ f_*` is the identity on underlying sheaves. -/
lemma comapPullbackHomCompIso_hom_app_hom
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((comapPullbackHomCompIso Λ f).hom.app M).hom = 𝟙 _ := by
  simp only [comapPullbackHomCompIso, Iso.trans_hom, NatTrans.comp_app, Mod.comp_hom',
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Mod.comapComp_inv_app_hom, Mod.id_hom', Functor.mapModComapIso_hom_app_hom,
    Mod.comap_map_hom, Mod.comapCongr_hom_app_hom]
  repeat erw [Category.id_comp]
  rfl

/-- The commutation `f^*_{Λ'} ⋙ Res ≅ Res ⋙ f^*_Λ` is compatible with the units of extension of
scalars along `α_f`. -/
lemma extendUnit_comapUpperStarIso_hom_app_hom
    (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ' f)).unit.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y)).obj N)).hom ≫
      ((comapUpperStarIso a f).hom.app N).hom =
    ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ f)).unit.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj
          ((Mod.comap (coefficientMap a Y)).obj N))).hom := by
  have hk := Mod.extendRestrictAdjunction_unit_app_hom_extendScalarsComapIsoOfIsIso_inv_app_hom
    ((f)^*[Ab.{u + 1}].map (coefficientMap a Y)) (coefficientMap a X)
    (condensedPullbackHom Λ f) (condensedPullbackHom Λ' f)
    (map_coefficientMap_comp_condensedPullbackHom a f).symm
    (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y)).obj N)
  have hk2 : ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ' f)).unit.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y)).obj N)).hom ≫
      ((Mod.extendScalarsComapIsoOfIsIso ((f)^*[Ab.{u + 1}].map (coefficientMap a Y))
        (coefficientMap a X) (condensedPullbackHom Λ f) (condensedPullbackHom Λ' f)
        (map_coefficientMap_comp_condensedPullbackHom a f).symm).hom.app
          (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y)).obj N)).hom =
      ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ f)).unit.app
          ((Mod.comap ((f)^*[Ab.{u + 1}].map (coefficientMap a Y))).obj
            (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y)).obj N))).hom := by
    rw [← hk, Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hk3 := Mod.extendUnitHom_extendScalarsMap (condensedPullbackHom Λ f)
    (((f)^*[Ab.{u + 1}].mapModComapIso (coefficientMap a Y)).inv.app N)
  rw [Functor.mapModComapIso_inv_app_hom, ← Mod.extendRestrictAdjunction_unit_app_hom,
    ← Mod.extendRestrictAdjunction_unit_app_hom] at hk3
  simp only [comapUpperStarIso, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.associator_inv_app, Mod.comp_hom',
    Mod.id_hom']
  erw [Category.id_comp, Category.id_comp, Category.comp_id, reassoc_of% hk2, hk3,
    Category.id_comp]
  rfl

/-- The units of the adjunctions `f^* ⊣ f_*` over `Λ'` and `Λ` are compatible with the
commutations of restriction of scalars with `f^*` and `f_*`. -/
lemma squareCompatible_upperStarLowerStarAdjunction_unit :
    NatTrans.SquareCompatible (Functor.idSquareIso (Mod.comap (coefficientMap a Y)))
      (Functor.pasteSquareIso (comapUpperStarIso a f) (comapLowerStarIso a f))
      (upperStarLowerStarAdjunction Λ' f).unit (upperStarLowerStarAdjunction Λ f).unit := by
  intro N
  apply Mod.hom_ext
  simp only [Functor.idSquareIso_hom_app, Functor.pasteSquareIso_hom_app, Category.id_comp,
    Mod.comp_hom', upperStarLowerStarAdjunction, Adjunction.unit_ofNatIsoRight_app,
    Adjunction.comp_unit_app, Mod.comap_map_hom, Adjunction.mapModAdjunction_unit_app_hom,
    Functor.comp_obj, Functor.id_obj, comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom,
    comapPullbackHomCompIso_hom_app_hom, Functor.comp_map]
  have hmap {M₁ M₂ : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
      (x : M₁ ⟶ M₂) : ((f)_*⟦Λ⟧.map x).hom = (f)_*[Ab.{u + 1}].map x.hom := rfl
  rw [hmap]
  simp only [Category.assoc]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  exact congrArg (_ ≫ ·) (((f)_*[Ab.{u + 1}].map_comp _ _).symm.trans
    (congrArg (f)_*[Ab.{u + 1}].map (extendUnit_comapUpperStarIso_hom_app_hom a f N)))

/-- The commutation of restriction of scalars with `f_*` is the mate of the inverse of its
commutation with `f^*`, for the adjunctions `f^* ⊣ f_*`. -/
lemma isMateSquare_comapUpperStarIso_comapLowerStarIso :
    (upperStarLowerStarAdjunction Λ' f).IsMateSquare (upperStarLowerStarAdjunction Λ f)
      (comapUpperStarIso a f) (comapLowerStarIso a f) :=
  Adjunction.IsMateSquare.of_unit (squareCompatible_upperStarLowerStarAdjunction_unit a f)

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
/-- The commutation of restriction of scalars with the pushforwards is compatible with the
composition isomorphisms `f_* ⋙ g_* ≅ (f ≫ g)_*`. -/
lemma squareCompatible_lowerStarComp :
    NatTrans.SquareCompatible
      (Functor.pasteSquareIso (comapLowerStarIso a f) (comapLowerStarIso a g))
      (comapLowerStarIso a (f ≫ g)) (lowerStarComp Λ' f g).hom (lowerStarComp Λ f g).hom := by
  intro K
  apply Mod.hom_ext
  simp only [Functor.pasteSquareIso_hom_app, Functor.comp_obj, Mod.comp_hom', Mod.comap_map_hom,
    comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom, lowerStarComp, Iso.trans_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Mod.id_hom', Mod.comapComp_inv_app_hom,
    Functor.mapModComapIso_hom_app_hom]
  repeat (first | erw [Category.id_comp] | erw [Category.comp_id])

omit [IsCommMonObj Λ'] in
/-- The composition isomorphism of the pullbacks is the inverse conjugate of that of the
pushforwards. -/
lemma upperStarComp_hom_eq_conjugateEquiv_symm :
    (upperStarComp Λ f g).hom = (conjugateEquiv ((upperStarLowerStarAdjunction Λ g).comp
      (upperStarLowerStarAdjunction Λ f)) (upperStarLowerStarAdjunction Λ (f ≫ g))).symm
        (lowerStarComp Λ f g).hom :=
  rfl

/-- The commutation of restriction of scalars with the pullbacks is compatible with the
composition isomorphisms `(f ≫ g)^* ≅ g^* ⋙ f^*`. -/
lemma squareCompatible_upperStarComp :
    NatTrans.SquareCompatible (comapUpperStarIso a (f ≫ g))
      (Functor.pasteSquareIso (comapUpperStarIso a g) (comapUpperStarIso a f))
      (upperStarComp Λ' f g).hom (upperStarComp Λ f g).hom := by
  rw [upperStarComp_hom_eq_conjugateEquiv_symm (Λ := Λ),
    upperStarComp_hom_eq_conjugateEquiv_symm (Λ := Λ')]
  exact NatTrans.SquareCompatible.conjugateEquiv_symm
    ((isMateSquare_comapUpperStarIso_comapLowerStarIso a g).comp
      (isMateSquare_comapUpperStarIso_comapLowerStarIso a f))
    (isMateSquare_comapUpperStarIso_comapLowerStarIso a (f ≫ g))
    (squareCompatible_lowerStarComp a f g)

end AlgebraicGeometry.ProEtale.CondensedRing
