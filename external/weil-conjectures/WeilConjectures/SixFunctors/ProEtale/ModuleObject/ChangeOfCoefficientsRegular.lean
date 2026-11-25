/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk

/-!
# Change of coefficients and the free module of rank one

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. The (Pull) isomorphism `Λ'_X ⊗_{Λ_X} f^* M ≅ f^* (Λ'_Y ⊗_{Λ_Y} M)` is, for the free
module `M = Λ_Y` of rank one, compatible with the identifications `f^* Λ_Y ≅ Λ_X` and
`Λ'_Y ⊗_{Λ_Y} Λ_Y ≅ Λ'_Y` (`ProEtale.CondensedRing.pullIso_hom_app_regular_comp`).

Along the way we record that the unit `R ⟶ S ⊗_R R` followed by `S ⊗_R R ≅ S` is `φ`
(`Mod.extendUnitHom_extendScalarsObjRegularIso_hom`), and that the unit of the pullback
`f^* Λ_Y ⟶ Λ_X ⊗_{f^* Λ_Y} f^* Λ_Y` followed by `f^* Λ_Y ≅ Λ_X` is `α_f`
(`ProEtale.CondensedRing.extendUnitHom_upperStarObjRegularIso_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

/-- The unit `R ⟶ S ⊗_R R` followed by the identification `S ⊗_R R ≅ S` is `φ`. -/
@[reassoc]
lemma extendUnitHom_extendScalarsObjRegularIso_hom :
    extendUnitHom φ (regular R) ≫ (extendScalarsObjRegularIso φ).hom.hom = φ := by
  rw [← comp_extendScalarsObjRegularIso_inv_hom, Category.assoc, ← comp_hom', Iso.inv_hom_id,
    id_hom']
  exact Category.comp_id _

/-- The unit `R ⟶ Res_φ (S ⊗_R R)` followed by the restriction of `S ⊗_R R ≅ S` is `φ`, seen
as an `R`-linear map `R ⟶ Res_φ S`. -/
lemma extendRestrictAdjunction_unit_app_regular_comp_comap_map :
    (extendRestrictAdjunction φ).unit.app (regular R) ≫
        (comap φ).map (extendScalarsObjRegularIso φ).hom =
      regularHomComap φ :=
  hom_ext _ _ (by
    rw [comp_hom', extendRestrictAdjunction_unit_app_hom, comap_map_hom,
      extendUnitHom_extendScalarsObjRegularIso_hom, regularHomComap, homMk_hom])

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The unit `f^* Λ_Y ⟶ Λ_X ⊗_{f^* Λ_Y} f^* Λ_Y` of the extension of scalars along `α_f`,
followed by the identification `f^* Λ_Y ≅ Λ_X` of module objects, is `α_f`. -/
@[reassoc]
lemma extendUnitHom_upperStarObjRegularIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj
          (Mod.regular (condensedRingObj Λ Y))) ≫
      (upperStarObjRegularIso Λ f).hom.hom = condensedPullbackHom Λ f := by
  rw [upperStarObjRegularIso, Iso.trans_hom, Mod.comp_hom', Iso.app_hom,
    Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app_assoc, Mod.regularIsoOfIsIso_hom_hom]

/-- The pullback of `a_Y : Λ_Y ⟶ Res Λ'_Y` is `a_X : Λ_X ⟶ Res Λ'_X`, through the
identifications `f^* Λ_Y ≅ Λ_X`, `f^* Λ'_Y ≅ Λ'_X` and `f^* ∘ Res ≅ Res ∘ f^*`. -/
lemma upperStar_map_regularHomComap_comp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*⟦Λ⟧.map (Mod.regularHomComap (coefficientMap a Y)) ≫
        (comapUpperStarIso a f).inv.app (Mod.regular (condensedRingObj Λ' Y)) ≫
        (Mod.comap (coefficientMap a X)).map (upperStarObjRegularIso Λ' f).hom =
      (upperStarObjRegularIso Λ f).hom ≫ Mod.regularHomComap (coefficientMap a X) := by
  refine Mod.extendScalarsObj_hom_ext' (φ := condensedPullbackHom Λ f) ?_
  have hu := extendUnit_comapUpperStarIso_hom_app_hom a f (Mod.regular (condensedRingObj Λ' Y))
  rw [Mod.extendRestrictAdjunction_unit_app_hom, Mod.extendRestrictAdjunction_unit_app_hom] at hu
  have hu' : Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj
          ((Mod.comap (coefficientMap a Y)).obj (Mod.regular (condensedRingObj Λ' Y)))) ≫
      ((comapUpperStarIso a f).inv.app (Mod.regular (condensedRingObj Λ' Y))).hom =
      Mod.extendUnitHom (condensedPullbackHom Λ' f)
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y)).obj
          (Mod.regular (condensedRingObj Λ' Y))) := by
    rw [← hu, Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id_app, Mod.id_hom']
    exact Category.comp_id _
  have hn : Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj
          (Mod.regular (condensedRingObj Λ Y))) ≫
      ((f)^*⟦Λ⟧.map (Mod.regularHomComap (coefficientMap a Y))).hom =
      (f)^*[Ab.{u + 1}].map (coefficientMap a Y) ≫ Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj
          ((Mod.comap (coefficientMap a Y)).obj (Mod.regular (condensedRingObj Λ' Y)))) :=
    Mod.extendUnitHom_naturality (condensedPullbackHom Λ f)
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).map
        (Mod.regularHomComap (coefficientMap a Y)))
  rw [Mod.comp_hom', Mod.comp_hom', Mod.comp_hom', Mod.comap_map_hom, reassoc_of% hn,
    reassoc_of% hu', extendUnitHom_upperStarObjRegularIso_hom,
    extendUnitHom_upperStarObjRegularIso_hom_assoc]
  exact map_coefficientMap_comp_condensedPullbackHom a f

/-- (Pull) on the free module of rank one is compatible with the identifications
`f^* Λ_Y ≅ Λ_X` and `Λ'_Y ⊗_{Λ_Y} Λ_Y ≅ Λ'_Y`. -/
lemma pullIso_hom_app_regular_comp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullIso a f).hom.app (Mod.regular (condensedRingObj Λ Y)) ≫
        (f)^*⟦Λ'⟧.map (Mod.extendScalarsObjRegularIso (coefficientMap a Y)).hom ≫
        (upperStarObjRegularIso Λ' f).hom =
      (Mod.extendScalars (coefficientMap a X)).map (upperStarObjRegularIso Λ f).hom ≫
        (Mod.extendScalarsObjRegularIso (coefficientMap a X)).hom := by
  refine Mod.extendScalarsObj_hom_ext' (φ := coefficientMap a X) ?_
  have hp := congrArg Mod.Hom.hom
    (upperStar_map_unit_comp_comapUpperStarIso_inv_app a f (Mod.regular (condensedRingObj Λ Y)))
  rw [Mod.comp_hom', Mod.comp_hom', Mod.extendRestrictAdjunction_unit_app_hom,
    Mod.comap_map_hom] at hp
  have hs := congrArg Mod.Hom.hom (upperStar_map_regularHomComap_comp a f)
  rw [← Mod.extendRestrictAdjunction_unit_app_regular_comp_comap_map, Functor.map_comp] at hs
  simp only [Category.assoc, Mod.comp_hom', Mod.comap_map_hom] at hs
  have hn := Mod.extendUnitHom_naturality (coefficientMap a X) (upperStarObjRegularIso Λ f).hom
  rw [Mod.regularHomComap, Mod.homMk_hom] at hs
  have hnat := congrArg Mod.Hom.hom ((comapUpperStarIso a f).inv.naturality
    (Mod.extendScalarsObjRegularIso (coefficientMap a Y)).hom)
  simp only [Functor.comp_map, Mod.comp_hom', Mod.comap_map_hom] at hnat
  rw [Mod.comp_hom', Mod.comp_hom', Mod.comp_hom', reassoc_of% hn,
    Mod.extendUnitHom_extendScalarsObjRegularIso_hom, ← Category.assoc, ← hp, ← hs,
    Category.assoc, reassoc_of% hnat]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
