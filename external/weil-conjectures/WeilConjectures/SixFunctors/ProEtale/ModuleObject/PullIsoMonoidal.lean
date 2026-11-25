/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidalComp
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsOfIsIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-!
# The underived (Pull) isomorphism is monoidal

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. The underived (Pull) isomorphism
`ProEtale.CondensedRing.pullIso a f : f^*_Λ ⋙ Ext_{a_X} ≅ Ext_{a_Y} ⋙ f^*_Λ'` is a monoidal
natural isomorphism (`ProEtale.CondensedRing.isMonoidal_pullIso_hom`), for the strong monoidal
structures of the pullbacks (`ProEtale.CondensedRing.monoidal_upperStar`) and of the extensions
of scalars (`Mod.extendScalarsMonoidal`).

The proof computes on underlying sheaves. Maps out of `Λ'_X ⊗_{Λ_X} f^* (M ⊗ N)` are determined
by their precomposition with the projection `f^* (M ⊗ N) ⟶ f^*(M ⊗_{Λ_Y} N)` and the units of the
extensions of scalars. On these generators, both comonoidal structures are that of the pullback of
sheaves (`ProEtale.CondensedRing.map_tensorObjπ_upperStarUnitHom_extendUnitHom_δ_hom`,
`ProEtale.CondensedRing.map_tensorObjπ_map_extendUnitHom_upperStarUnitHom_δ_hom`), and (Pull) is
the pullback of the unit `M ⟶ Λ'_Y ⊗_{Λ_Y} M`
(`ProEtale.CondensedRing.upperStarUnitHom_extendUnitHom_pullIso_hom_app_hom`). The compatibility
with the unit comparisons is automatic for an isomorphism between strong monoidal functors
(`NatTrans.IsMonoidal.of_isIso_of_δ`).
-/
@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The comonoidal structure of extension of scalars on the units: `m ⊗ n ↦ (1 ⊗ m) ⊗ (1 ⊗ n)`. -/
@[reassoc]
lemma tensorObjπ_extendUnitHom_δ_hom (M N : Mod C R) :
    letI := extendScalarsMonoidal φ
    tensorObjπ M N ≫ extendUnitHom φ (M ⊗ N) ≫ (δ (extendScalars φ) M N).hom =
      (extendUnitHom φ M ⊗ₘ extendUnitHom φ N) ≫
        tensorObjπ ((extendScalars φ).obj M) ((extendScalars φ).obj N) := by
  let := extendScalarsMonoidal φ
  erw [extendScalarsOplaxMonoidal_δ]
  rw [extendUnitHom_extendHom, comp_hom', tensorObjπ_tensorHom_hom_assoc]
  erw [tensorObjπ_comapTensorHom_hom]
  rfl

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- On underlying sheaves, the commutation `Res ⋙ f^*_Λ ≅ f^*_Λ' ⋙ Res` is the identity after
the units of the extensions of scalars along the coefficient morphisms. -/
@[reassoc]
lemma upperStarUnitHom_comapUpperStarIso_inv_app_hom
    (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    upperStarUnitHom Λ f ((Mod.comap (coefficientMap a Y)).obj N) ≫
      ((comapUpperStarIso a f).inv.app N).hom = upperStarUnitHom Λ' f N := by
  rw [upperStarUnitHom, ← Mod.extendRestrictAdjunction_unit_app_hom,
    ← extendUnit_comapUpperStarIso_hom_app_hom, Category.assoc, ← Mod.comp_hom',
    Iso.hom_inv_id_app, Mod.id_hom']
  erw [Category.comp_id]
  rw [Mod.extendRestrictAdjunction_unit_app_hom]

/-- **(Pull) on generators**: on underlying sheaves, after the units of the extensions of
scalars, (Pull) is the pullback of the unit `M ⟶ Λ'_Y ⊗_{Λ_Y} M`. -/
@[reassoc]
lemma upperStarUnitHom_extendUnitHom_pullIso_hom_app_hom
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    upperStarUnitHom Λ f M ≫ Mod.extendUnitHom (coefficientMap a X) ((f)^*⟦Λ⟧.obj M) ≫
      ((pullIso a f).hom.app M).hom =
    (f)^*[Ab.{u + 1}].map (Mod.extendUnitHom (coefficientMap a Y) M) ≫
      upperStarUnitHom Λ' f ((Mod.extendScalars (coefficientMap a Y)).obj M) := by
  have h := congrArg Mod.Hom.hom (upperStar_map_unit_comp_comapUpperStarIso_inv_app a f M)
  rw [Mod.comp_hom', Mod.comp_hom', Mod.comap_map_hom,
    Mod.extendRestrictAdjunction_unit_app_hom] at h
  rw [← h, upperStarUnitHom_map_hom_assoc, Mod.extendRestrictAdjunction_unit_app_hom]
  exact congrArg (_ ≫ ·) (upperStarUnitHom_comapUpperStarIso_inv_app_hom a f _)

/-- The comonoidal structure of `f^*_Λ ⋙ Ext_{a_X}` on generators: on underlying sheaves, after
the projection to the relative tensor product and the units of the extensions of scalars, it is
the comonoidal structure of the pullback of sheaves. -/
@[reassoc]
lemma map_tensorObjπ_upperStarUnitHom_extendUnitHom_δ_hom
    (M N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    letI := Mod.extendScalarsMonoidal (coefficientMap a X)
    (f)^*[Ab.{u + 1}].map (Mod.tensorObjπ M N) ≫ upperStarUnitHom Λ f (M ⊗ N) ≫
      Mod.extendUnitHom (coefficientMap a X) ((f)^*⟦Λ⟧.obj (M ⊗ N)) ≫
        (δ ((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)) M N).hom =
      δ (f)^*[Ab.{u + 1}] M.X N.X ≫
        ((upperStarUnitHom Λ f M ≫ Mod.extendUnitHom (coefficientMap a X) ((f)^*⟦Λ⟧.obj M)) ⊗ₘ
          (upperStarUnitHom Λ f N ≫ Mod.extendUnitHom (coefficientMap a X) ((f)^*⟦Λ⟧.obj N))) ≫
        Mod.tensorObjπ (((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)).obj M)
          (((f)^*⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)).obj N) := by
  let := Mod.extendScalarsMonoidal (coefficientMap a X)
  rw [Functor.OplaxMonoidal.comp_δ, Mod.comp_hom']
  rw [Mod.extendUnitHom_comp_extendScalars_map_hom_assoc]
  rw [map_tensorObjπ_upperStarUnitHom_δ_hom_assoc]
  erw [Mod.tensorObjπ_extendUnitHom_δ_hom]
  rw [tensorHom_comp_tensorHom_assoc]
  rfl

/-- The comonoidal structure of `Ext_{a_Y} ⋙ f^*_Λ'` on generators: on underlying sheaves, after
the projection to the relative tensor product and the units of the extensions of scalars, it is
the comonoidal structure of the pullback of sheaves. -/
@[reassoc]
lemma map_tensorObjπ_map_extendUnitHom_upperStarUnitHom_δ_hom
    (M N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    letI := Mod.extendScalarsMonoidal (coefficientMap a Y)
    (f)^*[Ab.{u + 1}].map (Mod.tensorObjπ M N) ≫
      (f)^*[Ab.{u + 1}].map (Mod.extendUnitHom (coefficientMap a Y) (M ⊗ N)) ≫
      upperStarUnitHom Λ' f ((Mod.extendScalars (coefficientMap a Y)).obj (M ⊗ N)) ≫
        (δ (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧) M N).hom =
      δ (f)^*[Ab.{u + 1}] M.X N.X ≫
        (((f)^*[Ab.{u + 1}].map (Mod.extendUnitHom (coefficientMap a Y) M) ≫
            upperStarUnitHom Λ' f ((Mod.extendScalars (coefficientMap a Y)).obj M)) ⊗ₘ
          ((f)^*[Ab.{u + 1}].map (Mod.extendUnitHom (coefficientMap a Y) N) ≫
            upperStarUnitHom Λ' f ((Mod.extendScalars (coefficientMap a Y)).obj N))) ≫
        Mod.tensorObjπ ((Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧).obj M)
          ((Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧).obj N) := by
  let := Mod.extendScalarsMonoidal (coefficientMap a Y)
  rw [Functor.OplaxMonoidal.comp_δ, Mod.comp_hom', upperStarUnitHom_map_hom_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]
  erw [Mod.tensorObjπ_extendUnitHom_δ_hom]
  rw [Functor.map_comp_assoc, map_tensorObjπ_upperStarUnitHom_δ_hom]
  rw [← tensorHom_comp_tensorHom_assoc, δ_natural_assoc]
  rfl

/-- **The underived (Pull) isomorphism is monoidal**: `pullIso a f` commutes with the tensor
comparisons of the composite strong monoidal functors `f^*_Λ ⋙ Ext_{a_X}` and
`Ext_{a_Y} ⋙ f^*_Λ'`. -/
theorem isMonoidal_pullIso_hom :
    letI := Mod.extendScalarsMonoidal (coefficientMap a X)
    letI := Mod.extendScalarsMonoidal (coefficientMap a Y)
    NatTrans.IsMonoidal (pullIso a f).hom := by
  let := Mod.extendScalarsMonoidal (coefficientMap a X)
  let := Mod.extendScalarsMonoidal (coefficientMap a Y)
  refine NatTrans.IsMonoidal.of_isIso_of_δ _ fun M N ↦ ?_
  refine Mod.extendScalarsObj_hom_ext' ?_
  rw [← cancel_epi ((f)^*[Ab.{u + 1}].map (Mod.tensorObjπ M N) ≫ upperStarUnitHom Λ f (M ⊗ N)),
    Mod.comp_hom', Mod.comp_hom']
  simp only [Category.assoc]
  rw [upperStarUnitHom_extendUnitHom_pullIso_hom_app_hom_assoc,
    map_tensorObjπ_map_extendUnitHom_upperStarUnitHom_δ_hom,
    map_tensorObjπ_upperStarUnitHom_extendUnitHom_δ_hom_assoc, Mod.tensorObjπ_tensorHom_hom,
    tensorHom_comp_tensorHom_assoc, Category.assoc, Category.assoc,
    upperStarUnitHom_extendUnitHom_pullIso_hom_app_hom,
    upperStarUnitHom_extendUnitHom_pullIso_hom_app_hom]

end AlgebraicGeometry.ProEtale.CondensedRing
