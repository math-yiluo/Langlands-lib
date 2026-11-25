/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-!
# The identification `σ^* ≅ 𝟭` at the unit

Let `Ω` be a separably closed field and `σ` an endomorphism of `Spec Ω`. The isomorphism
`σ^* ≅ 𝟭` of `ProEtale.CondensedRing.upperStarIsoIdOfIsSepClosed` is, at the unit `Λ_{Spec Ω}`,
the inverse of the unit comparison `ε_σ : Λ_{Spec Ω} ≅ σ^* Λ_{Spec Ω}` of the strong monoidal
functor `σ^*`.

Writing `P = p^*` for the pullback from condensed `Λ`-modules, the isomorphism `σ^* ≅ 𝟭` is,
on objects of the form `P A`, the comparison `P ⋙ σ^* ≅ P`
(`Functor.isoWhiskerLeft_counitIso_hom_app_functor_obj`), so its value at the unit reduces to
the unit coherence of `ProEtale.CondensedRing.upperStarFromPointModComp`.

## Main results

- `CategoryTheory.Functor.isoWhiskerLeft_counitIso_hom_app_functor_obj`,
  `CategoryTheory.Iso.hom_app_eq_inv_of_hom_app_eq`: the abstract reduction.
- `ProEtale.CondensedRing.upperStarFromPointModComp_hom_app_unit`: the comparison
  `P_Y ⋙ f^* ≅ P_X` is compatible with the unit comparisons. On underlying sheaves, after the
  unit of the extension of scalars along `α_f`, both sides are `α_f`.
- `ProEtale.CondensedRing.upperStarIsoIdOfIsSepClosed_hom_app_unit`: `σ^* Λ ≅ Λ` is `ε_σ⁻¹`.

## Implementation notes

The unit of a category of module objects occurs in two syntactic forms: `𝟙_ _` elaborates to the
unit of the instance `Mod.monoidalCategoryStruct`, while the unit comparisons `ε` of monoidal
functors are stated with the unit of `Mod.monoidalCategory`. The two are definitionally equal,
but the kernel only identifies them after unfolding the pullbacks when they occur as arguments
of a component of a concrete natural transformation. The statements here therefore leave the
unit to be inferred from the type of `ε`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

/-- Let `P : A ⥤ B` be an equivalence and `c : P ⋙ S ≅ P`. The induced isomorphism
`S ≅ P⁻¹ ⋙ P ⋙ S ≅ P⁻¹ ⋙ P ≅ 𝟭` is `c` on objects of the form `P a`. -/
lemma isoWhiskerLeft_counitIso_hom_app_functor_obj {A B : Type*} [Category A] [Category B]
    (P : A ⥤ B) [P.IsEquivalence] {S : B ⥤ B} (c : P ⋙ S ≅ P) (a : A) :
    ((Functor.leftUnitor S).symm ≪≫
      Functor.isoWhiskerRight P.asEquivalence.counitIso.symm S ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ c ≪≫ P.asEquivalence.counitIso).hom.app (P.obj a) =
      c.hom.app a := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp, Functor.comp_obj,
    Functor.id_obj]
  erw [P.asEquivalence.counitInv_app_functor a, P.asEquivalence.counit_app_functor a]
  have h := c.hom.naturality (P.asEquivalence.unit.app a)
  rw [Functor.comp_map] at h
  erw [reassoc_of% h, ← P.map_comp, P.asEquivalence.unitIso.hom_inv_id_app a, P.map_id,
    Category.comp_id]

/-- Let `τ : S ≅ 𝟭` and `e : b ≅ b'`. If `τ` at `b'` is `S e⁻¹ ≫ ε⁻¹ ≫ e` for an isomorphism
`ε : b ≅ S b`, then `τ` at `b` is `ε⁻¹`. -/
lemma _root_.CategoryTheory.Iso.hom_app_eq_inv_of_hom_app_eq {B : Type*} [Category B] {S : B ⥤ B}
    (τ : S ≅ 𝟭 B)
    {b b' : B} (e : b ≅ b') (ε : b ≅ S.obj b)
    (h : τ.hom.app b' = S.map e.inv ≫ ε.inv ≫ e.hom) : τ.hom.app b = ε.inv := by
  have hn := τ.hom.naturality e.hom
  rw [h, Iso.hom_inv_id_map_assoc, Functor.id_map] at hn
  exact ((cancel_mono e.hom).1 hn).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- The inverse image `p_X^*` preserves coequalizers, being a left adjoint. -/
noncomputable instance preservesColimitsOfShape_walkingParallelPair_upperStarFromPoint
    (X : Scheme.{u}) : PreservesColimitsOfShape WalkingParallelPair (upperStarFromPoint X) :=
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits
  inferInstance

/-- The inverse image `p_X^*` is braided strong monoidal. The low priority keeps instance search
for its lax monoidal structure on the existing instances. -/
noncomputable instance (priority := low) braided_upperStarFromPoint (X : Scheme.{u}) :
    (upperStarFromPoint X).Braided where

/-- The pullback `p_X^*` from condensed `Λ`-modules is strong monoidal, being the transport of
module objects along the braided functor `p_X^*` preserving coequalizers. -/
noncomputable instance monoidal_upperStarFromPointMod (X : Scheme.{u}) :
    (upperStarFromPointMod Λ X).Monoidal :=
  inferInstanceAs ((upperStarFromPoint X).mapMod Λ).Monoidal

/-- The comparison `upperStarFromPointModComp f`, written out as the composite of
`Functor.mapModCompIso` with the identification of the extension of scalars along the isomorphism
`α_f` with a restriction of scalars. It is definitionally `upperStarFromPointModComp f`; rewriting
to this reducible form before applying lemmas about the composite keeps the kernel from unfolding
the comparison of pullbacks, see the implementation notes of
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit`. Its type is left to be inferred,
in the form of the composite; ascribing the type of `upperStarFromPointModComp f` brings the kernel
timeouts back. -/
noncomputable abbrev upperStarFromPointModCompComposite {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso (upperStarFromPoint Y) (f)^*[Ab.{u + 1}]
        (upperStarFromPointComp f).hom Λ)
      (Mod.extendScalars (Functor.compAlgHom (upperStarFromPoint Y) (f)^*[Ab.{u + 1}]
        (upperStarFromPointComp f).hom Λ)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (Functor.compAlgHom
          (upperStarFromPoint Y) (f)^*[Ab.{u + 1}] (upperStarFromPointComp f).hom Λ)) ≪≫
        (Mod.comapEquivalenceOfIsIso (Functor.compAlgHom (upperStarFromPoint Y)
          (f)^*[Ab.{u + 1}] (upperStarFromPointComp f).hom Λ)).unitIso.symm) ≪≫
    Functor.rightUnitor _

/-- At the unit `Λ`, the comparison `p_Y^* ⋙ f^* ≅ p_X^*` is `α_f` on underlying sheaves after
the unit `f^* p_Y^* Λ ⟶ Λ_X ⊗_{f^* Λ_Y} f^* p_Y^* Λ` of the extension of scalars. -/
lemma extendUnitHom_upperStarFromPointModComp_hom_app_unit_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((f)^*[Ab.{u + 1}].mapMod _).obj ((upperStarFromPointMod Λ Y).obj
          (@MonoidalCategoryStruct.tensorUnit (Mod _ Λ) _
            MonoidalCategory.toMonoidalCategoryStruct))) ≫
      ((upperStarFromPointModComp Λ f).hom.app
        (@MonoidalCategoryStruct.tensorUnit (Mod _ Λ) _
          MonoidalCategory.toMonoidalCategoryStruct)).hom = condensedPullbackHom Λ f := by
  rw [show upperStarFromPointModComp Λ f = upperStarFromPointModCompComposite Λ f from rfl]
  exact Functor.extendUnitHom_hom_app_unit_hom_of_eq_mapModCompExtendScalarsIso _ _ _ _
    (upperStarFromPointModCompComposite Λ f) rfl

/-- The comparison `p_Y^* ⋙ f^* ≅ p_X^*` on module objects is compatible with the unit
comparisons: at the unit it is `f^*(ε_{p_Y^*}⁻¹) ≫ ε_f⁻¹ ≫ ε_{p_X^*}`.

On underlying sheaves, after the unit of the extension of scalars along `α_f`, both sides are
`α_f` (`extendUnitHom_upperStarFromPointModComp_hom_app_unit_hom` and
`extendUnitHom_η_upperStar`). The unit of `Mod_Λ` is the one of the type of `ε_{p_Y^*}`. -/
lemma upperStarFromPointModComp_hom_app_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarFromPointModComp Λ f).hom.app _ =
      (f)^*⟦Λ⟧.map (Functor.Monoidal.εIso (upperStarFromPointMod Λ Y)).inv ≫
        (Functor.Monoidal.εIso (f)^*⟦Λ⟧).inv ≫
          (Functor.Monoidal.εIso (upperStarFromPointMod Λ X)).hom := by
  apply Mod.extendScalarsObj_hom_ext'
  rw [extendUnitHom_upperStarFromPointModComp_hom_app_unit_hom, Mod.comp_hom', Mod.comp_hom']
  erw [Mod.extendUnitHom_extendScalarsMap_assoc]
  rw [Functor.mapMod_map_hom, Functor.Monoidal.εIso_inv (upperStarFromPointMod Λ Y),
    Functor.Monoidal.εIso_inv (f)^*⟦Λ⟧]
  erw [reassoc_of% (extendUnitHom_η_upperStar Λ f)]
  have h₁ : (Functor.OplaxMonoidal.η (upperStarFromPointMod Λ Y)).hom = 𝟙 _ := rfl
  have h₂ : (Functor.Monoidal.εIso (upperStarFromPointMod Λ X)).hom.hom = 𝟙 _ := rfl
  rw [h₁, h₂]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The isomorphism `σ^* ≅ 𝟭` is, at the unit, the inverse of the unit comparison of `σ^*`: by
`Iso.hom_app_eq_inv_of_hom_app_eq` it suffices to compute it at `p^* Λ`, where it is the
comparison `p^* ⋙ σ^* ≅ p^*` (`Functor.isoWhiskerLeft_counitIso_hom_app_functor_obj`), given at
the unit by `upperStarFromPointModComp_hom_app_unit`. The unit of `Mod_{Spec Ω}` is the one of
the type of `ε_σ`. -/
lemma upperStarIsoIdOfIsSepClosed_hom_app_unit (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) :
    (upperStarIsoIdOfIsSepClosed Λ σ).hom.app _ =
      (Functor.Monoidal.εIso (σ)^*⟦Λ⟧).inv := by
  refine Iso.hom_app_eq_inv_of_hom_app_eq _
    (Functor.Monoidal.εIso (upperStarFromPointMod Λ (Spec (.of Ω)))) _ ?_
  rw [show upperStarIsoIdOfIsSepClosed Λ σ = (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight
        (upperStarFromPointMod Λ (Spec (.of Ω))).asEquivalence.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (upperStarFromPointModComp Λ σ) ≪≫
      (upperStarFromPointMod Λ (Spec (.of Ω))).asEquivalence.counitIso from rfl,
    Functor.isoWhiskerLeft_counitIso_hom_app_functor_obj]
  exact upperStarFromPointModComp_hom_app_unit Λ σ

end AlgebraicGeometry.ProEtale.CondensedRing
