/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-!
# The coherence isomorphisms of the pullbacks of module objects at the unit

Let `Λ` be a commutative condensed ring. The pullback `f^* : Mod_{Λ_Y} ⥤ Mod_{Λ_X}` of module
objects over `Λ` is strong monoidal (`ProEtale.CondensedRing.monoidal_upperStar`), with unit
comparison `ε_f : Λ_X ≅ f^* Λ_Y`. This file shows that the identity isomorphism
`(𝟙 X)^* ≅ 𝟭` (`ProEtale.CondensedRing.upperStarId`) and the composition isomorphisms
`(f ≫ g)^* ≅ g^* ⋙ f^*` (`ProEtale.CondensedRing.upperStarComp`) are compatible with these unit
comparisons:
```
(𝟙 X)^* Λ_X ≅ Λ_X  is  ε_{𝟙 X}⁻¹,      (f ≫ g)^* Λ_Z ≅ f^* g^* Λ_Z ≅ f^* Λ_Y ≅ Λ_X  is  ε_{f ≫ g}⁻¹.
```

Both isomorphisms are conjugate to those of the pushforwards under the adjunctions `f^* ⊣ f_*`.
The adjoint of `ε_f⁻¹ : f^* Λ_Y ⟶ Λ_X` is the coefficient morphism `η_f : Λ_Y ⟶ f_* Λ_X`
(`ProEtale.CondensedRing.homEquiv_εIso_inv_hom`), and a transformation of left adjoints is
compatible with the maps to the unit if and only if its conjugate is compatible with their
adjoints (`CategoryTheory.homEquiv_comp_conjugateEquiv_app`). The statements thus reduce to the
identities `η_{𝟙 X} = (𝟙 X)_* ≅ 𝟭` (`ProEtale.condensedPushforwardHom_id`) and
`η_{f ≫ g} = η_g ≫ g_* η_f` up to `g_* f_* ≅ (f ≫ g)_*`
(`ProEtale.condensedPushforwardHom_comp`).

## Main results

- `ProEtale.CondensedRing.homEquiv_εIso_inv_hom`: the adjoint of `ε_f⁻¹` is `η_f`.
- `ProEtale.CondensedRing.upperStarId_hom_app_unit`: `(𝟙 X)^* Λ_X ≅ Λ_X` is `ε_{𝟙 X}⁻¹`.
- `ProEtale.CondensedRing.upperStarComp_hom_app_unit`: the composition isomorphism is compatible
  with the unit comparisons.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The adjunction `𝟭 ⊣ 𝟭` induces the identity on morphisms. -/
lemma Adjunction.id_homEquiv_apply {C : Type*} [Category C] (X Y : C) (f : X ⟶ Y) :
    Adjunction.id.homEquiv X Y f = f := by
  rw [Adjunction.homEquiv_unit]
  simp

/-- Let `α : L₂ ⟶ L₁` be a transformation of left adjoints, `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, with
conjugate `β : R₁ ⟶ R₂`. For `e : L₁ c ⟶ d`, the adjoint `c ⟶ R₁ d` of `e` followed by `β` is the
adjoint `c ⟶ R₂ d` of `α ≫ e`. -/
lemma homEquiv_comp_conjugateEquiv_app {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {c : C} {d : D} (e : L₁.obj c ⟶ d) :
    adj₁.homEquiv c d e ≫ (conjugateEquiv adj₁ adj₂ α).app d =
      adj₂.homEquiv c d (α.app c ≫ e) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (conjugateEquiv adj₁ adj₂ α).naturality e, ← Category.assoc, unit_conjugateEquiv,
    Functor.map_comp, Category.assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The adjoint of the unit comparison -/

section Adjoint

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The unit `M ⟶ Λ_X ⊗_{f^* Λ_Y} M` of the extension of scalars along `α_f`, followed by the
identification of the extension of scalars along the isomorphism `α_f` with the restriction of
scalars along `α_f⁻¹`, is the identity of the underlying sheaf (a case of
`Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app`). -/
lemma extendUnitHom_extendScalarsIsoComapInv_hom_app
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y))) :
    Mod.extendUnitHom (condensedPullbackHom Λ f) M ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app M).hom = 𝟙 _ :=
  Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app _ M

/-- The unit of the adjunction between extension and restriction of scalars along `α_f` is
`Mod.extendUnitHom` on underlying sheaves (a case of
`Mod.extendRestrictAdjunction_unit_app_hom`). -/
lemma extendRestrictAdjunction_condensedPullbackHom_unit_app_hom
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y))) :
    ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ f)).unit.app M).hom =
      Mod.extendUnitHom (condensedPullbackHom Λ f) M :=
  Mod.extendRestrictAdjunction_unit_app_hom _ M

/-- The inverse `f^* Λ_Y ⟶ Λ_X` of the unit comparison of the pullback of module objects,
precomposed with the unit of the extension of scalars along `α_f`, is `α_f` on underlying
sheaves. -/
lemma extendUnitHom_η_upperStar :
    Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj (𝟙_ _)) ≫
      (Functor.OplaxMonoidal.η (f)^*⟦Λ⟧).hom = condensedPullbackHom Λ f := by
  have hη : Functor.OplaxMonoidal.η (f)^*⟦Λ⟧ =
      (Mod.extendScalars (condensedPullbackHom Λ f)).map
        (Functor.OplaxMonoidal.η ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))) ≫
        Functor.OplaxMonoidal.η (Mod.extendScalars (condensedPullbackHom Λ f)) := rfl
  have hn := congrArg Mod.Hom.hom
    ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ f)).unit.naturality
      (Functor.OplaxMonoidal.η ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))))
  simp only [Functor.id_map, Functor.comp_map, Mod.comp_hom', Mod.comap_map_hom,
    extendRestrictAdjunction_condensedPullbackHom_unit_app_hom] at hn
  rw [hη, Mod.comp_hom', ← Category.assoc]
  erw [← hn]
  rw [Functor.Monoidal.transport_η]
  have h₁ : (Functor.OplaxMonoidal.η ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))).hom =
      𝟙 _ := rfl
  have h₂ : (Functor.OplaxMonoidal.η
      (Mod.comap (asIso (condensedPullbackHom Λ f)).inv)).hom = condensedPullbackHom Λ f := by
    simp [Functor.OplaxMonoidal.η, Mod.comapCoreMonoidal, Mod.comapUnitIso]
  rw [h₁, Iso.symm_inv, Mod.comp_hom']
  simp only [Category.id_comp, Category.assoc]
  rw [reassoc_of% (extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f), h₂]

/-- On underlying sheaves, the adjoint `M ⟶ f_* N` of a map `g : f^* M ⟶ N` of module objects is
the unit `M ⟶ f_* f^* M` of the pullback of sheaves followed by `f_*` of the unit
`f^* M ⟶ Λ_X ⊗_{f^* Λ_Y} f^* M` and of `g`. -/
lemma upperStarLowerStarAdjunction_homEquiv_hom
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (g : (f)^*⟦Λ⟧.obj M ⟶ N) :
    ((upperStarLowerStarAdjunction Λ f).homEquiv M N g).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
        (f)_*[Ab.{u + 1}].map (Mod.extendUnitHom (condensedPullbackHom Λ f)
          (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj M) ≫ g.hom) := by
  simp [upperStarLowerStarAdjunction, comapPullbackHomCompIso,
    Adjunction.mapModAdjunction, Mod.extendRestrictAdjunction, Adjunction.homEquiv_unit]
  rfl

/-- The adjoint `Λ_Y ⟶ f_* Λ_X` of the inverse `f^* Λ_Y ⟶ Λ_X` of the unit comparison of the
strong monoidal pullback of module objects is the coefficient morphism `η_f`. -/
lemma homEquiv_εIso_inv_hom : ((upperStarLowerStarAdjunction Λ f).homEquiv _ _
      (Functor.Monoidal.εIso (f)^*⟦Λ⟧).inv).hom = condensedPushforwardHom Λ f := by
  rw [upperStarLowerStarAdjunction_homEquiv_hom, Functor.Monoidal.εIso_inv,
    extendUnitHom_η_upperStar]
  exact unitAlgHom_comp_map_condensedPullbackHom Λ f

end Adjoint

/-! ### The identity and composition isomorphisms at the unit -/

/-- The identity isomorphism `(𝟙 X)^* ≅ 𝟭` of the pullback of module objects is, at the unit
`Λ_X`, the inverse of the unit comparison `ε : Λ_X ≅ (𝟙 X)^* Λ_X`. -/
lemma upperStarId_hom_app_unit (X : Scheme.{u}) :
    (upperStarId Λ X).hom.app (𝟙_ _) = (Functor.Monoidal.εIso (𝟙 X)^*⟦Λ⟧).inv := by
  apply ((upperStarLowerStarAdjunction Λ (𝟙 X)).homEquiv (𝟙_ _) (𝟙_ _)).injective
  have h := homEquiv_comp_conjugateEquiv_app Adjunction.id (upperStarLowerStarAdjunction Λ (𝟙 X))
    (upperStarId Λ X).hom (𝟙 (𝟙_ _))
  erw [Category.comp_id] at h
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarId] at h
  rw [← h]
  ext1
  rw [homEquiv_εIso_inv_hom, condensedPushforwardHom_id]
  erw [Adjunction.id_homEquiv_apply, Category.id_comp]
  rw [Iso.symm_hom]
  have h' := congrArg Mod.Hom.hom ((lowerStarId Λ X).hom_inv_id_app (𝟙_ _))
  rw [Mod.comp_hom', lowerStarId_hom_app_hom] at h'
  rw [← cancel_epi ((ProEtale.lowerStarId Ab.{u + 1} X).hom.app _), Iso.hom_inv_id_app]
  exact h'

/-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` of the pullbacks of module objects is
compatible with the unit comparisons: `(f ≫ g)^* Λ_Z ≅ f^* g^* Λ_Z ≅ f^* Λ_Y ≅ Λ_X` is the inverse
of the unit comparison of `(f ≫ g)^*`. -/
lemma upperStarComp_hom_app_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStarComp Λ f g).hom.app (𝟙_ _) ≫ (f)^*⟦Λ⟧.map (Functor.Monoidal.εIso (g)^*⟦Λ⟧).inv ≫
      (Functor.Monoidal.εIso (f)^*⟦Λ⟧).inv = (Functor.Monoidal.εIso (f ≫ g)^*⟦Λ⟧).inv := by
  apply ((upperStarLowerStarAdjunction Λ (f ≫ g)).homEquiv (𝟙_ _) (𝟙_ _)).injective
  have h := homEquiv_comp_conjugateEquiv_app
    ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
    (upperStarLowerStarAdjunction Λ (f ≫ g)) (upperStarComp Λ f g).hom
    ((f)^*⟦Λ⟧.map (Functor.Monoidal.εIso (g)^*⟦Λ⟧).inv ≫ (Functor.Monoidal.εIso (f)^*⟦Λ⟧).inv)
  have hc : ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f)).homEquiv
      (𝟙_ _) (𝟙_ _)
      ((f)^*⟦Λ⟧.map (Functor.Monoidal.εIso (g)^*⟦Λ⟧).inv ≫ (Functor.Monoidal.εIso (f)^*⟦Λ⟧).inv) =
      (upperStarLowerStarAdjunction Λ g).homEquiv _ _ ((upperStarLowerStarAdjunction Λ f).homEquiv
        _ _ ((f)^*⟦Λ⟧.map (Functor.Monoidal.εIso (g)^*⟦Λ⟧).inv ≫
          (Functor.Monoidal.εIso (f)^*⟦Λ⟧).inv)) := by
    rw [Adjunction.comp_homEquiv]
    rfl
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarComp, hc] at h
  rw [← h, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  ext1
  simp only [Mod.comp_hom', lowerStar_map_hom, lowerStarComp_hom_app_hom, homEquiv_εIso_inv_hom,
    condensedPushforwardHom_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
