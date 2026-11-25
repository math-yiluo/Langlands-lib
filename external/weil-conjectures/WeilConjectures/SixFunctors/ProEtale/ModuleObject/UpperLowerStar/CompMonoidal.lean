/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate

/-!
# The composition isomorphism of the pullbacks of module objects is monoidal

Let `Λ` be a commutative condensed ring. The pullback `f^* = mapMod(f^*) ⋙ Ext_{α_f}` of module
objects over `Λ` is strong monoidal (`ProEtale.CondensedRing.monoidal_upperStar`). This file shows
that the composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*`
(`ProEtale.CondensedRing.upperStarComp`) commutes with the tensor comparisons
(`ProEtale.CondensedRing.upperStarComp_hom_app_tensor_δ`).

On underlying sheaves, after the projections `M ⊗ N ⟶ M ⊗_Λ N` and the units
`f^* M ⟶ Λ_X ⊗_{f^* Λ_Y} f^* M` of the extensions of scalars, the tensor comparison of the
pullback of module objects is that of the pullback of sheaves
(`ProEtale.CondensedRing.map_tensorObjπ_upperStarUnitHom_δ_hom`) and the composition isomorphism
is that of the pullbacks of sheaves
(`ProEtale.CondensedRing.upperStarUnitHom_upperStarComp_hom_app_hom`),
which is monoidal (`ProEtale.CondensedRing.isMonoidal_sheafUpperStarComp_inv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The unit `f^* M ⟶ Λ_X ⊗_{f^* Λ_Y} f^* M` of the extension of scalars along `α_f`, from the
pullback of the underlying sheaf to the underlying sheaf of the pullback of module objects. -/
noncomputable abbrev upperStarUnitHom
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f)^*[Ab.{u + 1}].obj M.X ⟶ ((f)^*⟦Λ⟧.obj M).X :=
  Mod.extendUnitHom (condensedPullbackHom Λ f)
    (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj M)

lemma δ_upperStar_eq (A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) :
    δ (f)^*⟦Λ⟧ A B = (Mod.extendScalars (condensedPullbackHom Λ f)).map
        (δ ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)) A B) ≫
      δ (Mod.extendScalars (condensedPullbackHom Λ f)) _ _ :=
  rfl

/-- The tensor product `a ⊗ b` of module maps is `a ⊗ b` on underlying objects after the
projections to the relative tensor products. -/
@[reassoc]
lemma _root_.CategoryTheory.Mod.tensorObjπ_tensorHom_hom {C : Type*} [Category C]
    [MonoidalCategory C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C] {R : C}
    [MonObj R] [IsCommMonObj R] {M M' N N' : Mod C R} (a : M ⟶ M') (b : N ⟶ N') :
    Mod.tensorObjπ M N ≫ (a ⊗ₘ b).hom = (a.hom ⊗ₘ b.hom) ≫ Mod.tensorObjπ M' N' := by
  rw [MonoidalCategory.tensorHom_def, Mod.comp_hom', Mod.tensorObjπ_whiskerRight_assoc,
    Mod.tensorObjπ_whiskerLeft, ← Category.assoc, ← MonoidalCategory.tensorHom_def]

lemma extendScalarsIsoComapInv_inv_app_hom
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y))) :
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).inv.app M).hom =
      Mod.extendUnitHom (condensedPullbackHom Λ f) M := by
  have h := extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f M
  calc _ = (Mod.extendUnitHom (condensedPullbackHom Λ f) M ≫
        ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app M).hom) ≫
        ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).inv.app M).hom := by
        rw [h, Category.id_comp]
    _ = _ := by
        rw [Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id_app]
        exact Category.comp_id _

/-- On underlying sheaves, the tensor comparison `f^* (A ⊗ B) ⟶ f^* A ⊗ f^* B` of the pullback
of module objects is that of the pullback of sheaves, after the projections to the relative
tensor products and the units of the extensions of scalars. -/
@[reassoc]
lemma map_tensorObjπ_upperStarUnitHom_δ_hom
    (A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f)^*[Ab.{u + 1}].map (Mod.tensorObjπ A B) ≫ upperStarUnitHom Λ f (A ⊗ B) ≫
        (δ (f)^*⟦Λ⟧ A B).hom =
      δ (f)^*[Ab.{u + 1}] A.X B.X ≫ (upperStarUnitHom Λ f A ⊗ₘ upperStarUnitHom Λ f B) ≫
        Mod.tensorObjπ ((f)^*⟦Λ⟧.obj A) ((f)^*⟦Λ⟧.obj B) := by
  rw [δ_upperStar_eq, Mod.comp_hom']
  erw [Mod.extendUnitHom_extendScalarsMap_assoc]
  have h₁ : (f)^*[Ab.{u + 1}].map (Mod.tensorObjπ A B) ≫
      (δ ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)) A B).hom =
      δ (f)^*[Ab.{u + 1}] A.X B.X ≫
        Mod.tensorObjπ (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj A)
          (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj B) := by
    have h := Functor.tensorπ_mapModTensorIso_hom_hom (f)^*[Ab.{u + 1}] A B
    have hδ : (δ ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)) A B).hom =
        ((f)^*[Ab.{u + 1}].mapModTensorIso A B).inv.hom := rfl
    rw [hδ, ← cancel_epi (Functor.LaxMonoidal.μ (f)^*[Ab.{u + 1}] A.X B.X), ← Category.assoc, ← h,
      Functor.Monoidal.μ_δ_assoc, Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id]
    exact Category.comp_id _
  rw [reassoc_of% h₁]
  congr 1
  erw [Functor.Monoidal.transport_δ]
  rw [Iso.symm_inv, Iso.symm_hom, Mod.comp_hom', Mod.comp_hom',
    reassoc_of% (extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f _)]
  have hc (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y))) :
      Mod.tensorObjπ M N ≫ (δ (Mod.comap (asIso (condensedPullbackHom Λ f)).inv) M N).hom =
        Mod.tensorObjπ ((Mod.comap (asIso (condensedPullbackHom Λ f)).inv).obj M)
          ((Mod.comap (asIso (condensedPullbackHom Λ f)).inv).obj N) := by
    have h := Mod.tensorπ_comapTensorIso_hom_hom (asIso (condensedPullbackHom Λ f)).inv M N
    have hδ : (δ (Mod.comap (asIso (condensedPullbackHom Λ f)).inv) M N).hom =
        (Mod.comapTensorIso (asIso (condensedPullbackHom Λ f)).inv M N).inv.hom := rfl
    rw [hδ, ← h, Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id]
    exact Category.comp_id _
  erw [reassoc_of% (hc _ _), Mod.tensorObjπ_tensorHom_hom]
  rw [extendScalarsIsoComapInv_inv_app_hom, extendScalarsIsoComapInv_inv_app_hom]
  rfl

/-- On underlying sheaves, the composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` of the pullbacks of
module objects is that of the pullbacks of sheaves, after the units of the extensions of
scalars. -/
@[reassoc]
lemma upperStarUnitHom_upperStarComp_hom_app_hom
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    upperStarUnitHom Λ (f ≫ g) M ≫ ((upperStarComp Λ f g).hom.app M).hom =
      (ProEtale.upperStarComp Ab.{u + 1} f g).hom.app M.X ≫
        (f)^*[Ab.{u + 1}].map (upperStarUnitHom Λ g M) ≫
        upperStarUnitHom Λ f ((g)^*⟦Λ⟧.obj M) := by
  apply ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g)).homEquiv _ _).injective
  have hL := homEquiv_comp_conjugateEquiv_app
    ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
    (upperStarLowerStarAdjunction Λ (f ≫ g)) (upperStarComp Λ f g).hom
    (𝟙 (((g)^*⟦Λ⟧ ⋙ (f)^*⟦Λ⟧).obj M))
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarComp, Category.comp_id] at hL
  simp only [Adjunction.comp_homEquiv] at hL
  erw [Equiv.trans_apply] at hL
  have hL' := congrArg Mod.Hom.hom hL
  rw [Mod.comp_hom', lowerStarComp_hom_app_hom, upperStarLowerStarAdjunction_homEquiv_hom,
    upperStarLowerStarAdjunction_homEquiv_hom] at hL'
  erw [upperStarLowerStarAdjunction_homEquiv_hom] at hL'
  have hR := homEquiv_comp_conjugateEquiv_app
    ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f))
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
    (ProEtale.upperStarComp Ab.{u + 1} f g).hom
    ((f)^*[Ab.{u + 1}].map (upperStarUnitHom Λ g M) ≫ upperStarUnitHom Λ f ((g)^*⟦Λ⟧.obj M))
  rw [← conjugateIsoEquiv_apply_hom, ProEtale.conjugateIsoEquiv_upperStarComp] at hR
  simp only [Adjunction.comp_homEquiv] at hR
  erw [Equiv.trans_apply] at hR
  erw [← hR]
  conv_lhs => rw [Adjunction.homEquiv_unit]
  erw [← hL']
  erw [Mod.id_hom', Category.comp_id]
  have key : upperStarUnitHom Λ g M ≫
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app ((g)^*⟦Λ⟧.obj M).X ≫
        (f)_*[Ab.{u + 1}].map (upperStarUnitHom Λ f ((g)^*⟦Λ⟧.obj M)) =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
        ((f)^*[Ab.{u + 1}].map (upperStarUnitHom Λ g M) ≫
          upperStarUnitHom Λ f ((g)^*⟦Λ⟧.obj M)) := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp]
    exact (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.naturality_assoc
      (upperStarUnitHom Λ g M) _
  erw [key]
  conv_rhs => rw [Adjunction.homEquiv_unit]
  rfl

/-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` of the pullbacks of pro-étale sheaves is
monoidal: it is conjugate to the monoidal composition isomorphism of the pushforwards. -/
instance isMonoidal_sheafUpperStarComp_inv :
    NatTrans.IsMonoidal (ProEtale.upperStarComp Ab.{u + 1} f g).inv := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  exact isMonoidal_conjugateEquiv_symm _ _ (ProEtale.lowerStarComp Ab.{u + 1} f g).inv

/-- `isMonoidal_sheafUpperStarComp_inv`, in the form of the tensor comparisons of the strong
monoidal pullbacks. -/
@[reassoc]
lemma sheafUpperStarComp_hom_app_tensor_δ (P Q : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
    δ (f ≫ g)^*[Ab.{u + 1}] P Q ≫ ((ProEtale.upperStarComp Ab.{u + 1} f g).hom.app P ⊗ₘ
      (ProEtale.upperStarComp Ab.{u + 1} f g).hom.app Q) =
      (ProEtale.upperStarComp Ab.{u + 1} f g).hom.app (P ⊗ Q) ≫
        (f)^*[Ab.{u + 1}].map (δ (g)^*[Ab.{u + 1}] P Q) ≫ δ (f)^*[Ab.{u + 1}] _ _ := by
  have h := NatTrans.IsMonoidal.tensor (τ := (ProEtale.upperStarComp Ab.{u + 1} f g).inv) P Q
  have h' : ((ProEtale.upperStarComp Ab.{u + 1} f g).hom.app P ⊗ₘ
      (ProEtale.upperStarComp Ab.{u + 1} f g).hom.app Q) ≫
        Functor.LaxMonoidal.μ ((g)^*[Ab.{u + 1}] ⋙ (f)^*[Ab.{u + 1}]) P Q =
      Functor.LaxMonoidal.μ (f ≫ g)^*[Ab.{u + 1}] P Q ≫
        (ProEtale.upperStarComp Ab.{u + 1} f g).hom.app (P ⊗ Q) := by
    rw [← cancel_mono ((ProEtale.upperStarComp Ab.{u + 1} f g).inv.app (P ⊗ Q)), Category.assoc,
      h, ← Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
      id_tensorHom_id, Category.id_comp, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have e : (f)^*[Ab.{u + 1}].map (δ (g)^*[Ab.{u + 1}] P Q) ≫ δ (f)^*[Ab.{u + 1}] _ _ =
      δ ((g)^*[Ab.{u + 1}] ⋙ (f)^*[Ab.{u + 1}]) P Q := rfl
  rw [e, ← cancel_mono (Functor.LaxMonoidal.μ ((g)^*[Ab.{u + 1}] ⋙ (f)^*[Ab.{u + 1}]) P Q),
    Category.assoc, h', Functor.Monoidal.δ_μ_assoc, Category.assoc, Functor.Monoidal.δ_μ,
    Category.comp_id]

instance (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    IsIso (upperStarUnitHom Λ f M) :=
  ⟨((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app _).hom,
    extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f _, by
      rw [upperStarUnitHom, ← extendScalarsIsoComapInv_inv_app_hom, ← Mod.comp_hom',
        Iso.hom_inv_id_app]
      rfl⟩

/-- On underlying sheaves, the pullback of a map of module objects is the pullback of the
underlying map, after the units of the extensions of scalars. -/
@[reassoc]
lemma upperStarUnitHom_map_hom
    {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)} (h : M ⟶ N) :
    upperStarUnitHom Λ f M ≫ ((f)^*⟦Λ⟧.map h).hom =
      (f)^*[Ab.{u + 1}].map h.hom ≫ upperStarUnitHom Λ f N :=
  Mod.extendUnitHom_extendScalarsMap _ _

/-- **The composition isomorphism of the pullbacks of module objects is monoidal**: it commutes
with the tensor comparisons,
```
(f ≫ g)^* (A ⊗ B) ───────────────▶ (f ≫ g)^* A ⊗ (f ≫ g)^* B
        │                                    │
        ▼                                    ▼
f^* g^* (A ⊗ B) ──▶ f^* (g^* A ⊗ g^* B) ──▶ f^* g^* A ⊗ f^* g^* B
```
-/
@[reassoc]
lemma upperStarComp_hom_app_tensor_δ
    (A B : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    δ (f ≫ g)^*⟦Λ⟧ A B ≫ ((upperStarComp Λ f g).hom.app A ⊗ₘ (upperStarComp Λ f g).hom.app B) =
      (upperStarComp Λ f g).hom.app (A ⊗ B) ≫ (f)^*⟦Λ⟧.map (δ (g)^*⟦Λ⟧ A B) ≫
        δ (f)^*⟦Λ⟧ _ _ := by
  ext1
  rw [← cancel_epi ((f ≫ g)^*[Ab.{u + 1}].map (Mod.tensorObjπ A B) ≫
    upperStarUnitHom Λ (f ≫ g) (A ⊗ B))]
  rw [Mod.comp_hom', Category.assoc, Category.assoc,
    map_tensorObjπ_upperStarUnitHom_δ_hom_assoc, Mod.tensorObjπ_tensorHom_hom,
    tensorHom_comp_tensorHom_assoc, upperStarUnitHom_upperStarComp_hom_app_hom,
    upperStarUnitHom_upperStarComp_hom_app_hom, ← tensorHom_comp_tensorHom_assoc,
    ← tensorHom_comp_tensorHom_assoc, sheafUpperStarComp_hom_app_tensor_δ_assoc]
  rw [Mod.comp_hom', Mod.comp_hom', upperStarUnitHom_upperStarComp_hom_app_hom_assoc]
  have hn := (ProEtale.upperStarComp Ab.{u + 1} f g).hom.naturality (Mod.tensorObjπ A B)
  rw [reassoc_of% hn]
  rw [upperStarUnitHom_map_hom_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    map_tensorObjπ_upperStarUnitHom_δ_hom, Functor.map_comp_assoc, Functor.map_comp_assoc,
    map_tensorObjπ_upperStarUnitHom_δ_hom, Functor.OplaxMonoidal.δ_natural_assoc]
  rfl

/-- `upperStarComp_hom_app_tensor_δ` in terms of the tensorators. -/
@[reassoc]
lemma upperStarComp_hom_app_tensor_μ
    (A B : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    ((upperStarComp Λ f g).hom.app A ⊗ₘ (upperStarComp Λ f g).hom.app B) ≫
        Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ _ _ ≫
        (f)^*⟦Λ⟧.map (Functor.LaxMonoidal.μ (g)^*⟦Λ⟧ A B) =
      Functor.LaxMonoidal.μ (f ≫ g)^*⟦Λ⟧ A B ≫ (upperStarComp Λ f g).hom.app (A ⊗ B) := by
  rw [← cancel_epi (δ (f ≫ g)^*⟦Λ⟧ A B), reassoc_of% (upperStarComp_hom_app_tensor_δ Λ f g A B),
    Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.δ_μ_assoc, ← Functor.map_comp,
    Functor.Monoidal.δ_μ, CategoryTheory.Functor.map_id, Category.comp_id]

/-! ### The identity isomorphism -/

/-- The identity isomorphism `(𝟙 X)^* ≅ 𝟭` of the pullback of pro-étale sheaves is monoidal: it is
conjugate to the monoidal identity isomorphism of the pushforward. -/
instance isMonoidal_sheafUpperStarId_hom (X : Scheme.{u}) :
    NatTrans.IsMonoidal (ProEtale.upperStarId Ab.{u + 1} X).hom := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  exact isMonoidal_conjugateEquiv_symm _ _ (ProEtale.lowerStarId Ab.{u + 1} X).inv

/-- On underlying sheaves, the identity isomorphism `(𝟙 X)^* ≅ 𝟭` of the pullback of module
objects is that of the pullback of sheaves, after the unit of the extension of scalars. -/
lemma upperStarUnitHom_upperStarId_hom_app_hom (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    upperStarUnitHom Λ (𝟙 X) M ≫ ((upperStarId Λ X).hom.app M).hom =
      (ProEtale.upperStarId Ab.{u + 1} X).hom.app M.X := by
  apply ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X)).homEquiv _ _).injective
  have hL := homEquiv_comp_conjugateEquiv_app Adjunction.id
    (upperStarLowerStarAdjunction Λ (𝟙 X)) (upperStarId Λ X).hom (𝟙 M)
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarId] at hL
  simp only [Iso.symm_hom] at hL
  have hL' := congrArg Mod.Hom.hom hL
  rw [Mod.comp_hom', upperStarLowerStarAdjunction_homEquiv_hom] at hL'
  have hR := homEquiv_comp_conjugateEquiv_app Adjunction.id
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X)) (ProEtale.upperStarId Ab.{u + 1} X).hom
    (𝟙 M.X)
  rw [← conjugateIsoEquiv_apply_hom, ProEtale.conjugateIsoEquiv_upperStarId] at hR
  simp only [Iso.symm_hom] at hR
  erw [Category.comp_id] at hR
  erw [← hR]
  conv_lhs => rw [Adjunction.homEquiv_unit]
  erw [← hL']
  have hi : ((lowerStarId Λ X).inv.app M).hom =
      (ProEtale.lowerStarId Ab.{u + 1} X).inv.app M.X := by
    rw [← cancel_epi ((ProEtale.lowerStarId Ab.{u + 1} X).hom.app M.X), Iso.hom_inv_id_app]
    conv_lhs => rw [← lowerStarId_hom_app_hom]
    rw [← Mod.comp_hom', Iso.hom_inv_id_app]
    rfl
  erw [hi]
  rfl

/-- **The identity isomorphism of the pullback of module objects is monoidal**:
`(𝟙 X)^* (A ⊗ B) ⟶ (𝟙 X)^* A ⊗ (𝟙 X)^* B ⟶ A ⊗ B` is the identity isomorphism at `A ⊗ B`. -/
@[reassoc]
lemma upperStarId_hom_app_tensor_δ (X : Scheme.{u})
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    δ (𝟙 X)^*⟦Λ⟧ A B ≫ ((upperStarId Λ X).hom.app A ⊗ₘ (upperStarId Λ X).hom.app B) =
      (upperStarId Λ X).hom.app (A ⊗ B) := by
  ext1
  rw [← cancel_epi ((𝟙 X)^*[Ab.{u + 1}].map (Mod.tensorObjπ A B) ≫
    upperStarUnitHom Λ (𝟙 X) (A ⊗ B))]
  rw [Mod.comp_hom', Category.assoc, Category.assoc,
    map_tensorObjπ_upperStarUnitHom_δ_hom_assoc, Mod.tensorObjπ_tensorHom_hom,
    tensorHom_comp_tensorHom_assoc, upperStarUnitHom_upperStarId_hom_app_hom,
    upperStarUnitHom_upperStarId_hom_app_hom, upperStarUnitHom_upperStarId_hom_app_hom]
  have h := NatTrans.IsMonoidal.tensor (τ := (ProEtale.upperStarId Ab.{u + 1} X).hom) A.X B.X
  have h' : δ (𝟙 X)^*[Ab.{u + 1}] A.X B.X ≫ ((ProEtale.upperStarId Ab.{u + 1} X).hom.app A.X ⊗ₘ
      (ProEtale.upperStarId Ab.{u + 1} X).hom.app B.X) =
      (ProEtale.upperStarId Ab.{u + 1} X).hom.app (A.X ⊗ B.X) := by
    rw [← cancel_epi (Functor.LaxMonoidal.μ (𝟙 X)^*[Ab.{u + 1}] A.X B.X),
      Functor.Monoidal.μ_δ_assoc, h]
    exact (Category.comp_id _).symm
  rw [reassoc_of% h']
  exact ((ProEtale.upperStarId Ab.{u + 1} X).hom.naturality (Mod.tensorObjπ A B)).symm

/-- `upperStarId_hom_app_tensor_δ` in terms of the tensorator. -/
@[reassoc]
lemma upperStarId_hom_app_tensor_μ (X : Scheme.{u})
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((upperStarId Λ X).hom.app A ⊗ₘ (upperStarId Λ X).hom.app B) =
      Functor.LaxMonoidal.μ (𝟙 X)^*⟦Λ⟧ A B ≫ (upperStarId Λ X).hom.app (A ⊗ B) := by
  rw [← upperStarId_hom_app_tensor_δ, Functor.Monoidal.μ_δ_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
