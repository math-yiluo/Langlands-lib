/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendChangeTransfer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived

/-!
# `Res_E(ℚ̄_ℓ,X ⊗_{F_X} Y)` as a filtered colimit of complexes

Let `ℓ` be a prime, `X` a scheme and `E, F ≤ G` finite subextensions of `ℚ̄_ℓ`. For a finite
subextension `k ⊇ E, F`, the adjoint transfers (`CategoryTheory.Adjunction.compIsoTransfer`) of
the transitivity isomorphisms of the extensions of scalars give `E_X`-linear maps
```
Res_{E→k}(k_X ⊗_{F_X} M) ⟶ Res_{E→k'}(k'_X ⊗_{F_X} M),   Res_{E→k}(k_X ⊗_{F_X} M) ⟶
Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} M)
```
(`ProEtale.subfieldExtendScalarsTransfer`, `ProEtale.subfieldExtendScalarsTransferToPadicAlgCl`),
whose underlying maps are `x ⊗ m ↦ x ⊗ m` (`Mod.extendChangeHom`). For a complex `Y` of
`F_X`-modules, these form a diagram of complexes of `E_X`-modules over the finite
subextensions `k ⊇ G` (`ProEtale.subfieldExtendScalarsDiagram`) with a cocone of vertex
`Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y)` (`ProEtale.subfieldExtendScalarsCocone`), which is a colimit cocone
(`ProEtale.isColimitSubfieldExtendScalarsCocone`): colimits of complexes are computed degreewise,
colimits of module objects on the underlying objects, and
`ℚ̄_ℓ,X ⊗_{F_X} M = colim_k k_X ⊗_{F_X} M` (`Mod.isColimitExtendScalarsColimitCocone`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- `x ⊗ m ↦ s(x) ⊗ m` is the identity for `s = 𝟙`. -/
lemma extendChangeHom_eq_id {S : C} [MonObj S] {φ : R ⟶ S} [IsMonHom φ]
    (s : S ⟶ S) [IsMonHom s] (hs : s = 𝟙 S) (h : φ ≫ s = φ) (M : Mod C R) :
    extendChangeHom s h M = 𝟙 _ := by
  subst hs
  exact extendChangeHom_id M

/-- `extendChangeHom` only depends on the morphism of algebras. -/
lemma extendChangeHom_congr {S S' : C} [MonObj S] [MonObj S'] {φ : R ⟶ S} {φ' : R ⟶ S'}
    [IsMonHom φ] [IsMonHom φ'] {s s' : S ⟶ S'} [IsMonHom s] [IsMonHom s'] (hs : s = s')
    (h : φ ≫ s = φ') (M : Mod C R) :
    extendChangeHom s h M = extendChangeHom s' (hs ▸ h) M := by
  subst hs
  rfl

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The inclusions `E_X ⟶ F_X ⟶ H_X` compose to the inclusion `E_X ⟶ H_X`. -/
@[reassoc]
lemma padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap {E F H : FiniteIntermediateField ℓ}
    (h₁ : E ≤ F) (h₂ : F ≤ H) :
    padicSubfieldRingObjMap X ℓ h₁ ≫ padicSubfieldRingObjMap X ℓ h₂ =
      padicSubfieldRingObjMap X ℓ (h₁.trans h₂) :=
  (coefficientMap_comp _ _ X).symm

/-- The inclusion `E_X ⟶ E_X` is the identity. -/
lemma padicSubfieldRingObjMap_refl (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObjMap X ℓ (le_refl E) = 𝟙 _ :=
  coefficientMap_id X

section Transfer

variable {E F k k' : FiniteIntermediateField ℓ}

/-- The `E_X`-linear map `Res_{E→k}(k_X ⊗_{F_X} M) ⟶ Res_{E→k'}(k'_X ⊗_{F_X} M)`,
`x ⊗ m ↦ x ⊗ m`, for `E, F ≤ k ≤ k'`. -/
noncomputable def subfieldExtendScalarsTransfer (hE : E ≤ k) (hF : F ≤ k) (hk : k ≤ k') :
    Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF) ⋙
        Mod.comap (padicSubfieldRingObjMap X ℓ hE) ⟶
      Mod.extendScalars (padicSubfieldRingObjMap X ℓ (hF.trans hk)) ⋙
        Mod.comap (padicSubfieldRingObjMap X ℓ (hE.trans hk)) :=
  Adjunction.compIsoTransferNatTrans (Mod.extendRestrictAdjunction _)
    (Mod.extendRestrictAdjunction _)
    (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ hE hk))
    (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ hF hk))

/-- The underlying map of `subfieldExtendScalarsTransfer` is `x ⊗ m ↦ x ⊗ m`. -/
lemma subfieldExtendScalarsTransfer_app_hom (hE : E ≤ k) (hF : F ≤ k) (hk : k ≤ k')
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :
    ((subfieldExtendScalarsTransfer X ℓ hE hF hk).app M).hom =
      Mod.extendChangeHom (padicSubfieldRingObjMap X ℓ hk)
        (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ hF hk) M :=
  Mod.compIsoTransfer_extendRestrictAdjunction_hom _ _ M

/-- The `E_X`-linear map `Res_{E→k}(k_X ⊗_{F_X} M) ⟶ Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} M)`,
`x ⊗ m ↦ x ⊗ m`, for `E, F ≤ k`. -/
noncomputable def subfieldExtendScalarsTransferToPadicAlgCl (hE : E ≤ k) (hF : F ≤ k) :
    Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF) ⋙
        Mod.comap (padicSubfieldRingObjMap X ℓ hE) ⟶
      Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F) ⋙
        Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E) :=
  Adjunction.compIsoTransferNatTrans (Mod.extendRestrictAdjunction _)
    (Mod.extendRestrictAdjunction _)
    (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ hE))
    (Mod.extendScalarsCompIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ hF))

/-- The underlying map of `subfieldExtendScalarsTransferToPadicAlgCl` is `x ⊗ m ↦ x ⊗ m`. -/
lemma subfieldExtendScalarsTransferToPadicAlgCl_app_hom (hE : E ≤ k) (hF : F ≤ k)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :
    ((subfieldExtendScalarsTransferToPadicAlgCl X ℓ hE hF).app M).hom =
      Mod.extendChangeHom (padicSubfieldRingObjToPadicAlgCl X ℓ k)
        (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ hF) M :=
  Mod.compIsoTransfer_extendRestrictAdjunction_hom _ _ M


/-- The transfer `Res_{E→k}(k_X ⊗_{F_X} M) ⟶ Res_{E→k}(k_X ⊗_{F_X} M)` is the identity. -/
lemma subfieldExtendScalarsTransfer_app_refl (hE : E ≤ k) (hF : F ≤ k)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :
    (subfieldExtendScalarsTransfer X ℓ hE hF (le_refl k)).app M = 𝟙 _ := by
  refine Mod.hom_ext _ _ ?_
  rw [subfieldExtendScalarsTransfer_app_hom]
  exact Mod.extendChangeHom_eq_id _ (padicSubfieldRingObjMap_refl X ℓ k) _ _

/-- The transfers are compatible with composition. -/
lemma subfieldExtendScalarsTransfer_app_comp {k'' : FiniteIntermediateField ℓ} (hE : E ≤ k)
    (hF : F ≤ k) (hk : k ≤ k') (hk' : k' ≤ k'')
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :
    (subfieldExtendScalarsTransfer X ℓ hE hF hk).app M ≫
        (subfieldExtendScalarsTransfer X ℓ (hE.trans hk) (hF.trans hk) hk').app M =
      (subfieldExtendScalarsTransfer X ℓ hE hF (hk.trans hk')).app M := by
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', subfieldExtendScalarsTransfer_app_hom, subfieldExtendScalarsTransfer_app_hom,
    subfieldExtendScalarsTransfer_app_hom, Mod.extendChangeHom_comp]
  exact Mod.extendChangeHom_congr
    (padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _) _ _

/-- The transfers are compatible with the transfers to `ℚ̄_ℓ`. -/
lemma subfieldExtendScalarsTransfer_app_comp_toPadicAlgCl (hE : E ≤ k) (hF : F ≤ k)
    (hk : k ≤ k')
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :
    (subfieldExtendScalarsTransfer X ℓ hE hF hk).app M ≫
        (subfieldExtendScalarsTransferToPadicAlgCl X ℓ (hE.trans hk) (hF.trans hk)).app M =
      (subfieldExtendScalarsTransferToPadicAlgCl X ℓ hE hF).app M := by
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', subfieldExtendScalarsTransfer_app_hom,
    subfieldExtendScalarsTransferToPadicAlgCl_app_hom,
    subfieldExtendScalarsTransferToPadicAlgCl_app_hom, Mod.extendChangeHom_comp]
  exact Mod.extendChangeHom_congr (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ hk) _ _
end Transfer

section Diagram

variable {E F G : FiniteIntermediateField ℓ} (hE : E ≤ G) (hF : F ≤ G)
  (Y : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)

/-- The diagram `k ↦ Res_{E→k}(k_X ⊗_{F_X} Y)` of complexes of `E_X`-modules over the finite
subextensions `k ⊇ G`, with the transition maps `x ⊗ y ↦ x ⊗ y`. -/
@[simps obj]
noncomputable def subfieldExtendScalarsDiagram :
    PadicSubfieldAbove ℓ G ⥤
      CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ
      where
  obj k := ((Mod.comap (padicSubfieldRingObjMap X ℓ (hE.trans k.property))).mapHomologicalComplex
    _).obj (((Mod.extendScalars
      (padicSubfieldRingObjMap X ℓ (hF.trans k.property))).mapHomologicalComplex _).obj Y)
  map {k k'} g :=
    { f n := (subfieldExtendScalarsTransfer X ℓ (hE.trans k.property) (hF.trans k.property)
        (leOfHom ((ObjectProperty.ι _).map g))).app (Y.X n)
      comm' i j _ := ((subfieldExtendScalarsTransfer X ℓ (hE.trans k.property)
        (hF.trans k.property) (leOfHom ((ObjectProperty.ι _).map g))).naturality (Y.d i j)).symm }
  map_id k := by
    ext n : 1
    exact subfieldExtendScalarsTransfer_app_refl X ℓ _ _ _
  map_comp g g' := by
    ext n : 1
    exact (subfieldExtendScalarsTransfer_app_comp X ℓ _ _ _ _ _).symm

/-- The cocone of the diagram `k ↦ Res_{E→k}(k_X ⊗_{F_X} Y)` with vertex
`Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y)`, given by the maps `x ⊗ y ↦ x ⊗ y`. -/
@[simps pt]
noncomputable def subfieldExtendScalarsCocone :
    Cocone (subfieldExtendScalarsDiagram X ℓ hE hF Y) where
  pt := ((Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomologicalComplex _).obj
    (((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).mapHomologicalComplex _).obj Y)
  ι :=
    { app k :=
        { f n := (subfieldExtendScalarsTransferToPadicAlgCl X ℓ (hE.trans k.property)
            (hF.trans k.property)).app (Y.X n)
          comm' i j _ := ((subfieldExtendScalarsTransferToPadicAlgCl X ℓ (hE.trans k.property)
            (hF.trans k.property)).naturality (Y.d i j)).symm }
      naturality k k' g := by
        ext n : 1
        exact (subfieldExtendScalarsTransfer_app_comp_toPadicAlgCl X ℓ _ _ _ _).trans
          (Category.comp_id _).symm }

/-- The components of `subfieldExtendScalarsCocone`. -/
lemma subfieldExtendScalarsCocone_ι_app_f (k : PadicSubfieldAbove ℓ G) (n : ℤ) :
    ((subfieldExtendScalarsCocone X ℓ hE hF Y).ι.app k).f n =
      (subfieldExtendScalarsTransferToPadicAlgCl X ℓ (hE.trans k.property)
        (hF.trans k.property)).app (Y.X n) := rfl

/-- The diagram `k ↦ k_X ⊗_{F_X} Y^n` of `Mod.isColimitExtendScalarsColimitCocone` is the
underlying diagram of `subfieldExtendScalarsDiagram` in degree `n`. -/
noncomputable def subfieldExtendScalarsDiagramForgetIso (n : ℤ) :
    Mod.extendScalarsColimitDiagram (padicSubfieldAboveRingObjFunctor ℓ G X)
      (fun k ↦ padicSubfieldRingObjMap X ℓ (hF.trans k.property))
      (fun _ ↦ padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _) (Y.X n) ≅
    (subfieldExtendScalarsDiagram X ℓ hE hF Y ⋙ HomologicalComplex.eval _ _ n) ⋙ Mod.forget _ :=
  NatIso.ofComponents (fun k ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (subfieldExtendScalarsTransfer_app_hom X ℓ _ _ _ _).symm




/-- The vertex of `Mod.extendScalarsColimitCocone` is that of the underlying cocone of
`subfieldExtendScalarsCocone` in degree `n`. (A separate definition keeps the kernel checks
cheap.) -/
noncomputable def subfieldExtendScalarsCoconeForgetPtIso (n : ℤ) :
    (Mod.extendScalarsColimitCocone (padicSubfieldAboveRingObjFunctor ℓ G X)
    (fun k ↦ padicSubfieldRingObjMap X ℓ (hF.trans k.property))
    (fun _ ↦ padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _) (Y.X n)
    (fun k ↦ padicSubfieldRingObjToPadicAlgCl X ℓ k.obj)
    (fun g ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (leOfHom ((ObjectProperty.ι _).map g)))
    (padicSubfieldRingObjToPadicAlgCl X ℓ F)
    (fun k ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (hF.trans k.property))).pt ≅
    ((Mod.forget _).mapCocone ((HomologicalComplex.eval _ _ n).mapCocone
      (subfieldExtendScalarsCocone X ℓ hE hF Y))).pt :=
  Iso.refl _

/-- The isomorphism `subfieldExtendScalarsCoconeForgetPtIso` is the identity. -/
lemma subfieldExtendScalarsCoconeForgetPtIso_hom (n : ℤ) :
    (subfieldExtendScalarsCoconeForgetPtIso X ℓ hE hF Y n).hom = 𝟙 _ := rfl


/-- The cocone `Mod.extendScalarsColimitCocone`, transported along
`subfieldExtendScalarsDiagramForgetIso`, is the underlying cocone of `subfieldExtendScalarsCocone`
in degree `n`. -/
noncomputable def subfieldExtendScalarsCoconeForgetIso (n : ℤ) :
    (Cocone.precompose (subfieldExtendScalarsDiagramForgetIso X ℓ hE hF Y n).inv).obj
      (Mod.extendScalarsColimitCocone (padicSubfieldAboveRingObjFunctor ℓ G X)
    (fun k ↦ padicSubfieldRingObjMap X ℓ (hF.trans k.property))
    (fun _ ↦ padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap X ℓ _ _) (Y.X n)
    (fun k ↦ padicSubfieldRingObjToPadicAlgCl X ℓ k.obj)
    (fun g ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (leOfHom ((ObjectProperty.ι _).map g)))
    (padicSubfieldRingObjToPadicAlgCl X ℓ F)
    (fun k ↦ padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (hF.trans k.property))) ≅
    ((Mod.forget _).mapCocone ((HomologicalComplex.eval _ _ n).mapCocone
      (subfieldExtendScalarsCocone X ℓ hE hF Y))) :=
  Cocone.ext (subfieldExtendScalarsCoconeForgetPtIso X ℓ hE hF Y n) fun k ↦ by
    simp only [subfieldExtendScalarsCoconeForgetPtIso_hom,
      Cocone.precompose_obj_ι, NatTrans.comp_app, subfieldExtendScalarsDiagramForgetIso,
      NatIso.ofComponents_inv_app, Iso.refl_inv,
      Mod.extendScalarsColimitCocone_ι_app, Functor.mapCocone_ι_app, HomologicalComplex.eval_map,
      Mod.forget_map, subfieldExtendScalarsCocone_ι_app_f,
      subfieldExtendScalarsTransferToPadicAlgCl_app_hom]
    exact (Category.comp_id _).trans (Category.id_comp _)

/-- **`Res_E(ℚ̄_ℓ,X ⊗_{F_X} Y) = colim_{k ⊇ G} Res_E(k_X ⊗_{F_X} Y)`** as complexes of
`E_X`-modules. -/
noncomputable def isColimitSubfieldExtendScalarsCocone :
    IsColimit (subfieldExtendScalarsCocone X ℓ hE hF Y) :=
  HomologicalComplex.isColimitOfEval _ _ fun n ↦ isColimitOfReflects (Mod.forget _)
    (IsColimit.equivOfNatIsoOfIso (subfieldExtendScalarsDiagramForgetIso X ℓ hE hF Y n) _ _
      (subfieldExtendScalarsCoconeForgetIso X ℓ hE hF Y n)
      (Mod.isColimitExtendScalarsColimitCocone _ _ _ (Y.X n) _ _ _ _
        (isColimitPadicSubfieldAboveRingObjCocone ℓ G X)))
end Diagram

end AlgebraicGeometry.ProEtale
