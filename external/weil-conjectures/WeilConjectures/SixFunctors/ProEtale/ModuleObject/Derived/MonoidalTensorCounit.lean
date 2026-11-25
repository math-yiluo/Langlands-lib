/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
public import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived

/-!
# Tensor counits and the monoidal structure of left derived functors

Supplements to `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived`, used by the
finiteness of the derived pushforward (`boundedConstructible_rightDerivedLowerStar_obj`):

- `Functor.tensorCounitOfNatTrans`, `Functor.homotopyTensorCounit`,
  `Functor.homotopyTensorLeftDerivedCounit`: the tensor counits of a functor on complexes, on the
  homotopy category and for its left derived functor;
- `Functor.leftDerivedTensorUnitIso` and `leftDerivedMonoidalWithUnit`: the monoidal structure of a
  left derived functor with a prescribed unit comparison;
- `ProEtale.CondensedRing.upperStar_preservesFlat`: the pullback of module objects preserves flat
  objects.
-/

@[expose] public section

universe u v v₁ v₂

open CategoryTheory Limits MonoidalCategory

private lemma mapCochainComplexμIso_hom_f_eq_desc
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (G : C ⥤ D) [G.Additive] [G.Monoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (G.mapCochainComplexμIso K L).hom.f n =
      HomologicalComplex.mapBifunctorDesc (fun p q h ↦
        Functor.LaxMonoidal.μ G (K.X p) (L.X q) ≫
          G.map (HomologicalComplex.ιTensorObj K L p q n h)) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  exact Functor.ιTensorObj_mapCochainComplexμIso_hom_f G K L p q n h

/-- Apply a natural transformation in both tensor factors, then a tensor comparison. -/
@[irreducible]
noncomputable def CategoryTheory.Functor.tensorCounitOfNatTrans
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory E] (L : C ⥤ D) (F : D ⥤ E) (G : C ⥤ E)
    (τ : L ⋙ F ⟶ G) (T : C ⥤ C ⥤ E)
    (α : (((Functor.whiskeringLeft₂ E).obj G).obj G).obj (curriedTensor E) ⟶ T) :
    (((Functor.whiskeringLeft₂ E).obj L).obj L).obj
      ((((Functor.whiskeringLeft₂ E).obj F).obj F).obj (curriedTensor E)) ⟶ T :=
  (((Functor.whiskeringLeft₂ E).map τ).app (L ⋙ F)).app (curriedTensor E) ≫
    (((Functor.whiskeringLeft₂ E).obj G).map τ).app (curriedTensor E) ≫ α

private lemma tensorCounitOfNatTrans_eq_uncurry
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory E] (L : C ⥤ D) (F : D ⥤ E) (G : C ⥤ E)
    (τ : L ⋙ F ⟶ G) (T : C ⥤ C ⥤ E)
    (α : (((Functor.whiskeringLeft₂ E).obj G).obj G).obj (curriedTensor E) ⟶ T) :
    Functor.tensorCounitOfNatTrans L F G τ T α =
      (((Functor.whiskeringLeft₂ E).obj L).obj L).map (𝟙 _) ≫
        Functor.whiskeringLeft₂Equiv.symm
          (Functor.whiskeringLeft₂Equiv (𝟙 _) ≫
            Functor.whiskerRight (NatTrans.prod τ τ)
              (Functor.uncurry.obj (curriedTensor E)) ≫
            Functor.whiskeringLeft₂Equiv α) := by
  unfold Functor.tensorCounitOfNatTrans
  ext A B
  change (τ.app A ▷ F.obj (L.obj B)) ≫ (G.obj A ◁ τ.app B) ≫ (α.app A).app B =
    (𝟙 _) ≫ ((𝟙 _) ≫
      ((τ.app A ▷ F.obj (L.obj B)) ≫ (G.obj A ◁ τ.app B)) ≫ (α.app A).app B)
  simp only [Category.id_comp, Category.assoc]

/-- The tensorator of an additive monoidal functor, passed to the homotopy category
and followed by the lax tensorator of the derived localization. -/
@[irreducible]
noncomputable def CategoryTheory.Functor.homotopyTensorCounit
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive]
    [F.IsLeftAdjoint] [F.Monoidal]
    : (((Functor.whiskeringLeft₂ _).obj
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj
          (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _) ⟶
      (Functor.postcompose₂.obj
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _) :=
  (((Functor.whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
      (F.mapHomotopyCategory (.up ℤ))).map
        (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh) ≫
    (Functor.postcompose₂.obj DerivedCategory.Qh).map
      (asIso (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv

private lemma homotopyTensorCounit_app
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive]
    [F.IsLeftAdjoint] [F.Monoidal]
    (A B : HomotopyCategory C (.up ℤ)) :
    ((F.homotopyTensorCounit.app A).app B) =
    Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (F.mapCochainComplexμIso A.as B.as).hom) := by
  unfold Functor.homotopyTensorCounit
  obtain ⟨A, rfl⟩ := HomotopyCategory.quotient_obj_surjective A
  obtain ⟨B, rfl⟩ := HomotopyCategory.quotient_obj_surjective B
  change Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
    DerivedCategory.Qh.map
      (((asIso (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans
        (.up ℤ) F)).inv.app _).app _) = _
  congr 1
  apply DerivedCategory.Qh.congr_map
  simp only [Functor.mapCochainComplexμIso, Iso.symm_hom, Iso.app_inv,
    asIso_inv, NatIso.isIso_inv_app,
    Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app, ← Functor.map_inv,
    HomotopyCategory.quotient_obj_as]

/-- The counit of the derived tensor of two left derived functors, followed by the
homotopy-category tensor comparison. -/
@[irreducible]
noncomputable def CategoryTheory.Functor.homotopyTensorLeftDerivedCounit
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal]
    : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (Functor.derivedTensorLeftDerived F) ⟶
      (Functor.postcompose₂.obj
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _) :=
  Functor.tensorCounitOfNatTrans DerivedCategory.Qh F.leftDerivedFunctor
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) F.leftDerivedFunctorCounit _
    F.homotopyTensorCounit

/-- The tensor-unit comparison for the left derived functor of an exact monoidal functor. -/
@[irreducible]
noncomputable def CategoryTheory.Functor.leftDerivedTensorUnitIso
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal]
    : F.leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  asIso (F.leftDerivedFunctorCounit.app (𝟙_ _)) ≪≫
    DerivedCategory.Qh.mapIso
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app (𝟙_ _) ≪≫
        (HomotopyCategory.quotient _ _).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex F
              (ComplexShape.up ℤ) 0).app (𝟙_ _) ≪≫
            (HomologicalComplex.single _ _ 0).mapIso (Functor.Monoidal.εIso F).symm))

private lemma leftDerived₂Lift_congr
    {C₁ C₂ D₁ D₂ E : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂] [Category* E]
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
    [W₁.ContainsIdentities] [W₂.ContainsIdentities]
    {T : C₁ ⥤ C₂ ⥤ E} (F G : D₁ ⥤ D₂ ⥤ E)
    (α α' : (((Functor.whiskeringLeft₂ E).obj L₁).obj L₂).obj F ⟶ T)
    (β β' : (((Functor.whiskeringLeft₂ E).obj L₁).obj L₂).obj G ⟶ T)
    [F.IsLeftDerivedFunctor₂ α W₁ W₂] [F.IsLeftDerivedFunctor₂ α' W₁ W₂]
    (hα : α = α') (hβ : β = β') :
    F.leftDerived₂Lift α W₁ W₂ G β = F.leftDerived₂Lift α' W₁ W₂ G β' := by
  subst α'
  subst β'
  rfl

namespace CategoryTheory.Functor
open DerivedCategory LaxMonoidal OplaxMonoidal
variable {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.IsLeftAdjoint] [F.Monoidal] [F.PreservesFlat]

/-- The descended unit map is the counit followed by the ordinary unit comparison in degree zero. -/
lemma residueDerivedOplax_η_eq_tensorUnitIso :
    letI := residueDerivedOplax F
    η F.leftDerivedFunctor = (leftDerivedTensorUnitIso F).hom := by
  have := DerivedCategory.isIso_ε_Qh C
  have := DerivedCategory.isIso_ε_Qh D
  have hεC : ε (Qh (C := C)) = 𝟙 _ := rfl
  have hεD : ε (Qh (C := D)) = 𝟙 _ := rfl
  change F.leftDerivedFunctor.map (ε Qh) ≫ F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
    Qh.map (η (F.mapHomotopyCategory (.up ℤ))) ≫ CategoryTheory.inv (ε Qh) = _
  have hmapC : F.leftDerivedFunctor.map (ε (Qh (C := C))) = 𝟙 _ := by
    change F.leftDerivedFunctor.map (𝟙 _) = 𝟙 _
    exact F.leftDerivedFunctor.map_id _
  have hinvD : CategoryTheory.inv (ε (Qh (C := D))) = 𝟙 _ :=
    IsIso.inv_eq_of_hom_inv_id (by simpa only [Category.comp_id] using hεD)
  erw [hmapC, hinvD, Category.id_comp, Category.comp_id]
  simp only [leftDerivedTensorUnitIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom,
    mapHomotopyCategory_η, mapCochainComplex_η, mapCochainComplexεIso,
    Iso.trans_inv, Functor.mapIso_inv]
  congr 1
  apply Qh.congr_map
  change (HomotopyCategory.quotient D (.up ℤ)).map _ = _
  have hh : ((F.mapHomotopyCategoryFactors (.up ℤ)).app (𝟙_ _)).hom = 𝟙 _ := by
    simp [Functor.mapHomotopyCategoryFactors]
    rfl
  erw [hh, Category.id_comp]
  rfl

/-- The canonical derived monoidal structure with its unit maps written using the explicit
comparison `leftDerivedTensorUnitIso`. This preserves the definitional unit API. -/
@[instance_reducible]
noncomputable def leftDerivedMonoidalWithUnit : F.leftDerivedFunctor.Monoidal :=
  letI := residueDerivedMonoidal F
  have hη : η F.leftDerivedFunctor = (leftDerivedTensorUnitIso F).hom :=
    residueDerivedOplax_η_eq_tensorUnitIso F
  have hε : (leftDerivedTensorUnitIso F).inv = ε F.leftDerivedFunctor := by
    apply (cancel_mono (leftDerivedTensorUnitIso F).hom).1
    rw [Iso.inv_hom_id, ← hη, Monoidal.ε_η]
  Monoidal.copy (residueDerivedMonoidal F) (leftDerivedTensorUnitIso F).inv
    (μ F.leftDerivedFunctor) (leftDerivedTensorUnitIso F).hom (δ F.leftDerivedFunctor)
    hε rfl hη.symm rfl

variable [hR : (derivedTensorLeftDerived F).IsLeftDerivedFunctor₂
  F.homotopyTensorLeftDerivedCounit
  (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))]

omit hR in
private lemma homotopyTensorComparison_app_app_fac (A B : HomotopyCategory C (.up ℤ)) :
    ((F.leftDerivedTensorComparison.app (Qh.obj A)).app (Qh.obj B)) ≫
      (F.leftDerivedFunctorCounit.app A ⊗ₘ F.leftDerivedFunctorCounit.app B) ≫
      ((F.homotopyTensorCounit.app A).app B) =
    F.leftDerivedFunctor.map (μ Qh A B) ≫ F.leftDerivedFunctorCounit.app (A ⊗ B) := by
  unfold Functor.homotopyTensorCounit
  change ((F.leftDerivedTensorComparison.app (Qh.obj A)).app (Qh.obj B)) ≫
      (F.leftDerivedFunctorCounit.app A ⊗ₘ F.leftDerivedFunctorCounit.app B) ≫
      (μ Qh ((F.mapHomotopyCategory (.up ℤ)).obj A)
        ((F.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map (((asIso (mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv.app A).app B)) = _
  rw [F.leftDerivedTensorComparison_app_app_comp_tensorHom_assoc]
  have h := (asIso (mapHomotopyCategoryδNatTrans (.up ℤ) F)).hom_inv_id_app_app A B
  simp only [asIso_hom] at h
  rw [← Qh.map_comp, h]
  erw [Qh.map_id, Category.comp_id]

/-- Changing the target tensor counit by the inverse comonoidal comparison leaves the
canonical derived tensor comparison unchanged, by the derived universal property. -/
lemma homotopyTensorLeftDerivedLift_eq :
    (derivedTensorLeftDerived F).leftDerived₂Lift F.homotopyTensorLeftDerivedCounit
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))
      (leftDerivedDerivedTensor F) F.leftDerivedDerivedTensorCounit =
        F.leftDerivedTensorComparison := by
  apply Functor.leftDerived₂_ext (derivedTensorLeftDerived F)
    F.homotopyTensorLeftDerivedCounit
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))
  rw [Functor.leftDerived₂_fac]
  ext A B
  symm
  unfold Functor.homotopyTensorLeftDerivedCounit Functor.tensorCounitOfNatTrans
  change ((F.leftDerivedTensorComparison.app (Qh.obj A)).app (Qh.obj B)) ≫
      ((F.leftDerivedFunctorCounit.app A ▷ F.leftDerivedFunctor.obj (Qh.obj B)) ≫
      (Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj A) ◁ F.leftDerivedFunctorCounit.app B) ≫
      ((F.homotopyTensorCounit.app A).app B)) =
    F.leftDerivedFunctor.map (μ Qh A B) ≫ F.leftDerivedFunctorCounit.app (A ⊗ B)
  have h := homotopyTensorComparison_app_app_fac F A B
  erw [MonoidalCategory.tensorHom_def] at h
  simpa only [Functor.comp_obj, Category.assoc] using h

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open scoped CategoryTheory.Obj

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Instances

Direct instances for complexes of module objects over `Λ_Z`. Finding them from the generic
instances on `Mod` exceeds the default heartbeat limit, so they are recorded once here. -/

-- Cache the ambient existence properties used by every derived functor in the file.
local instance grothendieckModulesShortcut (Z : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

local instance flatResolutionModulesShortcut (Z : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

-- Reuse the already available pullback properties throughout these concrete constructions.
local instance upperStarAdditiveShortcut : (f)^*⟦Λ⟧.Additive := inferInstance

local instance upperStarFiniteLimitsShortcut : PreservesFiniteLimits (f)^*⟦Λ⟧ :=
  inferInstance

local instance upperStarFiniteColimitsShortcut : PreservesFiniteColimits (f)^*⟦Λ⟧ :=
  inferInstance

local instance upperStarLeftAdjointShortcut : (f)^*⟦Λ⟧.IsLeftAdjoint := inferInstance

-- Give tensor-colimit inference a direct path in the internal module category.
local instance preservesColimitsTensorLeftShortcut (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfSize.{0, 0} ((curriedTensor _).obj M) :=
  inferInstance

local instance preservesColimitsTensorRightShortcut (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfSize.{0, 0} ((curriedTensor _).flip.obj M) :=
  inferInstance

-- Cache the colimit compatibility proofs used repeatedly by total tensor products.
local instance hasTensorGradedShortcut (Z : Scheme.{u})
    (A B : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : A.HasTensor B :=
  inferInstance

local instance hasGoodTensorLeftShortcut (Z : Scheme.{u})
    (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasGoodTensor₁₂Tensor A B C :=
  inferInstance

local instance hasGoodTensorRightShortcut (Z : Scheme.{u})
    (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasGoodTensorTensor₂₃ A B C :=
  inferInstance

local instance hasTensorFourShortcut (Z : Scheme.{u})
    (A B C D : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasTensor₄ObjExt A B C D :=
  inferInstance

/-! ### Complexes -/

/-! ### The homotopy category -/

/-! ### Derived categories -/

/-- Pullback of module objects preserves flat objects. The coefficient ring comparison is an
isomorphism, so extension of scalars identifies with restriction along its inverse. Transport
flatness along this identification and apply `ProEtale.inverseImageModule_preservesFlat`. -/
lemma upperStar_preservesFlat : (f)^*⟦Λ⟧.PreservesFlat := by
  let G := (f)^*[Ab.{u + 1}]
  let R := condensedRingObj Λ Y
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  have h := ProEtale.inverseImageModule_preservesFlat f R (condensedRingObj Λ X) ρ
  let e : (f)^*⟦Λ⟧ ≅ Mod.mapModComap ρ :=
    Functor.isoWhiskerLeft (G.mapMod R)
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  exact ⟨fun hM ↦ (ObjectProperty.flat).prop_of_iso (e.symm.app _) (h.flat_obj hM)⟩

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma upperStarTensorComplexHom_eq
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B = ((f)^*⟦Λ⟧.mapCochainComplexμIso A B).hom := by
  ext n : 1
  exact (mapCochainComplexμIso_hom_f_eq_desc (f)^*⟦Λ⟧ A B n).symm

private lemma upperStarTensorCounit_eq :
    upperStarTensorCounit Λ f = (f)^*⟦Λ⟧.homotopyTensorCounit := by
  ext A B
  apply Eq.trans ?_ (homotopyTensorCounit_app (f)^*⟦Λ⟧ A B).symm
  change Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (upperStarTensorComplexHom Λ f A.as B.as)) = _
  congr 1
  apply DerivedCategory.Qh.congr_map
  apply (HomotopyCategory.quotient _ _).congr_map
  exact upperStarTensorComplexHom_eq Λ f A.as B.as

private lemma leftDerivedUpperStarTensorRightCounit_eq :
    leftDerivedUpperStarTensorRightCounit Λ f =
      (f)^*⟦Λ⟧.homotopyTensorLeftDerivedCounit := by
  unfold Functor.homotopyTensorLeftDerivedCounit
  change _ = Functor.tensorCounitOfNatTrans DerivedCategory.Qh
    (f)^*⟦Λ⟧.leftDerivedFunctor
    ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (f)^*⟦Λ⟧.leftDerivedFunctorCounit _ (f)^*⟦Λ⟧.homotopyTensorCounit
  exact (tensorCounitOfNatTrans_eq_uncurry DerivedCategory.Qh
    (f)^*⟦Λ⟧.leftDerivedFunctor
    ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (f)^*⟦Λ⟧.leftDerivedFunctorCounit _ (upperStarTensorCounit Λ f)).symm.trans
      (congrArg (Functor.tensorCounitOfNatTrans DerivedCategory.Qh
        (f)^*⟦Λ⟧.leftDerivedFunctor
        ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit _) (upperStarTensorCounit_eq Λ f))

private lemma leftDerivedUpperStarTensorLeftCounit_eq :
    leftDerivedUpperStarTensorLeftCounit Λ f =
      (f)^*⟦Λ⟧.leftDerivedDerivedTensorCounit := by
  ext A B
  exact ((f)^*⟦Λ⟧.leftDerivedDerivedTensorCounit_app_app A B).symm

/-! ### The monoidal structure -/

end AlgebraicGeometry.ProEtale.CondensedRing
