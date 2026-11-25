/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-!
# Extension of scalars to a colimit of algebras

Let `C` be a braided monoidal category whose tensor product preserves colimits, `R` a commutative
algebra object and `M` an `R`-module object.

For a morphism of algebras `s : S ⟶ S'` under `R`, i.e. with `φ ≫ s = φ'`, the map
`S ⊗_R M ⟶ S' ⊗_R M`, `x ⊗ m ↦ s(x) ⊗ m`, is `CategoryTheory.Mod.extendChangeHom`; it is
compatible with the units (`CategoryTheory.Mod.extendUnitHom_extendChangeHom`), with composition
(`CategoryTheory.Mod.extendChangeHom_comp`), and `s`-semilinear, so it is a morphism of
`S`-modules `S ⊗_R M ⟶ Res_s(S' ⊗_R M)` (`CategoryTheory.Mod.extendChange`).

If `T = colim_j S_j` is a colimit of `R`-algebras (in `C`, the transition maps and cocone maps
being morphisms of algebras under `R`), then `T ⊗_R M = colim_j (S_j ⊗_R M)` in `C`
(`CategoryTheory.Mod.isColimitExtendScalarsColimitCocone`): the tensor product commutes with
colimits, and colimits commute with the coequalizers defining `- ⊗_R M`.
-/

@[expose] public section

universe v₁ u₁

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R : C} [MonObj R] [IsCommMonObj R]

section Change

variable {S S' : C} [MonObj S] [MonObj S'] {φ : R ⟶ S} {φ' : R ⟶ S'} [IsMonHom φ]
  [IsMonHom φ'] (s : S ⟶ S') [IsMonHom s] (h : φ ≫ s = φ') (M : Mod C R)

omit [IsMonHom φ] in
include h in
/-- `s ⊗ M : S ⊗ M ⟶ S' ⊗ M ⟶ S' ⊗_R M` coequalizes the two actions of `R`. -/
lemma extendChangeHom_condition :
    (S ◁ φ ≫ μ[S]) ▷ M.X ≫ s ▷ M.X ≫ extendπ φ' M =
      ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X]) ≫ s ▷ M.X ≫ extendπ φ' M := by
  have h₁ : (S ◁ φ ≫ μ[S]) ≫ s = s ▷ R ≫ S' ◁ φ' ≫ μ[S'] := by
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, ← h, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [whisker_exchange_assoc]
  rw [← comp_whiskerRight_assoc, h₁, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc (S' ◁ φ'), extendπ_condition, Category.assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc, Category.assoc]

/-- The map `S ⊗_R M ⟶ S' ⊗_R M`, `x ⊗ m ↦ s(x) ⊗ m`, induced by a morphism of algebras
`s : S ⟶ S'` under `R`. -/
noncomputable def extendChangeHom : (extendScalarsObj φ M).X ⟶ (extendScalarsObj φ' M).X :=
  extendDescHom φ (s ▷ M.X ≫ extendπ φ' M) (extendChangeHom_condition s h M)

@[reassoc (attr := simp)]
lemma extendπ_extendChangeHom :
    extendπ φ M ≫ extendChangeHom s h M = s ▷ M.X ≫ extendπ φ' M :=
  extendπ_extendDescHom _ _ _

/-- The map `S ⊗_R M ⟶ S' ⊗_R M` is compatible with the units. -/
@[reassoc (attr := simp)]
lemma extendUnitHom_extendChangeHom :
    extendUnitHom φ M ≫ extendChangeHom s h M = extendUnitHom φ' M := by
  rw [extendUnitHom, Category.assoc, Category.assoc, extendπ_extendChangeHom,
    ← comp_whiskerRight_assoc, IsMonHom.one_hom, extendUnitHom]

/-- The map `S ⊗_R M ⟶ S' ⊗_R M` is `s`-semilinear. -/
@[reassoc]
lemma smul_extendChangeHom :
    γ[S,(extendScalarsObj φ M).X] ≫ extendChangeHom s h M =
      S ◁ extendChangeHom s h M ≫ s ▷ _ ≫ γ[S',(extendScalarsObj φ' M).X] := by
  rw [← cancel_epi (S ◁ extendπ φ M), whiskerLeft_extendπ_smul_assoc, extendπ_extendChangeHom,
    ← whiskerLeft_comp_assoc, extendπ_extendChangeHom, whiskerLeft_comp_assoc,
    whisker_exchange_assoc, whiskerLeft_extendπ_smul, associator_inv_naturality_left_assoc,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, IsMonHom.mul_hom,
    MonoidalCategory.tensorHom_def']
  simp only [comp_whiskerRight, Category.assoc]

/-- The map `S ⊗_R M ⟶ S' ⊗_R M`, as a morphism of `S`-modules `S ⊗_R M ⟶ Res_s(S' ⊗_R M)`. -/
noncomputable def extendChange :
    extendScalarsObj φ M ⟶ (comap s).obj (extendScalarsObj φ' M) :=
  Hom.mk' (extendChangeHom s h M) (smul_extendChangeHom s h M)

@[simp]
lemma extendChange_hom : (extendChange s h M).hom = extendChangeHom s h M := rfl

variable {S'' : C} [MonObj S''] {φ'' : R ⟶ S''} [IsMonHom φ''] (s' : S' ⟶ S'') [IsMonHom s']
  (h' : φ' ≫ s' = φ'')

/-- The maps `S ⊗_R M ⟶ S' ⊗_R M` are compatible with composition. -/
@[reassoc]
lemma extendChangeHom_comp :
    extendChangeHom s h M ≫ extendChangeHom s' h' M =
      extendChangeHom (s ≫ s') (by rw [← Category.assoc, h, h']) M := by
  rw [← cancel_epi (extendπ φ M), extendπ_extendChangeHom_assoc, extendπ_extendChangeHom,
    extendπ_extendChangeHom, comp_whiskerRight_assoc]

lemma extendChangeHom_id :
    extendChangeHom (𝟙 S) (Category.comp_id φ) M = 𝟙 _ := by
  rw [← cancel_epi (extendπ φ M), extendπ_extendChangeHom, id_whiskerRight, Category.id_comp,
    Category.comp_id]

end Change

section Colimit

variable {J : Type} [SmallCategory J] (S : J ⥤ C) [∀ j, MonObj (S.obj j)]
  [∀ {j k : J} (g : j ⟶ k), IsMonHom (S.map g)] (φ : ∀ j, R ⟶ S.obj j) [∀ j, IsMonHom (φ j)]
  (hφ : ∀ {j k : J} (g : j ⟶ k), φ j ≫ S.map g = φ k) (M : Mod C R)

/-- The diagram `j ↦ S_j ⊗_R M` attached to a diagram of `R`-algebras `j ↦ S_j`. -/
@[simps]
noncomputable def extendScalarsColimitDiagram : J ⥤ C where
  obj j := (extendScalarsObj (φ j) M).X
  map g := extendChangeHom (S.map g) (hφ g) M
  map_id j := by
    rw [← cancel_epi (extendπ (φ j) M), extendπ_extendChangeHom, S.map_id, id_whiskerRight,
      Category.id_comp, Category.comp_id]
  map_comp g g' := by
    rw [extendChangeHom_comp]
    rw [← cancel_epi (extendπ _ M), extendπ_extendChangeHom, extendπ_extendChangeHom, S.map_comp]

variable {T : C} [MonObj T] (ι : ∀ j, S.obj j ⟶ T)
  (hι : ∀ {j k : J} (g : j ⟶ k), S.map g ≫ ι k = ι j)

/-- The cocone with vertex `T` given by maps `ι j : S_j ⟶ T`. -/
@[simps]
def algCocone : Cocone S where
  pt := T
  ι :=
    { app := ι
      naturality j k g := by simpa using hι g }

variable [∀ j, IsMonHom (ι j)] (ψ : R ⟶ T) [IsMonHom ψ] (hψ : ∀ j, φ j ≫ ι j = ψ)

/-- The cocone `S_j ⊗_R M ⟶ T ⊗_R M` attached to a cocone of `R`-algebras `S_j ⟶ T`. -/
@[simps]
noncomputable def extendScalarsColimitCocone :
    Cocone (extendScalarsColimitDiagram S φ hφ M) where
  pt := (extendScalarsObj ψ M).X
  ι :=
    { app j := extendChangeHom (ι j) (hψ j) M
      naturality j k g := by
        dsimp only [Functor.const_obj_obj]
        rw [Functor.const_obj_map, Category.comp_id, extendScalarsColimitDiagram_map,
          extendChangeHom_comp]
        rw [← cancel_epi (extendπ _ M), extendπ_extendChangeHom, extendπ_extendChangeHom, hι] }

/-- The cocone `S_j ⊗ M ⟶ s.pt` induced by a cocone `S_j ⊗_R M ⟶ s.pt`. -/
@[simps]
noncomputable def extendScalarsColimitTensorCocone
    (s : Cocone (extendScalarsColimitDiagram S φ hφ M)) : Cocone (S ⋙ tensorRight M.X) where
  pt := s.pt
  ι :=
    { app j := extendπ (φ j) M ≫ s.ι.app j
      naturality j k g := by
        dsimp
        rw [Category.comp_id, ← s.w g, extendScalarsColimitDiagram_map,
          extendπ_extendChangeHom_assoc] }

/-- **Extension of scalars to a colimit of algebras**: if `T = colim_j S_j` in `C`, then
`T ⊗_R M = colim_j (S_j ⊗_R M)` in `C`. -/
noncomputable def isColimitExtendScalarsColimitCocone (hc : IsColimit (algCocone S ι hι)) :
    IsColimit (extendScalarsColimitCocone S φ hφ M ι hι ψ hψ) := by
  let hTM := isColimitOfPreserves (tensorRight M.X) hc
  let hTRM := isColimitOfPreserves (tensorRight R ⋙ tensorRight M.X) hc
  let d (s : Cocone (extendScalarsColimitDiagram S φ hφ M)) : T ⊗ M.X ⟶ s.pt :=
    hTM.desc (extendScalarsColimitTensorCocone S φ hφ M s)
  have hd (s : Cocone (extendScalarsColimitDiagram S φ hφ M)) (j : J) :
      ι j ▷ M.X ≫ d s = extendπ (φ j) M ≫ s.ι.app j :=
    hTM.fac (extendScalarsColimitTensorCocone S φ hφ M s) j
  have hg (s : Cocone (extendScalarsColimitDiagram S φ hφ M)) :
      (T ◁ ψ ≫ μ[T]) ▷ M.X ≫ d s = ((α_ T R M.X).hom ≫ T ◁ γ[R,M.X]) ≫ d s := by
    refine hTRM.hom_ext fun j ↦ ?_
    change (ι j ▷ R) ▷ M.X ≫ _ = (ι j ▷ R) ▷ M.X ≫ _
    have h₁ : ι j ▷ R ≫ T ◁ ψ ≫ μ[T] = (S.obj j ◁ φ j ≫ μ[S.obj j]) ≫ ι j := by
      rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, ← hψ j,
        whiskerLeft_comp]
      simp only [Category.assoc]
      rw [whisker_exchange_assoc]
    rw [← comp_whiskerRight_assoc, h₁, comp_whiskerRight_assoc, hd, extendπ_condition_assoc]
    simp only [Category.assoc]
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, hd]
  exact
    { desc s := extendDescHom ψ (d s) (hg s)
      fac s j := by
        rw [← cancel_epi (extendπ (φ j) M), extendScalarsColimitCocone_ι_app,
          extendπ_extendChangeHom_assoc, extendπ_extendDescHom, hd]
      uniq s m hm := by
        rw [← cancel_epi (extendπ ψ M), extendπ_extendDescHom]
        refine hTM.hom_ext fun j ↦ ?_
        change ι j ▷ M.X ≫ _ = ι j ▷ M.X ≫ _
        rw [hd, ← hm j, extendScalarsColimitCocone_ι_app, extendπ_extendChangeHom_assoc] }

end Colimit

end CategoryTheory.Mod
