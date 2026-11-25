/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# Extension of scalars along a finite free algebra

Let `φ : R ⟶ S` be a morphism of commutative algebra objects and `s₁, …, sₙ : 𝟙 ⟶ S` global
sections of `S` forming a basis of `S` over `R`: the map `Rⁿ ⟶ S`, `(rᵢ) ↦ ∑ φ(rᵢ) sᵢ`, is an
isomorphism. Then for every `R`-module object `M`, the map `Mⁿ ⟶ S ⊗_R M`,
`(mᵢ) ↦ ∑ sᵢ • (1 ⊗ mᵢ)`, is an isomorphism (`Mod.isIso_biproductDesc_extendUnitHom_globalSmul`).

Indeed the underlying object of `S ⊗_R M` is that of `S ⊗_R M` with `S` regarded as an
`R`-module (`Mod.extendForgetTensorObjIso`), and the relative tensor product is additive.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj S] in
/-- `1 ⊗ m ↦ σ • (1 ⊗ m)` is `m ↦ σ ⊗ m`. -/
lemma extendUnitHom_globalSmul (σ : 𝟙_ C ⟶ S) (M : Mod C R) :
    extendUnitHom φ M ≫ globalSmul σ (extendScalarsObj φ M) =
      (λ_ M.X).inv ≫ σ ▷ M.X ≫ extendπ φ M := by
  rw [globalSmul, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  erw [whiskerLeft_extendUnitHom_smul']

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
/-- The underlying morphism of the left unitor inverse `M ⟶ R ⊗_R M`. -/
lemma leftUnitor_inv_hom_eq (M : Mod C R) :
    (λ_ M).inv.hom = (λ_ M.X).inv ≫ η[R] ▷ M.X ≫ tensorObjπ (regular R) M := by
  have h : ((λ_ M).inv ≫ (λ_ M).hom).hom = 𝟙 _ := by rw [Iso.inv_hom_id]; rfl
  rw [comp_hom'] at h
  rw [← cancel_mono (λ_ M).hom.hom, h, Category.assoc, Category.assoc]
  erw [tensorObjπ_regular_leftUnitor_hom]
  rw [one_act, Iso.inv_hom_id]

omit [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj R] in
/-- The map `r ↦ φ(r) σ` is `φ` followed by the multiplication by `σ`. -/
lemma regularLift_comap_regular_hom (σ : 𝟙_ C ⟶ S) :
    (regularLift ((comap φ).obj (regular S)) σ).hom = φ ≫ globalSmul σ (regular S) := by
  have h : (ρ_ S).inv ≫ S ◁ σ ≫ μ[S] = (λ_ S).inv ≫ σ ▷ S ≫ μ[S] := by
    conv_lhs => rw [← IsCommMonObj.mul_comm S]
    rw [BraidedCategory.braiding_naturality_right_assoc, rightUnitor_inv_braiding_assoc]
  change (ρ_ R).inv ≫ R ◁ σ ≫ φ ▷ S ≫ μ[S] = φ ≫ (λ_ S).inv ≫ σ ▷ S ≫ μ[S]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc, h]

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
/-- The image of `m` under `M ≅ R ⊗_R M ⟶ φ^* S ⊗_R M ≅ S ⊗_R M`, where the middle map is
induced by `r ↦ φ(r) σ`, is `σ ⊗ m`. -/
lemma leftUnitor_inv_whiskerRight_regularLift_extendForgetTensorObjIso_inv (σ : 𝟙_ C ⟶ S)
    (M : Mod C R) :
    ((λ_ M).inv ≫ regularLift ((comap φ).obj (regular S)) σ ▷ M).hom ≫
        (extendForgetTensorObjIso φ M).inv =
      (λ_ M.X).inv ≫ σ ▷ M.X ≫ extendπ φ M := by
  have h₁ : tensorObjπ ((comap φ).obj (regular S)) M ≫ (extendForgetTensorObjIso φ M).inv =
      extendπ φ M := by
    have : extendπ φ M ≫ (extendForgetTensorObjIso φ M).hom =
        tensorObjπ ((comap φ).obj (regular S)) M := by
      simp only [extendForgetTensorObjIso, extendπ_extendDescHom]
    rw [← this, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [comp_hom', leftUnitor_inv_hom_eq]
  simp only [Category.assoc]
  rw [tensorObjπ_whiskerRight_assoc, h₁, ← comp_whiskerRight_assoc]
  erw [one_comp_regularLift]

omit [Abelian.HasFunctorialFlatResolution C] in
/-- **Extension of scalars along a finite free algebra**: if global sections `s₁, …, sₙ` of `S`
form a basis of `S` over `R`, then `Mⁿ ⟶ S ⊗_R M`, `(mᵢ) ↦ ∑ sᵢ • (1 ⊗ mᵢ)`, is an
isomorphism for every `R`-module object `M`. -/
theorem isIso_biproductDesc_extendUnitHom_globalSmul {n : ℕ} (s : Fin n → (𝟙_ C ⟶ S))
    (hs : IsIso (biproduct.desc fun i ↦ φ ≫ globalSmul (s i) (regular S) :
      ⨁ (fun _ : Fin n ↦ R) ⟶ S))
    (M : Mod C R) :
    IsIso (biproduct.desc fun i ↦ extendUnitHom φ M ≫ globalSmul (s i) (extendScalarsObj φ M) :
      ⨁ (fun _ : Fin n ↦ M.X) ⟶ (extendScalarsObj φ M).X) := by
  let P := (comap φ).obj (regular S)
  let J : Fin n → (𝟙_ (Mod C R) ⟶ P) := fun i ↦ regularLift P (s i)
  have hJ : IsIso (biproduct.desc J) := by
    have : IsIso ((forget R).map (biproduct.desc J)) := by
      rw [← biproduct.mapBiproduct_hom_desc]
      have e : (fun j ↦ (forget R).map (J j)) = fun j ↦ φ ≫ globalSmul (s j) (regular S) :=
        funext fun j ↦ regularLift_comap_regular_hom φ (s j)
      rw [e]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hs
    exact isIso_of_reflects_iso _ (forget R)
  let e : ⨁ (fun _ : Fin n ↦ M.X) ≅ (extendScalarsObj φ M).X :=
    ((forget R).mapBiproduct (fun _ : Fin n ↦ M)).symm ≪≫
      (forget R).mapIso (biproduct.mapIso (fun _ ↦ (λ_ M).symm) ≪≫
        ((tensorRight M).mapBiproduct (fun _ : Fin n ↦ 𝟙_ (Mod C R))).symm ≪≫
          (tensorRight M).mapIso (asIso (biproduct.desc J))) ≪≫
      (extendForgetTensorObjIso φ M).symm
  have he : (biproduct.desc fun i ↦ extendUnitHom φ M ≫ globalSmul (s i)
      (extendScalarsObj φ M) : ⨁ (fun _ : Fin n ↦ M.X) ⟶ _) = e.hom := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    rw [biproduct.ι_desc, extendUnitHom_globalSmul,
      ← leftUnitor_inv_whiskerRight_regularLift_extendForgetTensorObjIso_inv]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapBiproduct_inv,
      biproduct.mapIso_hom, asIso_hom, biproduct.ι_desc_assoc, ← Functor.map_comp_assoc,
      biproduct.ι_map_assoc, J]
    rw [← Functor.map_comp (tensorRight M), biproduct.ι_desc]
    rfl
  rw [he]
  infer_instance

end CategoryTheory.Mod
