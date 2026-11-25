/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsProjection

/-!
# The derived projection map of étale sheaves and the derived pullback

Let `S` be an `R`-algebra, `Ψ = L(S ⊗_R -)` derived extension of scalars of étale sheaves and
`g : Z ⟶ Y`. Restricted back to `R`, `Ψ` is the derived tensor product with the sheaf `S_Y`
(`AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection`), and the derived pullback
`Lg^*` carries `L(- ⊗ S_Y)` to `L(- ⊗ S_Z)`: the comparison `g^*(P ⊗ S_Y) ⟶ g^* P ⊗ S_Z` of
sheaves induces a natural transformation `Lg^* (L(- ⊗ S_Y) K) ⟶ L(- ⊗ S_Z) (Lg^* K)`.

We show that the transposes `Ψ (K ⊗ᴸ S_Y) ⟶ Ψ K` of the derived projection maps are compatible
with this comparison and with the commutation `Lg^* Ψ ≅ Ψ Lg^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarEtaleSheafExtendScalarsIso`). This is the input
needed to compare the base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` with the projection map of
`Rg_*` at `S_Y`.

This is the étale counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.ProjectionPullback`.

## Main definitions and results

- `AlgebraicGeometry.Etale.tensorRestrictScalarsUnitUpperStarMap`: the comparison
  `g^*(P ⊗ S_Y) ⟶ g^* P ⊗ S_Z` of sheaves.
- `AlgebraicGeometry.Etale.leftDerivedTensorRestrictScalarsUnitUpperStarMap`: the induced
  natural transformation `L(- ⊗ S_Y) ⋙ Lg^* ⟶ Lg^* ⋙ L(- ⊗ S_Z)`.
- `AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection_transpose_upperStar`: the
  compatibility of the transposed derived projection maps with the derived pullback.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory HomologicalComplex Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace CategoryTheory

section ProjectionTransposeUpperStar

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  [Preadditive A] [Preadditive B] [Preadditive A'] [Preadditive B']
  {T : A ⥤ A} {E : A ⥤ B} {gA : A ⥤ A'} {gB : B ⥤ B'} {T' : A' ⥤ A'} {E' : A' ⥤ B'}
  [T.Additive] [E.Additive] [gA.Additive] [gB.Additive] [T'.Additive] [E'.Additive]

omit [Preadditive A] [Preadditive B] [Preadditive A'] [Preadditive B'] [T.Additive]
  [E.Additive] [gA.Additive] [gB.Additive] [T'.Additive] [E'.Additive] in
/-- `NatTrans.mapHomotopyCategory` evaluated at the quotient of a complex. -/
private lemma NatTrans.mapHomotopyCategory_app_quotient {V W : Type*} [Category V] [Category W]
    [Preadditive V] [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive]
    (α : F ⟶ G) (K : CochainComplex V ℤ) :
    (NatTrans.mapHomotopyCategory α (.up ℤ)).app ((HomotopyCategory.quotient V (.up ℤ)).obj K) =
      (HomotopyCategory.quotient W (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K) :=
  rfl

/-- A commutative square of natural transformations `gB (p P) ≫ σ P = σ (T P) ≫ E' (τ P) ≫
p' (gA P)` induces the corresponding commutative square on homotopy categories. -/
private lemma NatTrans.mapHomotopyCategory_transpose_square (p : T ⋙ E ⟶ E) (p' : T' ⋙ E' ⟶ E')
    (σ : E ⋙ gB ⟶ gA ⋙ E') (τ : T ⋙ gA ⟶ gA ⋙ T')
    (h : ∀ P, gB.map (p.app P) ≫ σ.app P = σ.app (T.obj P) ≫ E'.map (τ.app P) ≫ p'.app (gA.obj P))
    (σH : E.mapHomotopyCategory (.up ℤ) ⋙ gB.mapHomotopyCategory (.up ℤ) ⟶
      gA.mapHomotopyCategory (.up ℤ) ⋙ E'.mapHomotopyCategory (.up ℤ))
    (hσH : σH = (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ gB)) (.up ℤ)).hom ≫
      NatTrans.mapHomotopyCategory σ (.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (gA ⋙ E')) (.up ℤ)).inv)
    (τH : T.mapHomotopyCategory (.up ℤ) ⋙ gA.mapHomotopyCategory (.up ℤ) ⟶
      gA.mapHomotopyCategory (.up ℤ) ⋙ T'.mapHomotopyCategory (.up ℤ))
    (hτH : τH = (Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ gA)) (.up ℤ)).hom ≫
      NatTrans.mapHomotopyCategory τ (.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (gA ⋙ T')) (.up ℤ)).inv)
    (K : HomotopyCategory A (.up ℤ)) :
    (gB.mapHomotopyCategory (.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ E)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory p (.up ℤ)).app K) ≫ σH.app K =
    σH.app ((T.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (E'.mapHomotopyCategory (.up ℤ)).map (τH.app K) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (T' ⋙ E')) (.up ℤ)).hom.app
        ((gA.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (NatTrans.mapHomotopyCategory p' (.up ℤ)).app ((gA.mapHomotopyCategory (.up ℤ)).obj K) := by
  subst hσH hτH
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [NatTrans.comp_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, Category.id_comp, Category.comp_id,
    NatTrans.mapHomotopyCategory_app_quotient,
    Functor.mapHomotopyCategory_map]
  simp only [← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f]
  erw [Category.id_comp]
  exact h (K.X n)

end ProjectionTransposeUpperStar

section ProjectionTransposeUpperStarAux

variable {𝒟₁ 𝒟₂ 𝒟₃ 𝒟₄ ℋ₁ ℋ₂ ℋ₃ ℋ₄ : Type*} [Category 𝒟₁] [Category 𝒟₂] [Category 𝒟₃]
  [Category 𝒟₄] [Category ℋ₁] [Category ℋ₂] [Category ℋ₃] [Category ℋ₄]
  {Q₁ : ℋ₁ ⥤ 𝒟₁} {Q₂ : ℋ₂ ⥤ 𝒟₂} {Q₃ : ℋ₃ ⥤ 𝒟₃} {Q₄ : ℋ₄ ⥤ 𝒟₄}
  {LT₁ : 𝒟₁ ⥤ 𝒟₁} {LT₃ : 𝒟₃ ⥤ 𝒟₃} {LE₁ : 𝒟₁ ⥤ 𝒟₂} {LE₃ : 𝒟₃ ⥤ 𝒟₄}
  {LgR : 𝒟₁ ⥤ 𝒟₃} {LgS : 𝒟₂ ⥤ 𝒟₄} {LRes₂ : 𝒟₂ ⥤ 𝒟₁} {LRes₄ : 𝒟₄ ⥤ 𝒟₃}
  {T₁ : ℋ₁ ⥤ ℋ₁} {T₃ : ℋ₃ ⥤ ℋ₃} {E₁ : ℋ₁ ⥤ ℋ₂} {E₃ : ℋ₃ ⥤ ℋ₄} {gR : ℋ₁ ⥤ ℋ₃}
  {gS : ℋ₂ ⥤ ℋ₄} {TE₁ : ℋ₁ ⥤ ℋ₂} {TE₃ : ℋ₃ ⥤ ℋ₄}

/-- The diagram chase behind `leftDerivedSheafExtendScalarsProjection_transpose_upperStar`,
stated for arbitrary categories, functors and natural transformations: localization functors
`Qᵢ`, derived functors `L…` with counits `κ…`, derived projection maps `θᵢ` and adjunctions
`adjᵢ`, the comparison maps `α` and `β` and their homotopy category counterparts `σ` and `τ`. -/
private lemma transpose_upperStar_aux
    (κT₁ : Q₁ ⋙ LT₁ ⟶ T₁ ⋙ Q₁) (κT₃ : Q₃ ⋙ LT₃ ⟶ T₃ ⋙ Q₃)
    (κE₁ : Q₁ ⋙ LE₁ ⟶ E₁ ⋙ Q₂) (κE₃ : Q₃ ⋙ LE₃ ⟶ E₃ ⋙ Q₄)
    (κgR : Q₁ ⋙ LgR ⟶ gR ⋙ Q₃) (κgS : Q₂ ⋙ LgS ⟶ gS ⋙ Q₄)
    (θ₁ : LT₁ ⟶ LE₁ ⋙ LRes₂) (θ₃ : LT₃ ⟶ LE₃ ⋙ LRes₄)
    (adj₁ : LE₁ ⊣ LRes₂) (adj₃ : LE₃ ⊣ LRes₄)
    (α : LE₁ ⋙ LgS ≅ LgR ⋙ LE₃) (β : LT₁ ⋙ LgR ⟶ LgR ⋙ LT₃)
    (cZ : Q₁ ⋙ LgR ⋙ LE₃ ⟶ gR ⋙ E₃ ⋙ Q₄)
    (hcZ : cZ = Functor.whiskerRight κgR LE₃ ≫ Functor.whiskerLeft gR κE₃)
    (cY : Q₁ ⋙ LE₁ ⋙ LgS ⟶ E₁ ⋙ gS ⋙ Q₄)
    (hcY : cY = Functor.whiskerRight κE₁ LgS ≫ Functor.whiskerLeft E₁ κgS)
    (cT : Q₁ ⋙ LT₁ ⋙ LgR ⟶ T₁ ⋙ gR ⋙ Q₃)
    (hcT : cT = Functor.whiskerRight κT₁ LgR ≫ Functor.whiskerLeft T₁ κgR)
    (cT' : Q₁ ⋙ LgR ⋙ LT₃ ⟶ gR ⋙ T₃ ⋙ Q₃)
    (hcT' : cT' = Functor.whiskerRight κgR LT₃ ≫ Functor.whiskerLeft gR κT₃)
    (σ : E₁ ⋙ gS ≅ gR ⋙ E₃) (τ : T₁ ⋙ gR ⟶ gR ⋙ T₃)
    (e₁ : T₁ ⋙ E₁ ≅ TE₁) (p₁ : TE₁ ⟶ E₁) (e₃ : T₃ ⋙ E₃ ≅ TE₃) (p₃ : TE₃ ⟶ E₃)
    (hα : ∀ K, α.hom.app (Q₁.obj K) ≫ cZ.app K = cY.app K ≫ Q₄.map (σ.hom.app K))
    (hβ : ∀ K, β.app (Q₁.obj K) ≫ cT'.app K = cT.app K ≫ Q₃.map (τ.app K))
    (htr₁ : ∀ K, LE₁.map (θ₁.app (Q₁.obj K)) ≫ adj₁.counit.app (LE₁.obj (Q₁.obj K)) ≫
        κE₁.app K =
      LE₁.map (κT₁.app K) ≫ κE₁.app (T₁.obj K) ≫ Q₂.map (e₁.hom.app K ≫ p₁.app K))
    (htr₃ : ∀ K, LE₃.map (θ₃.app (Q₃.obj K)) ≫ adj₃.counit.app (LE₃.obj (Q₃.obj K)) ≫
        κE₃.app K =
      LE₃.map (κT₃.app K) ≫ κE₃.app (T₃.obj K) ≫ Q₄.map (e₃.hom.app K ≫ p₃.app K))
    (hH : ∀ K, gS.map (e₁.hom.app K ≫ p₁.app K) ≫ σ.hom.app K =
      σ.hom.app (T₁.obj K) ≫ E₃.map (τ.app K) ≫ e₃.hom.app (gR.obj K) ≫ p₃.app (gR.obj K))
    (K : ℋ₁) :
    (LgS.map (LE₁.map (θ₁.app (Q₁.obj K)) ≫ adj₁.counit.app (LE₁.obj (Q₁.obj K))) ≫
      α.hom.app (Q₁.obj K)) ≫ cZ.app K =
    (α.hom.app (LT₁.obj (Q₁.obj K)) ≫
      LE₃.map (β.app (Q₁.obj K) ≫ θ₃.app (LgR.obj (Q₁.obj K))) ≫
      adj₃.counit.app (LE₃.obj (LgR.obj (Q₁.obj K)))) ≫ cZ.app K := by
  have hα₁ := hα K
  have hα₂ := hα (T₁.obj K)
  have hY := congrArg LgS.map (htr₁ K)
  have hZ := htr₃ (gR.obj K)
  have ha := congrArg LE₃.map (hβ K)
  have hS := κgS.naturality (e₁.hom.app K ≫ p₁.app K)
  have hϑ := congrArg LE₃.map (θ₃.naturality (κgR.app K))
  have hΨ := κE₃.naturality (τ.app K)
  have hn := α.hom.naturality (κT₁.app K)
  have hH' := congrArg Q₄.map (hH K)
  subst hcZ hcY hcT hcT'
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Functor.comp_map, Functor.comp_obj, Category.assoc]
    at hα₁ hα₂ hY hZ ha hS hϑ hΨ hn hH' ⊢
  rw [hα₁, reassoc_of% hY, reassoc_of% hS, hH']
  erw [← Adjunction.counit_naturality_assoc]
  rw [← reassoc_of% hϑ, hZ, reassoc_of% ha, reassoc_of% hΨ, ← reassoc_of% hn, reassoc_of% hα₂]

end ProjectionTransposeUpperStarAux

end CategoryTheory

-- Use the monoidal structure of the derived tensor product of étale sheaves, see
-- `WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsDerived`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]
  {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The comparison `g^*(P ⊗ S_Y) ⟶ g^* P ⊗ S_Z` of étale sheaves: the comonoidal structure
of the pullback followed by the identification `g^* S_Y ≅ S_Z` of
`AlgebraicGeometry.Etale.upperStarSheafRestrictScalarsUnitMap`. -/
noncomputable abbrev tensorRestrictScalarsUnitUpperStarMap :
    tensorRight (sheafRestrictScalarsUnit R S Y) ⋙ (g)^*[ModuleCat.{u + 1} R] ⟶
      (g)^*[ModuleCat.{u + 1} R] ⋙ tensorRight (sheafRestrictScalarsUnit R S Z) :=
  tensorRightUpperStarMap g (upperStarSheafRestrictScalarsUnitMap R S g)

/-- The transposes `S ⊗_R (P ⊗ S_Y) ⟶ S ⊗_R P` of the projection maps are compatible with the
pullback: the square
```
g^* (S ⊗_R (P ⊗ S_Y)) ──g^* π♯──▶ g^* (S ⊗_R P)
        │ ≅                              │ ≅
        ▼                                ▼
S ⊗_R g^* (P ⊗ S_Y) ──▶ S ⊗_R (g^* P ⊗ S_Z) ──π♯──▶ S ⊗_R g^* P
```
commutes. It is the transpose of `AlgebraicGeometry.Etale.sheafExtendScalarsProjection_upperStar`
along the adjunction between extension and restriction of scalars. -/
lemma sheafExtendScalarsProjectionTranspose_upperStar
    (P : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (g)^*[ModuleCat.{u + 1} S].map ((sheafExtendScalarsProjectionTranspose R S Y).app P) ≫
      (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.app P =
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.app
        (P ⊗ sheafRestrictScalarsUnit R S Y) ≫
      (sheafExtendScalars (algebraMap R S) Z).map
        ((tensorRestrictScalarsUnitUpperStarMap R S g).app P) ≫
      (sheafExtendScalarsProjectionTranspose R S Z).app ((g)^*[ModuleCat.{u + 1} R].obj P) := by
  have h₀ : (tensorRestrictScalarsUnitUpperStarMap R S g).app P ≫
      (sheafExtendScalarsProjection R S Z).app ((g)^*[ModuleCat.{u + 1} R].obj P) =
      (g)^*[ModuleCat.{u + 1} R].map ((sheafExtendScalarsProjection R S Y).app P) ≫
        (upperStarRestrictScalarsMap R S g).app
          ((sheafExtendScalars (algebraMap R S) Y).obj P) ≫
        (sheafCompose Z.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map
          ((sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.app P) := by
    rw [sheafExtendScalarsProjection_upperStar]
    simp [tensorRightUpperStarMap]
  have hU : (sheafExtendScalars (algebraMap R S) Z).map
        ((upperStarRestrictScalarsMap R S g).app
          ((sheafExtendScalars (algebraMap R S) Y).obj P)) ≫
      (sheafExtendScalarsAdjunction (algebraMap R S) Z).counit.app _ =
      (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv.app _ ≫
        (g)^*[ModuleCat.{u + 1} S].map
          ((sheafExtendScalarsAdjunction (algebraMap R S) Y).counit.app _) :=
    mateEquiv_counit (sheafExtendScalarsAdjunction (algebraMap R S) Y)
      (sheafExtendScalarsAdjunction (algebraMap R S) Z)
      (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv
      ((sheafExtendScalars (algebraMap R S) Y).obj P)
  have hσ := (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.naturality
    ((sheafExtendScalarsProjection R S Y).app P)
  dsimp at hσ
  simp only [sheafExtendScalarsProjectionTranspose, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [← Functor.map_comp_assoc, h₀]
  simp only [Functor.map_comp, Category.assoc]
  rw [Adjunction.counit_naturality, reassoc_of% hU, ← reassoc_of% hσ,
    Iso.hom_inv_id_app_assoc]

/-- The comparison `g^*(P ⊗ S_Y) ⟶ g^* P ⊗ S_Z` on homotopy categories. -/
noncomputable abbrev mapHomotopyCategoryTensorRestrictScalarsUnitUpperStarMap :
    (tensorRight (sheafRestrictScalarsUnit R S Y)).mapHomotopyCategory (.up ℤ) ⋙
        (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⟶
      (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⋙
        (tensorRight (sheafRestrictScalarsUnit R S Z)).mapHomotopyCategory (.up ℤ) :=
  mapHomotopyCategoryTensorRightUpperStarMap g (upperStarSheafRestrictScalarsUnitMap R S g)

/-- The comparison `Lg^* (K ⊗ᴸ S_Y) ⟶ Lg^* K ⊗ᴸ S_Z` induced by the comparison
`g^*(P ⊗ S_Y) ⟶ g^* P ⊗ S_Z` of sheaves, where `- ⊗ᴸ S_Y` is the left derived functor of
`- ⊗ S_Y` (`AlgebraicGeometry.Etale.leftDerivedTensorRightUpperStarMap`). -/
noncomputable abbrev leftDerivedTensorRestrictScalarsUnitUpperStarMap :
    L(tensorRight (sheafRestrictScalarsUnit R S Y)) ⋙ L((g)^*[ModuleCat.{u + 1} R]) ⟶
      L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(tensorRight (sheafRestrictScalarsUnit R S Z)) :=
  leftDerivedTensorRightUpperStarMap g (upperStarSheafRestrictScalarsUnitMap R S g)

/-- `AlgebraicGeometry.Etale.sheafExtendScalarsProjectionTranspose_upperStar` on homotopy
categories. -/
lemma mapHomotopyCategory_sheafExtendScalarsProjectionTranspose_upperStar [IsNoetherianRing R]
    (K : HomotopyCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (.up ℤ)) :
    ((g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (tensorRight (sheafRestrictScalarsUnit R S Y) ⋙
              sheafExtendScalars (algebraMap R S) Y)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory (sheafExtendScalarsProjectionTranspose R S Y)
            (.up ℤ)).app K) ≫
      (mapHomotopyCategoryEtaleSheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.app K =
    (mapHomotopyCategoryEtaleSheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.app
        (((tensorRight (sheafRestrictScalarsUnit R S Y)).mapHomotopyCategory (.up ℤ)).obj K) ≫
      ((sheafExtendScalars (algebraMap R S) Z).mapHomotopyCategory (.up ℤ)).map
        ((mapHomotopyCategoryTensorRestrictScalarsUnitUpperStarMap R S g).app K) ≫
      (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (tensorRight (sheafRestrictScalarsUnit R S Z) ⋙
            sheafExtendScalars (algebraMap R S) Z)) (.up ℤ)).hom.app
        (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj K) ≫
      (NatTrans.mapHomotopyCategory (sheafExtendScalarsProjectionTranspose R S Z) (.up ℤ)).app
        (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj K) :=
  NatTrans.mapHomotopyCategory_transpose_square (sheafExtendScalarsProjectionTranspose R S Y)
    (sheafExtendScalarsProjectionTranspose R S Z)
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom
    (tensorRestrictScalarsUnitUpperStarMap R S g)
    (sheafExtendScalarsProjectionTranspose_upperStar R S g)
    (mapHomotopyCategoryEtaleSheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom rfl
    (mapHomotopyCategoryTensorRestrictScalarsUnitUpperStarMap R S g) rfl K

section Derived

variable [IsNoetherianRing R]

set_option hygiene false in
/-- Derived extension of scalars on `X`. -/
local notation "Ψ[" X "]" => L(sheafExtendScalars (algebraMap R S) X)

set_option hygiene false in
/-- The derived tensor product with `S_X`. -/
local notation "𝓣[" X "]" => L(tensorRight (sheafRestrictScalarsUnit R S X))

set_option hygiene false in
/-- The derived pullback with coefficients `R`. -/
local notation "𝓖R" => L((g)^*[ModuleCat.{u + 1} R])

set_option hygiene false in
/-- The derived pullback with coefficients `S`. -/
local notation "𝓖S" => L((g)^*[ModuleCat.{u + 1} S])

/-- The two sides of `leftDerivedSheafExtendScalarsProjection_transpose_upperStar` agree after
composition with the counit of `Lg^* ⋙ Ψ` on the image of an object of the homotopy category. -/
private lemma leftDerivedSheafExtendScalarsProjection_transpose_upperStar_aux
    (K : HomotopyCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (.up ℤ)) :
    ((𝓖S).map ((Ψ[Y]).map ((leftDerivedSheafExtendScalarsProjection R S Y).app
          (DerivedCategory.Qh.obj K)) ≫
        (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) Y).counit.app
          ((Ψ[Y]).obj (DerivedCategory.Qh.obj K))) ≫
      (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom.app
        (DerivedCategory.Qh.obj K)) ≫
      (leftDerivedUpperStarEtaleSheafExtendScalarsCounit (algebraMap R S) g).app K =
    ((leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom.app
        ((𝓣[Y]).obj (DerivedCategory.Qh.obj K)) ≫
      (Ψ[Z]).map ((leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g).app
          (DerivedCategory.Qh.obj K) ≫
        (leftDerivedSheafExtendScalarsProjection R S Z).app
          ((𝓖R).obj (DerivedCategory.Qh.obj K))) ≫
      (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) Z).counit.app
        ((Ψ[Z]).obj ((𝓖R).obj (DerivedCategory.Qh.obj K)))) ≫
      (leftDerivedUpperStarEtaleSheafExtendScalarsCounit (algebraMap R S) g).app K :=
  transpose_upperStar_aux
    (T₁ := (tensorRight (sheafRestrictScalarsUnit R S Y)).mapHomotopyCategory (.up ℤ))
    (T₃ := (tensorRight (sheafRestrictScalarsUnit R S Z)).mapHomotopyCategory (.up ℤ))
    (E₁ := (sheafExtendScalars (algebraMap R S) Y).mapHomotopyCategory (.up ℤ))
    (E₃ := (sheafExtendScalars (algebraMap R S) Z).mapHomotopyCategory (.up ℤ))
    (gR := (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ))
    (gS := (g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ))
    (tensorRight (sheafRestrictScalarsUnit R S Y)).leftDerivedFunctorCounit
    (tensorRight (sheafRestrictScalarsUnit R S Z)).leftDerivedFunctorCounit
    (sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit
    (sheafExtendScalars (algebraMap R S) Z).leftDerivedFunctorCounit
    (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorCounit
    (g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorCounit
    (leftDerivedSheafExtendScalarsProjection R S Y) (leftDerivedSheafExtendScalarsProjection R S Z)
    (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) Y)
    (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) Z)
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g)
    (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g)
    (leftDerivedUpperStarEtaleSheafExtendScalarsCounit (algebraMap R S) g) rfl
    (leftDerivedEtaleSheafExtendScalarsUpperStarCounit (algebraMap R S) g) rfl
    (leftDerivedTensorRightUpperStarCounit (c_Y := sheafRestrictScalarsUnit R S Y) g) rfl
    (leftDerivedUpperStarTensorRightCounit g (sheafRestrictScalarsUnit R S Z)) rfl
    (mapHomotopyCategoryEtaleSheafExtendScalarsCompUpperStarIso (algebraMap R S) g)
    (mapHomotopyCategoryTensorRestrictScalarsUnitUpperStarMap R S g)
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (tensorRight (sheafRestrictScalarsUnit R S Y) ⋙
      sheafExtendScalars (algebraMap R S) Y)) (.up ℤ))
    (NatTrans.mapHomotopyCategory (sheafExtendScalarsProjectionTranspose R S Y) (.up ℤ))
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (tensorRight (sheafRestrictScalarsUnit R S Z) ⋙
      sheafExtendScalars (algebraMap R S) Z)) (.up ℤ))
    (NatTrans.mapHomotopyCategory (sheafExtendScalarsProjectionTranspose R S Z) (.up ℤ))
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso_hom_app_comp_counit (algebraMap R S) g)
    (leftDerivedTensorRightUpperStarMap_app_comp_counit g
      (upperStarSheafRestrictScalarsUnitMap R S g))
    (leftDerivedSheafExtendScalarsProjection_transpose R S Y)
    (leftDerivedSheafExtendScalarsProjection_transpose R S Z)
    (mapHomotopyCategory_sheafExtendScalarsProjectionTranspose_upperStar R S g) K

/-- **The transposed derived projection maps commute with the derived pullback**: for `K` in
`D(Y_ét, R)`, the square
```
Lg^* Ψ (K ⊗ᴸ S_Y) ──Lg^* ϑ♯──▶ Lg^* Ψ K
       │ ≅                         │ ≅
       ▼                           ▼
Ψ Lg^* (K ⊗ᴸ S_Y) ──▶ Ψ (Lg^* K ⊗ᴸ S_Z) ──ϑ♯──▶ Ψ Lg^* K
```
commutes, where `ϑ♯ : Ψ (K ⊗ᴸ S_Y) ⟶ Ψ K` is the transpose along `Ψ ⊣ Res` of the derived
projection map `AlgebraicGeometry.Etale.leftDerivedSheafExtendScalarsProjection`, the vertical
maps are `AlgebraicGeometry.Etale.leftDerivedUpperStarEtaleSheafExtendScalarsIso` and the middle
map is `Ψ` of `AlgebraicGeometry.Etale.leftDerivedTensorRestrictScalarsUnitUpperStarMap`. -/
lemma leftDerivedSheafExtendScalarsProjection_transpose_upperStar
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (𝓖S).map ((Ψ[Y]).map ((leftDerivedSheafExtendScalarsProjection R S Y).app K) ≫
        (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) Y).counit.app
          ((Ψ[Y]).obj K)) ≫
      (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom.app K =
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom.app
        ((𝓣[Y]).obj K) ≫
      (Ψ[Z]).map ((leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g).app K ≫
        (leftDerivedSheafExtendScalarsProjection R S Z).app ((𝓖R).obj K)) ≫
      (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) Z).counit.app
        ((Ψ[Z]).obj ((𝓖R).obj K)) := by
  let γ₁ : 𝓣[Y] ⋙ Ψ[Y] ⋙ 𝓖S ⟶ 𝓖R ⋙ Ψ[Z] :=
    Functor.whiskerRight (Functor.whiskerRight (leftDerivedSheafExtendScalarsProjection R S Y)
        (Ψ[Y]) ≫ Functor.whiskerLeft (Ψ[Y])
          (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) Y).counit)
      (𝓖S) ≫ (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom
  let γ₂ : 𝓣[Y] ⋙ Ψ[Y] ⋙ 𝓖S ⟶ 𝓖R ⋙ Ψ[Z] :=
    Functor.whiskerLeft (𝓣[Y])
        (leftDerivedUpperStarEtaleSheafExtendScalarsIso (algebraMap R S) g).hom ≫
      Functor.whiskerRight (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g ≫
        Functor.whiskerLeft (𝓖R) (leftDerivedSheafExtendScalarsProjection R S Z)) (Ψ[Z]) ≫
      Functor.whiskerLeft (𝓖R) (Functor.whiskerLeft (Ψ[Z])
        (leftDerivedEtaleSheafExtendScalarsAdjunction (algebraMap R S) Z).counit)
  have h : γ₁ = γ₂ := by
    apply (𝓖R ⋙ Ψ[Z]).leftDerived_ext
      (leftDerivedUpperStarEtaleSheafExtendScalarsCounit (algebraMap R S) g)
      (HomotopyCategory.quasiIso _ (.up ℤ))
    ext K
    simpa [γ₁, γ₂] using leftDerivedSheafExtendScalarsProjection_transpose_upperStar_aux R S g K
  simpa [γ₁, γ₂] using NatTrans.congr_app h K

end Derived

end AlgebraicGeometry.Etale
