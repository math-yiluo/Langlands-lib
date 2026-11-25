/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-!
# Closed support as a relative section complex

Let `i : Z ⟶ X` be a closed immersion with complementary open immersion `j : U ⟶ X`. For every
`K ∈ D(X_ét, A)` the global derived Hom `RΓ(X, RHom(i_* Λ_Z, K))` is the fibre of the
restriction map `RΓ(X, K) ⟶ RΓ(U, j^* K)` (blueprint `lemma-cycle-class-cartier-divisor`).

The proof applies `RHom(-, K)` to the open–closed triangle `j_! j^* Λ ⟶ Λ ⟶ i_* i^* Λ ⟶`
(`AlgebraicGeometry.Etale.exists_distTriang_openClosed`) and identifies
`RHom(j_! j^* Λ, -) ≅ Rj_* j^*` as right adjoints of `j_! j^* Λ ⊗ᴸ - ≅ j_! j^*` (projection
formula), compatibly with `RHom(Λ, -) ≅ 𝟭` and the unit of `j^* ⊣ Rj_*`.

## Main statements

- `AlgebraicGeometry.Etale.exists_distTriang_rightDerivedGlobalSections_derivedHom_closedImmersion`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (G' : D ⥤ C) (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
  (δ : (((Functor.whiskeringLeft₂ C).obj G).obj G').obj T ⟶
    (Functor.postcompose₂.obj G).obj T')

/-- The projection map at an object `G K'`, followed by the counit at `K'` in the first
variable, is `F δ` followed by the counit. -/
@[reassoc]
lemma projectionMap_app_app_comp_map_counit (K' : D) (M : D) :
    ((adj.projectionMap G' T T' δ).app (G.obj K')).app M ≫ (T'.map (adj.counit.app K')).app M =
      F.map ((δ.app K').app M) ≫ adj.counit.app ((T'.obj K').obj M) := by
  rw [projectionMap_app_app, ← adj.homEquiv_naturality_right_symm]
  rw [Adjunction.homEquiv_counit]
  dsimp [projectionMapTranspose]
  have := δ.naturality (adj.counit.app K')
  have h2 := congr_app this M
  dsimp at h2
  rw [Category.assoc, ← h2, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    adj.right_triangle_components]
  simp

end Adjunction

end CategoryTheory


namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ] [HasZeroObject C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If the second map `f₂` of a distinguished triangle is identified with `r` through
isomorphisms of its second and third objects, then `r`, with first object any object isomorphic
to the first object of the triangle, extends to a distinguished triangle. -/
lemma exists_distTriang_of_iso {Y₁ Y₂ Y₃ X₁ X₂ X₃ : C} {f₁ : Y₁ ⟶ Y₂} {f₂ : Y₂ ⟶ Y₃}
    {f₃ : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧} (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C)
    (r : X₂ ⟶ X₃) (e₁ : Y₁ ≅ X₁) (e₂ : Y₂ ≅ X₂) (e₃ : Y₃ ≅ X₃)
    (h : f₂ ≫ e₃.hom = e₂.hom ≫ r) :
    ∃ (a : X₁ ⟶ X₂) (δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧), Triangle.mk a r δ ∈ distTriang C := by
  refine ⟨e₁.inv ≫ f₁ ≫ e₂.hom, e₃.inv ≫ f₃ ≫ e₁.hom⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e₁.symm e₂.symm e₃.symm ?_ ?_ ?_)⟩
  · simp
  · simp only [Triangle.mk_mor₂, Iso.symm_hom]
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  · simp [← Functor.map_comp]

end CategoryTheory.Pretriangulated

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

/-- Let `P ⊗ - ≅ G` for a left adjoint `G ⊣ H`, compatibly with a map `f : P ⟶ 𝟙_` and a
transformation `ε : G ⟶ 𝟭`. Then precomposition with `f`, `ihom 𝟙_ ⟶ ihom P`, corresponds under
`𝟭 ≅ ihom 𝟙_` and the induced `H ≅ ihom P` to the conjugate `𝟭 ⟶ H` of `ε`. -/
lemma unitNatIso_hom_comp_pre {P : C} {G H : C ⥤ C} (adj : G ⊣ H) (Φ : tensorLeft P ⟶ G)
    (f : P ⟶ 𝟙_ C) (ε : G ⟶ 𝟭 C)
    (h : Φ ≫ ε = (tensoringLeft C).map f ≫ (leftUnitorNatIso C).hom) :
    unitNatIso.hom ≫ pre f =
      conjugateEquiv Adjunction.id adj ε ≫ conjugateEquiv adj (ihom.adjunction P) Φ := by
  rw [conjugateEquiv_comp, h, ← conjugateEquiv_comp _ (ihom.adjunction (𝟙_ C))]
  rfl

end CategoryTheory.MonoidalClosed

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  [Etale.UpperStarPreservesFlat A]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j : U ⟶ X`, tensoring with `j_! j^* Λ_X` is `j_! j^*`:
`j_! j^* Λ_X ⊗ᴸ M ≅ j_!(j^* Λ_X ⊗ᴸ Lj^* M) ≅ j_! j^*(Λ_X ⊗ᴸ M) ≅ j_! j^* M`, by the projection
formula and the left unitor. -/
noncomputable def tensorLeftOpenImmersionLowerShriekUpperStarUnitIso
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    tensorLeft ((D((j)_!open[A])).obj ((D((j)^*[A])).obj (𝟙_ _))) ≅
      D((j)^*[A]) ⋙ D((j)_!open[A]) :=
  NatIso.ofComponents (fun M ↦
    ((((derivedOpenImmersionLowerShriekProjectionIso A j).app
        ((D((j)^*[A])).obj (𝟙_ _))).app M).symm ≪≫
      (D((j)_!open[A])).mapIso
        ((((mapDerivedCategoryUpperStarDerivedTensorIso A j).app (𝟙_ _)).app M) ≪≫
          (D((j)^*[A])).mapIso (λ_ M)))) (by
    intro M M' φ
    have h1 := ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app
      ((D((j)^*[A])).obj (𝟙_ _))).naturality φ
    have h2 := ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app (𝟙_ _)).naturality φ
    dsimp at h1 h2 ⊢
    simp only [Category.assoc, ← Functor.map_comp]
    erw [reassoc_of% h1]
    congr 1
    rw [← leftUnitor_naturality, ← Functor.map_comp]
    congr 1
    rw [Functor.map_comp]
    erw [reassoc_of% h2]
    rfl)

/-- The isomorphism `j_! j^* Λ_X ⊗ᴸ M ≅ j_! j^* M`, followed by the counit of `j_! ⊣ j^*`, is the
counit at `Λ_X` tensored with `M`, followed by the left unitor. -/
lemma tensorLeftOpenImmersionLowerShriekUpperStarUnitIso_hom_comp_counit
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    (tensorLeftOpenImmersionLowerShriekUpperStarUnitIso A j).hom ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit =
      (tensoringLeft _).map ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app
        (𝟙_ _)) ≫ (leftUnitorNatIso _).hom := by
  ext M
  have h := Adjunction.projectionMap_app_app_comp_map_counit
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
    L((j)^*[A]) (-⊗ᴸ-(U)[A]) (-⊗ᴸ-(X)[A]) (mapDerivedCategoryUpperStarDerivedTensorIso A j).hom
    (𝟙_ _) M
  dsimp [tensorLeftOpenImmersionLowerShriekUpperStarUnitIso]
  rw [← cancel_epi (((derivedOpenImmersionLowerShriekProjectionIso A j).hom.app
    ((D((j)^*[A])).obj (𝟙_ _))).app M)]
  simp only [Category.assoc, Iso.hom_inv_id_app_app_assoc]
  simp only [derivedOpenImmersionLowerShriekProjectionIso_hom,
    derivedOpenImmersionLowerShriekProjectionMap, Functor.map_comp, Category.assoc]
  erw [reassoc_of% h]
  rw [(derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit_naturality]
  rfl

omit [UpperStarPreservesFlat A] in
/-- The conjugate of the counit of `j_! ⊣ j^*`, under the composite adjunction
`j_! j^* ⊣ Rj_* j^*`, is the unit of `j^* ⊣ Rj_*`. -/
lemma conjugateEquiv_id_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit :
    conjugateEquiv Adjunction.id ((mapDerivedUpperStarLowerStarAdjunction A j).comp
        (derivedOpenImmersionLowerShriekUpperStarAdjunction A j))
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit =
      (mapDerivedUpperStarLowerStarAdjunction A j).unit := by
  ext K
  have := unit_conjugateEquiv Adjunction.id ((mapDerivedUpperStarLowerStarAdjunction A j).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A j))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit K
  dsimp at this
  erw [Category.id_comp] at this
  rw [this, Adjunction.comp_unit_app]
  dsimp
  rw [Category.assoc, ← Functor.map_comp,
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).right_triangle_components,
    CategoryTheory.Functor.map_id, Category.comp_id]

end OpenImmersion

section ClosedSupport

variable {Z X U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]

/-- Blueprint `lemma-cycle-class-cartier-divisor`: Closed support as a relative section complex.

Let `i : Z ⟶ X` be a closed immersion with complementary open immersion `j : U ⟶ X`. For every
complex `K` of étale sheaves on `X`, the global derived Hom out of `i_* Λ_Z`,
`RHom_X(i_* Λ_Z, K) = RΓ(X, RHom(Ri_* Λ_Z, K))`, is the fibre of the restriction map
`RΓ(X, K) ⟶ RΓ(U, j^* K)`: there is a distinguished triangle
`RHom_X(i_* Λ_Z, K) ⟶ RΓ(X, K) ⟶ RΓ(U, j^* K) ⟶ RHom_X(i_* Λ_Z, K)[1]`
whose second map is the restriction map, the unit `K ⟶ Rj_* j^* K` followed by the Leray
isomorphism `RΓ(X, Rj_* j^* K) ≅ RΓ(U, j^* K)`; that is,
`RHom_X(i_* Λ_Z, K) ≅ Cone(RΓ(X, K) ⟶ RΓ(U, j^* K))[-1]`. -/
theorem exists_distTriang_rightDerivedGlobalSections_derivedHom_closedImmersion
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ∃ (a : (rightDerivedGlobalSections A X).obj
          (((RHom(X)[A]).obj (op ((R((i)_*[A])).obj (𝟙_ _)))).obj K) ⟶
        (rightDerivedGlobalSections A X).obj K)
      (δ : (rightDerivedGlobalSections A U).obj ((D((j)^*[A])).obj K) ⟶
        ((rightDerivedGlobalSections A X).obj
          (((RHom(X)[A]).obj (op ((R((i)_*[A])).obj (𝟙_ _)))).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk a ((rightDerivedGlobalSections A X).map
          ((mapDerivedUpperStarLowerStarAdjunction A j).unit.app K) ≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A j).hom.app
          ((D((j)^*[A])).obj K)) δ ∈ distTriang _ := by
  -- the open–closed triangle `j_! j^* Λ ⟶ Λ ⟶ Ri_* i^* Λ ⟶` and its image under `RHom(-, K)`
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed A j i hij (𝟙_ _)
  obtain ⟨w', hw'⟩ := exists_distTriang_derivedHom_left K _ hw
  have : (rightDerivedGlobalSections A X).IsTriangulated :=
    inferInstanceAs (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.IsTriangulated
  have hT := (rightDerivedGlobalSections A X).map_distinguished _ hw'
  -- the identifications `RHom(Λ, K) ≅ K` and `RHom(j_! j^* Λ, K) ≅ Rj_* j^* K`
  let adj := (mapDerivedUpperStarLowerStarAdjunction A j).comp
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
  let ψ := conjugateEquiv adj (ihom.adjunction _)
    (tensorLeftOpenImmersionLowerShriekUpperStarUnitIso A j).hom
  have key := MonoidalClosed.unitNatIso_hom_comp_pre adj
    (tensorLeftOpenImmersionLowerShriekUpperStarUnitIso A j).hom
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app (𝟙_ _)) _
    (tensorLeftOpenImmersionLowerShriekUpperStarUnitIso_hom_comp_counit A j)
  rw [conjugateEquiv_id_derivedOpenImmersionLowerShriekUpperStarAdjunction_counit] at key
  let e : (D((i)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _ :=
    ((leftDerivedUpperStarIsoMapDerivedCategory A i).app (𝟙_ _)).symm ≪≫
      leftDerivedUpperStarUnitIso A i
  let e₁ := (rightDerivedGlobalSections A X).mapIso
    (((RHom(X)[A]).mapIso ((R((i)_*[A])).mapIso e).op.symm).app K)
  let e₂ := (rightDerivedGlobalSections A X).mapIso (MonoidalClosed.unitNatIso.app K).symm
  let e₃ := (rightDerivedGlobalSections A X).mapIso (asIso (ψ.app K)).symm ≪≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A j).app ((D((j)^*[A])).obj K)
  simp only [Functor.mapTriangle_obj, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃] at hT
  refine exists_distTriang_of_iso hT _ e₁ e₂ e₃ ?_
  have k := congr_app key K
  dsimp at k
  have k' : ((RHom(X)[A]).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit.app (𝟙_ _)).op).app K ≫
        inv (ψ.app K) =
      MonoidalClosed.unitNatIso.inv.app K ≫
        (mapDerivedUpperStarLowerStarAdjunction A j).unit.app K := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← k, Iso.inv_hom_id_app_assoc]
    rfl
  simp only [e₂, e₃, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv, Iso.app_inv]
  rw [← Functor.map_comp_assoc, k', Functor.map_comp_assoc]
  rfl

end ClosedSupport

end AlgebraicGeometry.Etale
