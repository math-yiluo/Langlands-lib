/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Derived
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit

/-!
# The tensor comparison of the derived pullback

- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison g`: the comparison
  `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`, and
  `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso g`: it is a natural isomorphism.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso g`: the canonical `Lg^* Λ_Y ≅ Λ_Z`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal g`: `Lg^*` is a monoidal functor, with
  comonoidal structure `leftDerivedUpperStarTensorComparison`. The coherence axioms are
  checked on complexes whose pullback is K-flat
  (`CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare`).

See `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal` for an overview.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
section

open _root_.DerivedCategory Functor.OplaxMonoidal

variable [(g)^*[A].PreservesFlat]

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

/-- The comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` of bifunctors,
of type `D(Y_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`, obtained by deriving the oplax monoidal structure `δ`
of `g^*`. It is the unique natural transformation such that, for `K, M` in `K(Y_ét)`, the square
```
  Lg^*(Qh K ⊗ᴸ Qh M) ──comparison──▶ Lg^*(Qh K) ⊗ᴸ Lg^*(Qh M)
          │                                    │
          │ Lg^*(μ Qh) ≫ counit                │ derivedTensorLeftDerivedUpperStarCounit
          ▼                                    ▼
   Qh(g^*(K ⊗ M)) ─────────Qh(δ g^*)──────▶ Qh(g^*K ⊗ g^*M)
```
commutes, the left vertical arrow being `leftDerivedUpperStarDerivedTensorCounit`. -/
noncomputable def leftDerivedUpperStarTensorComparison :
    leftDerivedUpperStarDerivedTensor A g ⟶ derivedTensorLeftDerivedUpperStar A g :=
  Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh)

/-- The natural isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` of bifunctors,
of type `D(Y_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`, whose underlying morphism is
`leftDerivedUpperStarTensorComparison`. -/
noncomputable def leftDerivedUpperStarTensorNatIso :
    leftDerivedUpperStarDerivedTensor A g ≅ derivedTensorLeftDerivedUpperStar A g :=
  -- `δ` is an isomorphism since `g^*` is strong monoidal.
  Functor.leftDerived₂NatIso _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (asIso (Functor.postcompose₂MapWhiskeringLeft₂
      (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh))

@[simp]
lemma leftDerivedUpperStarTensorNatIso_hom :
    (leftDerivedUpperStarTensorNatIso A g).hom = leftDerivedUpperStarTensorComparison A g :=
  rfl

/-- The comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` is an isomorphism. -/
instance isIso_leftDerivedUpperStarTensorComparison :
    IsIso (leftDerivedUpperStarTensorComparison A g) :=
  (leftDerivedUpperStarTensorNatIso A g).isIso_hom

/-- The isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` in `D(Z_ét)`, for `K, M` in `D(Y_ét)`. -/
noncomputable def leftDerivedUpperStarTensorIso
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).obj (((-⊗ᴸ-(Y)[A]).obj K).obj M) ≅
      ((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K)).obj (L((g)^*[A]).obj M) :=
  ((leftDerivedUpperStarTensorNatIso A g).app K).app M

@[simp]
lemma leftDerivedUpperStarTensorIso_hom
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarTensorIso A g K M).hom =
      ((leftDerivedUpperStarTensorComparison A g).app K).app M :=
  rfl

variable {A} in
/-- The isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` is natural in `K`. -/
@[reassoc]
lemma leftDerivedUpperStarTensorIso_hom_naturality_left
    {K K' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (f : K ⟶ K')
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map (((-⊗ᴸ-(Y)[A]).map f).app M) ≫ (leftDerivedUpperStarTensorIso A g K' M).hom =
      (leftDerivedUpperStarTensorIso A g K M).hom ≫
        ((-⊗ᴸ-(Z)[A]).map (L((g)^*[A]).map f)).app _ :=
  NatTrans.congr_app ((leftDerivedUpperStarTensorNatIso A g).hom.naturality f) M

variable {A} in
/-- The isomorphism `Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M` is natural in `M`. -/
@[reassoc]
lemma leftDerivedUpperStarTensorIso_hom_naturality_right
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    {M M' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (h : M ⟶ M') :
    L((g)^*[A]).map (((-⊗ᴸ-(Y)[A]).obj K).map h) ≫ (leftDerivedUpperStarTensorIso A g K M').hom =
      (leftDerivedUpperStarTensorIso A g K M).hom ≫
        ((-⊗ᴸ-(Z)[A]).obj _).map (L((g)^*[A]).map h) :=
  ((leftDerivedUpperStarTensorNatIso A g).hom.app K).naturality h

/-- For a fixed complex `M` on `Y`, the derived pullback commutes with tensoring by `M`:
`Lg^*(K ⊗ᴸ M) ≅ Lg^*K ⊗ᴸ Lg^*M`, naturally in `K`. That is, it compares the two functors
`K ↦ Lg^*(K ⊗ᴸ M)` and `K ↦ Lg^*K ⊗ᴸ Lg^*M` from `D(Y_ét)` to `D(Z_ét)`. This is
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso` with its second variable fixed. -/
noncomputable def derivedTensorRightCompLeftDerivedUpperStarIso
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    derivedTensorRight A Y M ⋙ L((g)^*[A]) ≅
      L((g)^*[A]) ⋙ derivedTensorRight A Z (L((g)^*[A]).obj M) :=
  NatIso.ofComponents (fun K ↦ leftDerivedUpperStarTensorIso A g K M) fun φ ↦
    NatTrans.congr_app ((leftDerivedUpperStarTensorNatIso A g).hom.naturality φ) M

end

/-- Tensoring with a complex pulled back along `g : Z ⟶ Y`, as a functor of the complex
downstairs: `N ↦ (K ↦ K ⊗ᴸ g^* N)`. -/
noncomputable def derivedTensorRightPullback :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  D((g)^*[A]) ⋙ derivedTensorRightFunctor A Z

/-- The canonical identification `Lg^* Λ_Y ≅ Λ_Z` of the units, the unit comparison asked for
in the TODO above.

The unit `Λ_Y` is the image in `D(Y_ét)` of the unit sheaf placed in degree `0`. Since `g^*` is
exact, `Lg^*` is computed by applying `g^*` degreewise, and `g^*` sends the unit sheaf of `Y`
to that of `Z` because it is strong monoidal. -/
noncomputable def leftDerivedUpperStarUnitIso : (L((g)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (leftDerivedUpperStarIsoMapDerivedCategory A g).app _ ≪≫
    D((g)^*[A]).mapIso ((DerivedCategory.quotientCompQhIso _).app
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ _))) ≪≫
    ((g)^*[A].mapDerivedCategoryFactors).app _ ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex (g)^*[A] (.up ℤ) 0).app _) ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso (Functor.Monoidal.εIso (g)^*[A]).symm) ≪≫
    ((DerivedCategory.quotientCompQhIso _).app
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ _))).symm

/-- The derived pullback preserves the unit, `Lg^* Λ_Y ≅ Λ_Z`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`). -/
theorem nonempty_iso_leftDerivedUpperStar_unit :
    Nonempty ((L((g)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) :=
  ⟨leftDerivedUpperStarUnitIso A g⟩

section Monoidal

open _root_.DerivedCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable [(g)^*[A].PreservesFlat]

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

/-- Replace the natural transformation `τ` in `(τ.app X).app Y ≫ f = k` by `σ = τ`, at the level
of natural transformations. -/
lemma app_app_comp_of_eq {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D ⥤ E} {τ : F ⟶ G} {X : C} {Y : D} {Z : E} {f : (G.obj X).obj Y ⟶ Z}
    {k : (F.obj X).obj Y ⟶ Z} (h : (τ.app X).app Y ≫ f = k) (σ : F ⟶ G) (hσ : σ = τ) :
    (σ.app X).app Y ≫ f = k :=
  hσ ▸ h

/-- The tensor comparison `Lg^*(Qh K ⊗ᴸ Qh M) ⟶ Lg^*(Qh K) ⊗ᴸ Lg^*(Qh M)` is induced by the
comonoidal structure of `g^*` on homotopy categories, through the counits of `Lg^*`. -/
lemma leftDerivedUpperStarTensorComparison_app_app_comp
    (K M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g).app (Qh.obj K)).app (Qh.obj M) ≫
        ((g)^*[A].leftDerivedFunctorCounit.app K ⊗ₘ (g)^*[A].leftDerivedFunctorCounit.app M) ≫
          μ Qh (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
            (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M) =
      L((g)^*[A]).map (μ Qh K M) ≫ (g)^*[A].leftDerivedFunctorCounit.app (K ⊗ M) ≫
        Qh.map (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M) := by
  have h := Functor.leftDerived₂NatTrans_app_app _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂ (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh)
    K M
  have e₁ : ((derivedTensorLeftDerivedUpperStarCounit A g).app K).app M =
      ((g)^*[A].leftDerivedFunctorCounit.app K ⊗ₘ (g)^*[A].leftDerivedFunctorCounit.app M) ≫
        μ Qh (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj K)
          (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M) := by
    rw [tensorHom_def]
    dsimp [derivedTensorLeftDerivedUpperStarCounit, derivedTensor]
    rw [Category.assoc]
    rfl
  have e₂ : ((leftDerivedUpperStarDerivedTensorCounit A g).app K).app M =
      L((g)^*[A]).map (μ Qh K M) ≫ (g)^*[A].leftDerivedFunctorCounit.app (K ⊗ M) := rfl
  have e₃ : ((Functor.postcompose₂MapWhiskeringLeft₂
      (mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh).app K).app M =
      Qh.map (δ ((g)^*[A].mapHomotopyCategory (.up ℤ)) K M) := rfl
  rw [e₁, e₂, e₃] at h
  simp only [Category.assoc] at h
  exact app_app_comp_of_eq h (leftDerivedUpperStarTensorComparison A g) rfl

/-- Every complex in `D(Y_ét)` is isomorphic to `Qh P` for a complex `P` whose pullback by `g`
is K-flat. -/
lemma exists_kFlatUpperStar_iso (X : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ∃ P, kFlatUpperStar A g P ∧ Nonempty (Qh.obj P ≅ X) := by
  have := Localization.essSurj (Qh (C := Sheaf Y.smallEtaleTopology A))
    (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)) (Qh.objPreimage X)
  have : IsIso (Qh.map R.w) := Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨asIso (Qh.map R.w) ≪≫ Qh.objObjPreimageIso X⟩⟩

/-- The hypothesis `hδ` of `CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare`, as a regular
definition: the kernel compares two instances of it argument by argument instead of unfolding
the commutative square. -/
def LaxSquareHδ {K₁ K₂ D₁ D₂ : Type*} [Category* K₁] [Category* K₂] [Category* D₁]
    [Category* D₂] [MonoidalCategory K₁] [MonoidalCategory K₂] [MonoidalCategory D₁]
    [MonoidalCategory D₂] {G : D₁ ⥤ D₂}
    (δG : (Functor.postcompose₂.obj G).obj (curriedTensor D₁) ⟶
      (((Functor.whiskeringLeft₂ D₂).obj G).obj G).obj (curriedTensor D₂))
    {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} [Q₁.LaxMonoidal] [Q₂.LaxMonoidal]
    {F : K₁ ⥤ K₂} [F.OplaxMonoidal] (e : ∀ a, G.obj (Q₁.obj a) ⟶ Q₂.obj (F.obj a)) : Prop :=
  ∀ a b, (δG.app (Q₁.obj a)).app (Q₁.obj b) ≫ (e a ⊗ₘ e b) ≫
    μ Q₂ (F.obj a) (F.obj b) = G.map (μ Q₁ a b) ≫ e (a ⊗ b) ≫ Q₂.map (δ F a b)

/-- `CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare`, with the hypothesis `hδ` stated as
`LaxSquareHδ δG e`. -/
@[instance_reducible]
noncomputable def ofLaxSquareHδ {K₁ K₂ D₁ D₂ : Type*} [Category* K₁] [Category* K₂]
    [Category* D₁] [Category* D₂] [MonoidalCategory K₁] [MonoidalCategory K₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂] {G : D₁ ⥤ D₂}
    (δG : (Functor.postcompose₂.obj G).obj (curriedTensor D₁) ⟶
      (((Functor.whiskeringLeft₂ D₂).obj G).obj G).obj (curriedTensor D₂))
    {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} [Q₁.LaxMonoidal] [Q₂.LaxMonoidal]
    {F : K₁ ⥤ K₂} [F.OplaxMonoidal] (e : ∀ a, G.obj (Q₁.obj a) ⟶ Q₂.obj (F.obj a))
    (he : ∀ ⦃a b : K₁⦄ (f : a ⟶ b), G.map (Q₁.map f) ≫ e b = e a ≫ Q₂.map (F.map f))
    (hδ : LaxSquareHδ δG e) [∀ a, IsIso (e a)] [IsIso (ε Q₂)] (S : ObjectProperty K₁)
    (hS : ∀ X : D₁, ∃ a, S a ∧ Nonempty (Q₁.obj a ≅ X))
    (hμ : ∀ (x : K₂) (b : K₁), S b → IsIso (μ Q₂ x (F.obj b))) :
    G.OplaxMonoidal :=
  Functor.OplaxMonoidal.ofLaxSquare δG e he hδ S hS hμ

/-- `leftDerivedUpperStarTensorComparison_app_app_comp` in the form of the hypothesis `hδ` of
`Functor.OplaxMonoidal.ofLaxSquare`. -/
lemma leftDerivedUpperStarTensorComparison_laxSquareHδ :
    LaxSquareHδ (Q₁ := Qh) (Q₂ := Qh) (F := (g)^*[A].mapHomotopyCategory (.up ℤ))
      (leftDerivedUpperStarTensorComparison A g)
      (fun a ↦ (g)^*[A].leftDerivedFunctorCounit.app a) :=
  leftDerivedUpperStarTensorComparison_app_app_comp A g

/-- The oplax monoidal structure on the derived pullback `Lg^* : D(Y_ét) ⥤ D(Z_ét)`, whose
comonoidal structure is the tensor comparison `leftDerivedUpperStarTensorComparison`. It is
induced by the oplax monoidal structure of `g^*` on homotopy categories
(`Functor.mapHomotopyCategoryOplaxMonoidal`), computing on complexes whose pullback is K-flat. -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarOplaxMonoidal : L((g)^*[A]).OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh (Sheaf Z.smallEtaleTopology A)
  ofLaxSquareHδ (Q₁ := Qh) (Q₂ := Qh)
    (F := (g)^*[A].mapHomotopyCategory (.up ℤ)) (leftDerivedUpperStarTensorComparison A g)
    (fun a ↦ (g)^*[A].leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ (g)^*[A].leftDerivedFunctorCounit.naturality f)
    (leftDerivedUpperStarTensorComparison_laxSquareHδ A g) (kFlatUpperStar A g)
    (exists_kFlatUpperStar_iso A g) (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb)

lemma isIso_leftDerivedUpperStarOplaxMonoidal_δ
    (X X' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarOplaxMonoidal A g
    IsIso (δ L((g)^*[A]) X X') :=
  inferInstanceAs (IsIso (((leftDerivedUpperStarTensorComparison A g).app X).app X'))

lemma isIso_leftDerivedUpperStarOplaxMonoidal_η :
    letI := leftDerivedUpperStarOplaxMonoidal A g
    IsIso (η L((g)^*[A])) := by
  have := DerivedCategory.isIso_ε_Qh (Sheaf Z.smallEtaleTopology A)
  have := DerivedCategory.isIso_ε_Qh (Sheaf Y.smallEtaleTopology A)
  have : IsIso (η ((g)^*[A].mapHomotopyCategory (.up ℤ))) := by
    rw [Functor.mapHomotopyCategory_η]
    infer_instance
  exact inferInstanceAs (IsIso (L((g)^*[A]).map (ε Qh) ≫
    (g)^*[A].leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (η ((g)^*[A].mapHomotopyCategory (.up ℤ))) ≫ CategoryTheory.inv (ε Qh)))

/-- The derived pullback `Lg^* : D(Y_ét) ⥤ D(Z_ét)` as a monoidal functor: the oplax monoidal
structure `leftDerivedUpperStarOplaxMonoidal`, whose structure maps are isomorphisms. -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarMonoidal : L((g)^*[A]).Monoidal :=
  letI := leftDerivedUpperStarOplaxMonoidal A g
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_δ A g
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_η A g
  (Functor.CoreMonoidal.ofOplaxMonoidal _).toMonoidal

end Monoidal

/-- The derived pullback `Lg^* : D(Y_ét) ⥤ D(Z_ét)` is a monoidal functor for the derived tensor
products. This is the monoidality of derived pullback in blueprint
`prose-03-02` (within `theorem-f-shriek-ell-adic-coefficients--4`).

The monoidal structure is `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`, whose
tensor comparison is `leftDerivedUpperStarTensorIso`. -/
theorem nonempty_monoidal_leftDerivedUpperStar [Etale.UpperStarPreservesFlat A] :
    Nonempty (L((g)^*[A])).Monoidal :=
  ⟨leftDerivedUpperStarMonoidal A g⟩

end Etale

end AlgebraicGeometry
