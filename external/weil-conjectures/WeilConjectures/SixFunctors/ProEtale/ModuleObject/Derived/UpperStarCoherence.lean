/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Coherence of the derived pullbacks of module objects

Let `Λ` be a commutative condensed ring. The composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` (`ProEtale.CondensedRing.leftDerivedUpperStarComp`) of the derived
pullbacks of module objects over `Λ`, and the identity isomorphisms `L(𝟙 X)^* ≅ 𝟭`
(`ProEtale.CondensedRing.leftDerivedUpperStarId`, defined here), satisfy the associativity and
unit laws.

The pullbacks of module objects are exact, and for exact functors the derived isomorphisms are
determined by their compatibility with the counits `Qh ⋙ L(F) ⟶ F ⋙ Qh` of the left derived
functors, which are isomorphisms. The laws thus follow from the laws of the underived pullbacks
(`ProEtale.CondensedRing.upperStarComp_hom_app_comp_upperStarComp_hom_app`,
`ProEtale.CondensedRing.upperStarComp_id_left`, `ProEtale.CondensedRing.upperStarComp_id_right`).
This argument is carried out first for abstract exact functors between abelian categories with
functorial flat resolutions (`CategoryTheory.Functor.leftDerivedFunctorFactorIso_assoc_app`,
`CategoryTheory.Functor.leftDerivedFunctorFactorIso_id_left_app`,
`CategoryTheory.Functor.leftDerivedFunctorFactorIso_id_right_app`), where the computations are
cheap, and then specialized to the module objects.

## Main definitions

- `CategoryTheory.Functor.leftDerivedFunctorFactorIso`: the isomorphism `L(A) ≅ L(B) ⋙ L(B')`
  induced by an isomorphism `A ≅ B ⋙ B'` of exact functors.
- `CategoryTheory.Functor.leftDerivedFunctorIdIso`: the isomorphism `L(I) ≅ 𝟭` induced by an
  isomorphism `I ≅ 𝟭` of exact functors.
- `ProEtale.CondensedRing.leftDerivedUpperStarId`: the identity isomorphism `L(𝟙 X)^* ≅ 𝟭`.

## Main results

- `ProEtale.CondensedRing.leftDerivedUpperStarComp_assoc_app`: the associativity law.
- `ProEtale.CondensedRing.leftDerivedUpperStarComp_id_left_app`,
  `ProEtale.CondensedRing.leftDerivedUpperStarComp_id_right_app`: the unit laws.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-! ### Additive functors on homotopy categories -/

section Homotopy

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]

/-- The associativity law of isomorphisms of additive functors, on the homotopy categories. -/
lemma mapHomotopyCategory_assoc_of_app {H : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {F : C₃ ⥤ C₄}
    {GH : C₁ ⥤ C₃} {FG : C₂ ⥤ C₄} {FGH FGH' : C₁ ⥤ C₄} [H.Additive] [G.Additive] [F.Additive]
    [GH.Additive] [FG.Additive] [FGH.Additive] [FGH'.Additive]
    (e₁ : FGH ≅ H ⋙ FG) (eFG : FG ≅ G ⋙ F) (e₂ : FGH' ≅ GH ⋙ F) (eGH : GH ≅ H ⋙ G)
    (c : FGH ≅ FGH')
    (h : ∀ M, e₁.hom.app M ≫ eFG.hom.app (H.obj M) =
      c.hom.app M ≫ e₂.hom.app M ≫ F.map (eGH.hom.app M))
    (P : HomotopyCategory C₁ (.up ℤ)) :
    (NatTrans.mapHomotopyCategory e₁.hom (.up ℤ)).app P ≫
        (NatTrans.mapHomotopyCategory eFG.hom (.up ℤ)).app
          ((H.mapHomotopyCategory (.up ℤ)).obj P) =
      (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app P ≫
        (NatTrans.mapHomotopyCategory e₂.hom (.up ℤ)).app P ≫
          (F.mapHomotopyCategory (.up ℤ)).map
            ((NatTrans.mapHomotopyCategory eGH.hom (.up ℤ)).app P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex e₁.hom _).app K) ≫
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex eFG.hom _).app
        ((H.mapHomologicalComplex _).obj K)) =
    (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex c.hom _).app K) ≫
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex e₂.hom _).app K) ≫
        (HomotopyCategory.quotient _ _).map ((F.mapHomologicalComplex _).map
          ((NatTrans.mapHomologicalComplex eGH.hom _).app K))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact h (K.X n)

end Homotopy

/-! ### Exact functors -/

section Generic

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  [MonoidalCategory C₁] [MonoidalPreadditive C₁] [HasCountableCoproducts C₁]
  [HasColimitsOfShape ℤ C₁] [HasExactColimitsOfShape ℤ C₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).obj X)]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁]

/-- The isomorphism `L(I) ≅ 𝟭` of total left derived functors induced by an isomorphism
`ι : I ≅ 𝟭` of exact functors: the derived functor of `ι`, followed by `L(𝟭) ≅ D(𝟭) ≅ 𝟭`. -/
noncomputable abbrev leftDerivedFunctorIdIso {I : C₁ ⥤ C₁} [I.Additive] [PreservesFiniteLimits I]
    [PreservesFiniteColimits I] (ι : I ≅ 𝟭 C₁) : I.leftDerivedFunctor ≅ 𝟭 _ :=
  I.leftDerivedFunctorNatIso ι ≪≫ (𝟭 C₁).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    mapDerivedCategoryIdIso C₁

/-- The naturality of the counit of the left derived functor, with the composite functors
unfolded. -/
lemma leftDerivedFunctorCounit_naturality {A : C₁ ⥤ C₂} [A.Additive] [PreservesFiniteLimits A]
    [PreservesFiniteColimits A] {P Q : HomotopyCategory C₁ (.up ℤ)} (φ : P ⟶ Q) :
    A.leftDerivedFunctor.map (Qh.map φ) ≫ A.leftDerivedFunctorCounit.app Q =
      A.leftDerivedFunctorCounit.app P ≫ Qh.map ((A.mapHomotopyCategory (.up ℤ)).map φ) :=
  A.leftDerivedFunctorCounit.naturality φ

/-- On the image `Qh K` of a complex, the isomorphism `L(I) ≅ 𝟭` induced by `ι : I ≅ 𝟭` is `ι`
itself, read through the counit of the derived functor. -/
lemma leftDerivedFunctorIdIso_hom_app_Qh_obj {I : C₁ ⥤ C₁} [I.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I] (ι : I ≅ 𝟭 C₁)
    (K : HomotopyCategory C₁ (.up ℤ)) :
    (leftDerivedFunctorIdIso ι).hom.app (Qh.obj K) =
      I.leftDerivedFunctorCounit.app K ≫
        Qh.map ((NatTrans.mapHomotopyCategory ι.hom (.up ℤ)).app K ≫
          (mapHomotopyCategoryIdIso C₁ (.up ℤ)).hom.app K) := by
  have hfac := NatTrans.congr_app (𝟭 C₁).leftDerivedFunctorIsoMapDerivedCategory_hom_fac K
  have hid := NatTrans.congr_app (congrArg Iso.hom (mapDerivedCategoryIdIso_factorsh C₁)) K
  dsimp at hfac hid
  simp only [Category.comp_id] at hid
  rw [Iso.trans_hom, NatTrans.comp_app, Iso.trans_hom, NatTrans.comp_app, hid, reassoc_of% hfac,
    ← Category.assoc, leftDerivedFunctorNatIso_hom_app_comp_counit, Category.assoc,
    Functor.map_comp]

/-- The isomorphism `L(A) ≅ L(B)` induced by an equality `A = B` of exact functors is
`eqToHom`. -/
lemma leftDerivedFunctorNatIso_eqToIso_hom_app {A B : C₁ ⥤ C₂} [A.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A] [B.Additive] [PreservesFiniteLimits B]
    [PreservesFiniteColimits B] (h : A = B) (K : DerivedCategory C₁) :
    (A.leftDerivedFunctorNatIso (eqToIso h)).hom.app K = eqToHom (by subst h; rfl) := by
  subst h
  simp only [eqToIso_refl, leftDerivedFunctorNatIso, Iso.trans_hom, NatTrans.comp_app,
    mapDerivedCategoryNatIso_refl, Category.id_comp, Iso.symm_hom,
    Iso.hom_inv_id_app]
  rfl

section FlatTwo

variable [MonoidalCategory C₂] [MonoidalPreadditive C₂] [HasCountableCoproducts C₂]
  [HasColimitsOfShape ℤ C₂] [HasExactColimitsOfShape ℤ C₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₂), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).obj X)]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₂]

/-- The isomorphism `L(A) ≅ L(B) ⋙ L(B')` of total left derived functors induced by an
isomorphism `e : A ≅ B ⋙ B'` of exact functors. -/
noncomputable abbrev leftDerivedFunctorFactorIso {A : C₁ ⥤ C₃} {B : C₁ ⥤ C₂} {B' : C₂ ⥤ C₃}
    [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [B'.Additive] [PreservesFiniteLimits B'] [PreservesFiniteColimits B'] (e : A ≅ B ⋙ B') :
    A.leftDerivedFunctor ≅ B.leftDerivedFunctor ⋙ B'.leftDerivedFunctor :=
  A.leftDerivedFunctorNatIso e ≪≫ B.leftDerivedFunctorCompIso B'

/-- On the image `Qh K` of a complex, the isomorphism `L(A) ≅ L(B) ⋙ L(B')` induced by
`e : A ≅ B ⋙ B'` is `e` itself, read through the counits of the derived functors. -/
lemma leftDerivedFunctorFactorIso_hom_app_comp_counit {A : C₁ ⥤ C₃} {B : C₁ ⥤ C₂}
    {B' : C₂ ⥤ C₃} [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [B'.Additive] [PreservesFiniteLimits B'] [PreservesFiniteColimits B'] (e : A ≅ B ⋙ B')
    (K : HomotopyCategory C₁ (.up ℤ)) :
    (leftDerivedFunctorFactorIso e).hom.app (Qh.obj K) ≫
        B'.leftDerivedFunctor.map (B.leftDerivedFunctorCounit.app K) ≫
          B'.leftDerivedFunctorCounit.app ((B.mapHomotopyCategory (.up ℤ)).obj K) =
      A.leftDerivedFunctorCounit.app K ≫
        Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  rw [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    leftDerivedFunctorCompIso_hom_app_comp_counit, leftDerivedFunctorNatIso_hom_app_comp_counit]

section IdLeft

variable {A B : C₁ ⥤ C₂} [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]

/-- **Left unit law** for the isomorphisms `L(A) ≅ L(B) ⋙ L(B')` induced by isomorphisms of
exact functors. -/
lemma leftDerivedFunctorFactorIso_id_left_app {I : C₂ ⥤ C₂} [I.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I] (e : A ≅ B ⋙ I) (ι : I ≅ 𝟭 C₂)
    (c : A ≅ B) (h : ∀ M, e.hom.app M ≫ ι.hom.app (B.obj M) = c.hom.app M)
    (K : DerivedCategory C₁) :
    (leftDerivedFunctorFactorIso e).hom.app K ≫
        (leftDerivedFunctorIdIso ι).hom.app (B.leftDerivedFunctor.obj K) =
      (A.leftDerivedFunctorNatIso c).hom.app K := by
  have := Localization.natTrans_ext (L := Qh) (W := HomotopyCategory.quasiIso C₁ (.up ℤ))
    (τ := (leftDerivedFunctorFactorIso e).hom ≫
      Functor.whiskerLeft B.leftDerivedFunctor (leftDerivedFunctorIdIso ι).hom)
    (τ' := (A.leftDerivedFunctorNatIso c).hom)
    fun P ↦ by
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
      rw [← cancel_mono (B.leftDerivedFunctorCounit.app P)]
      have h₁ : I.leftDerivedFunctor.map (B.leftDerivedFunctorCounit.app P) ≫
          (leftDerivedFunctorIdIso ι).hom.app (Qh.obj ((B.mapHomotopyCategory (.up ℤ)).obj P)) =
          (leftDerivedFunctorIdIso ι).hom.app (B.leftDerivedFunctor.obj (Qh.obj P)) ≫
            B.leftDerivedFunctorCounit.app P :=
        (leftDerivedFunctorIdIso ι).hom.naturality (B.leftDerivedFunctorCounit.app P)
      rw [Category.assoc, ← h₁, leftDerivedFunctorIdIso_hom_app_Qh_obj,
        reassoc_of% (leftDerivedFunctorFactorIso_hom_app_comp_counit e P),
        leftDerivedFunctorNatIso_hom_app_comp_counit, ← Functor.map_comp]
      congr 2
      rw [mapHomotopyCategoryIdIso_hom_app_eq_id]
      erw [Category.comp_id]
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
      change (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex e.hom _).app K) ≫
        (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex ι.hom _).app
          ((B.mapHomologicalComplex _).obj K)) =
        (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex c.hom _).app K)
      rw [← Functor.map_comp]
      congr 1
      ext n
      simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
      exact h (K.X n)
  exact NatTrans.congr_app this K

end IdLeft

section FlatThree

variable [MonoidalCategory C₃] [MonoidalPreadditive C₃] [HasCountableCoproducts C₃]
  [HasColimitsOfShape ℤ C₃] [HasExactColimitsOfShape ℤ C₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₃), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₃), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₃), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C₃), PreservesColimitsOfShape ℤ ((curriedTensor C₃).obj X)]
  [∀ (X : C₃), PreservesColimitsOfShape ℤ ((curriedTensor C₃).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₃]

section Laws

variable {H : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {F : C₃ ⥤ C₄} {GH : C₁ ⥤ C₃} {FG : C₂ ⥤ C₄}
  {FGH FGH' : C₁ ⥤ C₄}
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [GH.Additive] [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
  [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [FGH.Additive] [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
  [FGH'.Additive] [PreservesFiniteLimits FGH'] [PreservesFiniteColimits FGH']
  (e₁ : FGH ≅ H ⋙ FG) (eFG : FG ≅ G ⋙ F) (e₂ : FGH' ≅ GH ⋙ F) (eGH : GH ≅ H ⋙ G)
  (c : FGH ≅ FGH')

/-- **Associativity** of the isomorphisms `L(A) ≅ L(B) ⋙ L(B')` induced by isomorphisms of exact
functors, on the image of a complex: it follows from the associativity of the isomorphisms of
the exact functors. -/
lemma leftDerivedFunctorFactorIso_assoc_app_Qh_obj
    (h : ∀ M, e₁.hom.app M ≫ eFG.hom.app (H.obj M) =
      c.hom.app M ≫ e₂.hom.app M ≫ F.map (eGH.hom.app M))
    (P : HomotopyCategory C₁ (.up ℤ)) :
    (leftDerivedFunctorFactorIso e₁).hom.app (Qh.obj P) ≫
        (leftDerivedFunctorFactorIso eFG).hom.app (H.leftDerivedFunctor.obj (Qh.obj P)) =
      (FGH.leftDerivedFunctorNatIso c).hom.app (Qh.obj P) ≫
        (leftDerivedFunctorFactorIso e₂).hom.app (Qh.obj P) ≫
          F.leftDerivedFunctor.map ((leftDerivedFunctorFactorIso eGH).hom.app (Qh.obj P)) := by
  rw [← cancel_mono (F.leftDerivedFunctor.map (G.leftDerivedFunctor.map
      (H.leftDerivedFunctorCounit.app P)) ≫
    F.leftDerivedFunctor.map (G.leftDerivedFunctorCounit.app
      ((H.mapHomotopyCategory (.up ℤ)).obj P)) ≫
    F.leftDerivedFunctorCounit.app ((G.mapHomotopyCategory (.up ℤ)).obj
      ((H.mapHomotopyCategory (.up ℤ)).obj P)))]
  have u₁ := leftDerivedFunctorFactorIso_hom_app_comp_counit eGH P
  have u₂ := leftDerivedFunctorFactorIso_hom_app_comp_counit e₂ P
  have u₃ := leftDerivedFunctorFactorIso_hom_app_comp_counit eFG
    ((H.mapHomotopyCategory (.up ℤ)).obj P)
  have u₄ := leftDerivedFunctorFactorIso_hom_app_comp_counit e₁ P
  have u₅ := leftDerivedFunctorNatIso_hom_app_comp_counit FGH c P
  have n₁ : F.leftDerivedFunctor.map
      (Qh.map ((NatTrans.mapHomotopyCategory eGH.hom (.up ℤ)).app P)) ≫
      F.leftDerivedFunctorCounit.app ((G.mapHomotopyCategory (.up ℤ)).obj
        ((H.mapHomotopyCategory (.up ℤ)).obj P)) =
      F.leftDerivedFunctorCounit.app ((GH.mapHomotopyCategory (.up ℤ)).obj P) ≫
        Qh.map ((F.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory eGH.hom (.up ℤ)).app P)) :=
    leftDerivedFunctorCounit_naturality _
  have n₂ : (leftDerivedFunctorFactorIso eFG).hom.app (H.leftDerivedFunctor.obj (Qh.obj P)) ≫
      F.leftDerivedFunctor.map (G.leftDerivedFunctor.map (H.leftDerivedFunctorCounit.app P)) =
      FG.leftDerivedFunctor.map (H.leftDerivedFunctorCounit.app P) ≫
        (leftDerivedFunctorFactorIso eFG).hom.app _ :=
    ((leftDerivedFunctorFactorIso eFG).hom.naturality _).symm
  have hL : ((leftDerivedFunctorFactorIso e₁).hom.app (Qh.obj P) ≫
      (leftDerivedFunctorFactorIso eFG).hom.app (H.leftDerivedFunctor.obj (Qh.obj P))) ≫
      F.leftDerivedFunctor.map (G.leftDerivedFunctor.map (H.leftDerivedFunctorCounit.app P)) ≫
      F.leftDerivedFunctor.map (G.leftDerivedFunctorCounit.app
        ((H.mapHomotopyCategory (.up ℤ)).obj P)) ≫
      F.leftDerivedFunctorCounit.app ((G.mapHomotopyCategory (.up ℤ)).obj
        ((H.mapHomotopyCategory (.up ℤ)).obj P)) =
      FGH.leftDerivedFunctorCounit.app P ≫
        Qh.map ((NatTrans.mapHomotopyCategory e₁.hom (.up ℤ)).app P) ≫
        Qh.map ((NatTrans.mapHomotopyCategory eFG.hom (.up ℤ)).app
          ((H.mapHomotopyCategory (.up ℤ)).obj P)) := by
    simp only [Category.assoc]
    rw [reassoc_of% n₂, u₃, reassoc_of% u₄]
  have hR : ((FGH.leftDerivedFunctorNatIso c).hom.app (Qh.obj P) ≫
      (leftDerivedFunctorFactorIso e₂).hom.app (Qh.obj P) ≫
      F.leftDerivedFunctor.map ((leftDerivedFunctorFactorIso eGH).hom.app (Qh.obj P))) ≫
      F.leftDerivedFunctor.map (G.leftDerivedFunctor.map (H.leftDerivedFunctorCounit.app P)) ≫
      F.leftDerivedFunctor.map (G.leftDerivedFunctorCounit.app
        ((H.mapHomotopyCategory (.up ℤ)).obj P)) ≫
      F.leftDerivedFunctorCounit.app ((G.mapHomotopyCategory (.up ℤ)).obj
        ((H.mapHomotopyCategory (.up ℤ)).obj P)) =
      FGH.leftDerivedFunctorCounit.app P ≫
        Qh.map ((NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app P) ≫
        Qh.map ((NatTrans.mapHomotopyCategory e₂.hom (.up ℤ)).app P) ≫
        Qh.map ((F.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory eGH.hom (.up ℤ)).app P)) := by
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    simp only [Category.assoc]
    rw [u₁, Functor.map_comp_assoc, n₁, reassoc_of% u₂, reassoc_of% u₅]
  rw [hL, hR, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    mapHomotopyCategory_assoc_of_app e₁ eFG e₂ eGH c h]

/-- **Associativity** of the isomorphisms `L(A) ≅ L(B) ⋙ L(B')` induced by isomorphisms of exact
functors: it follows from the associativity of the isomorphisms of the exact functors. -/
lemma leftDerivedFunctorFactorIso_assoc_app
    (h : ∀ M, e₁.hom.app M ≫ eFG.hom.app (H.obj M) =
      c.hom.app M ≫ e₂.hom.app M ≫ F.map (eGH.hom.app M))
    (K : DerivedCategory C₁) :
    (leftDerivedFunctorFactorIso e₁).hom.app K ≫
        (leftDerivedFunctorFactorIso eFG).hom.app (H.leftDerivedFunctor.obj K) =
      (FGH.leftDerivedFunctorNatIso c).hom.app K ≫
        (leftDerivedFunctorFactorIso e₂).hom.app K ≫
          F.leftDerivedFunctor.map ((leftDerivedFunctorFactorIso eGH).hom.app K) := by
  have := Localization.natTrans_ext (L := Qh) (W := HomotopyCategory.quasiIso C₁ (.up ℤ))
    (τ := (leftDerivedFunctorFactorIso e₁).hom ≫
      Functor.whiskerLeft H.leftDerivedFunctor (leftDerivedFunctorFactorIso eFG).hom)
    (τ' := (FGH.leftDerivedFunctorNatIso c).hom ≫ (leftDerivedFunctorFactorIso e₂).hom ≫
      Functor.whiskerRight (leftDerivedFunctorFactorIso eGH).hom F.leftDerivedFunctor)
    fun P ↦ by
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      exact leftDerivedFunctorFactorIso_assoc_app_Qh_obj e₁ eFG e₂ eGH c h P
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using
    NatTrans.congr_app this K

omit c in
/-- The associativity law when the comparison of the two composite functors is an equality. -/
private lemma leftDerivedFunctorFactorIso_assoc_eq_app (hc : FGH = FGH')
    (h : ∀ M, e₁.hom.app M ≫ eFG.hom.app (H.obj M) =
      (eqToIso hc).hom.app M ≫ e₂.hom.app M ≫ F.map (eGH.hom.app M))
    (K : DerivedCategory C₁) :
    (leftDerivedFunctorFactorIso e₁).hom.app K ≫
        (leftDerivedFunctorFactorIso eFG).hom.app (H.leftDerivedFunctor.obj K) =
      eqToHom (by clear c; subst hc; rfl) ≫
        (leftDerivedFunctorFactorIso e₂).hom.app K ≫
          F.leftDerivedFunctor.map ((leftDerivedFunctorFactorIso eGH).hom.app K) := by
  rw [← leftDerivedFunctorNatIso_eqToIso_hom_app hc K]
  exact leftDerivedFunctorFactorIso_assoc_app e₁ eFG e₂ eGH (eqToIso hc) h K

end Laws

end FlatThree

end FlatTwo

section IdRight

variable {A B : C₁ ⥤ C₂} [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]

/-- **Right unit law** for the isomorphisms `L(A) ≅ L(B) ⋙ L(B')` induced by isomorphisms of
exact functors. -/
lemma leftDerivedFunctorFactorIso_id_right_app {I : C₁ ⥤ C₁} [I.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I] (e : A ≅ I ⋙ B) (ι : I ≅ 𝟭 C₁)
    (c : A ≅ B) (h : ∀ M, e.hom.app M ≫ B.map (ι.hom.app M) = c.hom.app M)
    (K : DerivedCategory C₁) :
    (leftDerivedFunctorFactorIso e).hom.app K ≫
        B.leftDerivedFunctor.map ((leftDerivedFunctorIdIso ι).hom.app K) =
      (A.leftDerivedFunctorNatIso c).hom.app K := by
  have := Localization.natTrans_ext (L := Qh) (W := HomotopyCategory.quasiIso C₁ (.up ℤ))
    (τ := (leftDerivedFunctorFactorIso e).hom ≫
      Functor.whiskerRight (leftDerivedFunctorIdIso ι).hom B.leftDerivedFunctor)
    (τ' := (A.leftDerivedFunctorNatIso c).hom)
    fun P ↦ by
      simp only [NatTrans.comp_app, Functor.whiskerRight_app]
      rw [← cancel_mono (B.leftDerivedFunctorCounit.app P)]
      have n : B.leftDerivedFunctor.map
          (Qh.map ((NatTrans.mapHomotopyCategory ι.hom (.up ℤ)).app P ≫
            (mapHomotopyCategoryIdIso C₁ (.up ℤ)).hom.app P)) ≫ B.leftDerivedFunctorCounit.app P =
          B.leftDerivedFunctorCounit.app ((I.mapHomotopyCategory (.up ℤ)).obj P) ≫
            Qh.map ((B.mapHomotopyCategory (.up ℤ)).map
              ((NatTrans.mapHomotopyCategory ι.hom (.up ℤ)).app P ≫
                (mapHomotopyCategoryIdIso C₁ (.up ℤ)).hom.app P)) :=
        leftDerivedFunctorCounit_naturality _
      rw [Category.assoc, leftDerivedFunctorIdIso_hom_app_Qh_obj, Functor.map_comp,
        Category.assoc, n,
        reassoc_of% (leftDerivedFunctorFactorIso_hom_app_comp_counit e P),
        leftDerivedFunctorNatIso_hom_app_comp_counit, ← Functor.map_comp]
      congr 2
      rw [mapHomotopyCategoryIdIso_hom_app_eq_id]
      erw [Category.comp_id]
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
      change (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex e.hom _).app K) ≫
        (HomotopyCategory.quotient _ _).map ((B.mapHomologicalComplex _).map
          ((NatTrans.mapHomologicalComplex ι.hom _).app K)) =
        (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex c.hom _).app K)
      rw [← Functor.map_comp]
      congr 1
      ext n
      simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
        Functor.mapHomologicalComplex_map_f]
      exact h (K.X n)
  exact NatTrans.congr_app this K

end IdRight

end Generic

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback of module objects over `Λ`:
the derived functor of `ProEtale.CondensedRing.upperStarId`, followed by `L(𝟭) ≅ D(𝟭) ≅ 𝟭`. -/
noncomputable def leftDerivedUpperStarId (X : Scheme.{u}) : L((𝟙 X)^*⟦Λ⟧) ≅ 𝟭 _ :=
  Functor.leftDerivedFunctorIdIso (upperStarId Λ X)

variable {W X Y Z : Scheme.{u}}

lemma leftDerivedUpperStarComp_eq_leftDerivedFunctorFactorIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftDerivedUpperStarComp Λ f g = Functor.leftDerivedFunctorFactorIso (upperStarComp Λ f g) :=
  rfl

/-- **Associativity** of the composition isomorphisms of the derived pullbacks of module
objects: the two ways of identifying `L(f ≫ g ≫ h)^*` with `Lh^* ⋙ Lg^* ⋙ Lf^*` agree. -/
lemma leftDerivedUpperStarComp_assoc_app (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (leftDerivedUpperStarComp Λ (f ≫ g) h).hom.app K ≫
        (leftDerivedUpperStarComp Λ f g).hom.app (L((h)^*⟦Λ⟧).obj K) =
      eqToHom (by rw [Category.assoc]) ≫ (leftDerivedUpperStarComp Λ f (g ≫ h)).hom.app K ≫
        L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarComp Λ g h).hom.app K) := by
  exact Functor.leftDerivedFunctorFactorIso_assoc_eq_app (upperStarComp Λ (f ≫ g) h)
    (upperStarComp Λ f g) (upperStarComp Λ f (g ≫ h)) (upperStarComp Λ g h)
    (by rw [Category.assoc])
    (upperStarComp_hom_app_comp_upperStarComp_hom_app Λ f g h) K

-- the instances of the general lemma are found for each of the categories of module objects
/-- **Left unit law** for the composition isomorphisms of the derived pullbacks of module
objects. -/
lemma leftDerivedUpperStarComp_id_left_app (g : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarComp Λ (𝟙 X) g).hom.app K ≫
        (leftDerivedUpperStarId Λ X).hom.app (L((g)^*⟦Λ⟧).obj K) =
      eqToHom (by rw [Category.id_comp]; rfl) := by
  rw [leftDerivedUpperStarComp_eq_leftDerivedFunctorFactorIso, leftDerivedUpperStarId,
    Functor.leftDerivedFunctorFactorIso_id_left_app (upperStarComp Λ (𝟙 X) g) (upperStarId Λ X)
      (upperStarCongr Λ (Category.id_comp g)) (fun M ↦ ?_) K,
    upperStarCongr, Functor.leftDerivedFunctorNatIso_eqToIso_hom_app]
  rw [upperStarComp_id_left]
  simp

-- the instances of the general lemma are found for each of the categories of module objects
/-- **Right unit law** for the composition isomorphisms of the derived pullbacks of module
objects. -/
lemma leftDerivedUpperStarComp_id_right_app (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarComp Λ f (𝟙 Y)).hom.app K ≫
        L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app K) =
      eqToHom (by rw [Category.comp_id]; rfl) := by
  rw [leftDerivedUpperStarComp_eq_leftDerivedFunctorFactorIso, leftDerivedUpperStarId,
    Functor.leftDerivedFunctorFactorIso_id_right_app (upperStarComp Λ f (𝟙 Y)) (upperStarId Λ Y)
      (upperStarCongr Λ (Category.comp_id f)) (fun M ↦ ?_) K,
    upperStarCongr, Functor.leftDerivedFunctorNatIso_eqToIso_hom_app]
  rw [upperStarComp_id_right]
  simp [← Functor.map_comp]

end AlgebraicGeometry.ProEtale.CondensedRing
