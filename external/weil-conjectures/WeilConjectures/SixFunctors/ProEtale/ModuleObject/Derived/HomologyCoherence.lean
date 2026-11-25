/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.Algebra.Homology.ShortComplex.MapHomologyIsoComp
public import WeilConjectures.Algebra.Homology.MapHomologicalComplexHomologyIso
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso

/-!
# Homology of the derived pullbacks of module objects

The left derived functor `L(F)` of an exact functor `F` commutes with the homology functors
(`CategoryTheory.Functor.leftDerivedFunctorHomologyFunctorIso`). We show that these
commutation isomorphisms are compatible with the isomorphisms of derived functors induced by
isomorphisms of exact functors, with the composition isomorphisms `L(F ⋙ G) ≅ L(F) ⋙ L(G)` and
with the identity isomorphisms `L(I) ≅ 𝟭`. This is first done for the functors
`Functor.mapDerivedCategory` (by checking on the images of complexes), then for the left
derived functors of exact functors between abelian categories with functorial flat
resolutions, and finally specialized to the derived pullbacks of module objects over a
commutative condensed ring `Λ`.

## Main definitions

- `ProEtale.CondensedRing.leftDerivedUpperStarHomologyIso`: the commutation
  `H^n(-) ⋙ f^* ≅ L(f^*) ⋙ H^n(-)`.

## Main results

- `CategoryTheory.ShortComplex.mapHomologyIso_id`: the isomorphism
  `(S.map (𝟭 C)).homology ≅ S.homology` is the identity.
- `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_comp_hom_app`,
  `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_id_hom_app`: the compatibility
  of `Functor.mapDerivedCategoryHomologyFunctorIso` with `Functor.mapDerivedCategoryCompIso` and
  `Functor.mapDerivedCategoryIdIso`.
- `CategoryTheory.Functor.leftDerivedFunctorHomologyFunctorIso_naturality`,
  `CategoryTheory.Functor.leftDerivedFunctorHomologyFunctorIso_comp`,
  `CategoryTheory.Functor.leftDerivedFunctorHomologyFunctorIso_factorIso`,
  `CategoryTheory.Functor.leftDerivedFunctorHomologyFunctorIso_idIso`: the same compatibilities
  for left derived functors.
- `ProEtale.CondensedRing.leftDerivedUpperStarHomologyIso_comp_hom_app`,
  `ProEtale.CondensedRing.leftDerivedUpperStarHomologyIso_hom_app_idIso`,
  `ProEtale.CondensedRing.leftDerivedUpperStarHomologyIso_hom_app_id`: their specializations to
  the derived pullbacks of module objects.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  [CategoryWithHomology C]

/-- The isomorphism `(S.map (𝟭 C)).homology ≅ S.homology` is the identity. -/
lemma mapHomologyIso_id (S : ShortComplex C) :
    S.mapHomologyIso (𝟭 C) = Iso.refl _ := by
  ext
  refine Eq.trans ?_ S.leftHomologyIso.inv_hom_id
  refine (cancel_epi (S.map (𝟭 C)).homologyπ).1 ?_
  refine ((S.homologyData.left.map (𝟭 C)).homologyπ_comp_homologyIso_hom).trans
    (Eq.trans ?_ S.homologyData.left.homologyπ_comp_homologyIso_hom.symm)
  refine congrArg (· ≫ _) ((cancel_mono S.homologyData.left.i).1 ?_)
  exact (LeftHomologyData.cyclesIso_hom_comp_i _).trans
    (LeftHomologyData.cyclesIso_hom_comp_i _).symm

end CategoryTheory.ShortComplex

namespace CategoryTheory.Functor

section HomologicalComplex

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [CategoryWithHomology C] [CategoryWithHomology D] [CategoryWithHomology E]
  {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- The commutation of `𝟭 C` with the homology of complexes is the identity. -/
lemma mapHomologicalComplexHomologyIso_id_hom_app (K : HomologicalComplex C c) :
    ((𝟭 C).mapHomologicalComplexHomologyIso c i).hom.app K = 𝟙 _ := by
  rw [mapHomologicalComplexHomologyIso_hom_app_eq, ShortComplex.mapHomologyIso_id]
  rfl

/-- The commutation of `𝟭 C` with the homology of complexes is the identity (inverse form). -/
lemma mapHomologicalComplexHomologyIso_id_inv_app (K : HomologicalComplex C c) :
    ((𝟭 C).mapHomologicalComplexHomologyIso c i).inv.app K = 𝟙 _ := by
  rw [← Iso.app_inv]
  refine Iso.inv_ext ?_
  rw [Iso.app_hom, mapHomologicalComplexHomologyIso_id_hom_app]
  exact Category.id_comp _

end HomologicalComplex

section DerivedCategory

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- The commutation `H^n(-) ⋙ (F ⋙ G) ≅ D(F ⋙ G) ⋙ H^n(-)` of the composite of two exact
functors with the homology functors is, through `Functor.mapDerivedCategoryCompIso`, the
composite of the commutations for `F` and for `G`. -/
@[reassoc]
lemma mapDerivedCategoryHomologyFunctorIso_comp_hom_app (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (n : ℤ) (K : DerivedCategory C) :
    ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor E n).map ((mapDerivedCategoryCompIso F G).inv.app K) =
      G.map ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app K) ≫
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app (F.mapDerivedCategory.obj K) := by
  have h : ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom ≫
      whiskerRight (mapDerivedCategoryCompIso F G).inv (DerivedCategory.homologyFunctor E n) =
      whiskerRight (F.mapDerivedCategoryHomologyFunctorIso n).hom G ≫
        whiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyFunctorIso n).hom := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun L => ?_)
    have hc₀ : (F ⋙ G).mapDerivedCategoryFactors.inv.app L ≫
        (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj L) =
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app L) := by
      rw [← cancel_epi ((F ⋙ G).mapDerivedCategoryFactors.hom.app L), Iso.hom_inv_id_app_assoc,
        ← mapDerivedCategoryCompIso_hom_app_factors]
      simp [← Functor.map_comp]
    have hc : (DerivedCategory.homologyFunctor E n).map
          ((F ⋙ G).mapDerivedCategoryFactors.inv.app L) ≫
        (DerivedCategory.homologyFunctor E n).map
          ((mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj L)) =
        (DerivedCategory.homologyFunctor E n).map
          (G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        (DerivedCategory.homologyFunctor E n).map
          (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app L)) := by
      rw [← Functor.map_comp, ← Functor.map_comp, hc₀]
    have hG : G.map ((DerivedCategory.homologyFunctor D n).map
          (F.mapDerivedCategoryFactors.inv.app L)) ≫
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) =
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        (DerivedCategory.homologyFunctor E n).map
          (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app L)) :=
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality _
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
    rw [mapDerivedCategoryHomologyFunctorIso_hom_app_Q,
      mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [Functor.map_comp, Category.assoc]
    rw [hc, hG, mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [Category.assoc]
    rw [← G.map_comp_assoc ((DerivedCategory.homologyFunctorFactors D n).inv.app _)
        ((DerivedCategory.homologyFunctorFactors D n).hom.app _),
      Iso.inv_hom_id_app, G.map_id, Category.id_comp,
      mapHomologicalComplexHomologyIso_comp_inv_app, Category.assoc]
    rfl
  exact congr_app h K

variable (C) in
/-- On the image of a cochain complex, the identity isomorphism `D(𝟭 C) ≅ 𝟭` is the
factorization isomorphism of `D(𝟭 C)`, followed by the identity isomorphism of complexes. -/
lemma mapDerivedCategoryIdIso_hom_app_Q (L : CochainComplex C ℤ) :
    (mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj L) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app L ≫
        DerivedCategory.Q.map ((mapHomologicalComplexIdIso C (.up ℤ)).hom.app L) := by
  have hid := NatTrans.congr_app (congrArg Iso.hom (mapDerivedCategoryIdIso_factorsh C))
    ((HomotopyCategory.quotient C (.up ℤ)).obj L)
  dsimp at hid
  simp only [Category.comp_id] at hid
  have hn := (mapDerivedCategoryIdIso C).hom.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app L)
  dsimp at hn
  rw [← cancel_epi ((𝟭 C).mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app L)),
    hn, hid, mapDerivedCategoryFactorsh_hom_app, mapHomotopyCategoryIdIso_hom_app]
  simp [mapHomotopyCategoryFactors]

/-- The commutation `H^n(-) ⋙ 𝟭 ≅ D(𝟭) ⋙ H^n(-)` of the identity functor with the homology
functors is, through `Functor.mapDerivedCategoryIdIso`, the identity. -/
@[reassoc]
lemma mapDerivedCategoryHomologyFunctorIso_id_hom_app (n : ℤ) (K : DerivedCategory C) :
    ((𝟭 C).mapDerivedCategoryHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor C n).map ((mapDerivedCategoryIdIso C).hom.app K) =
      𝟙 _ := by
  have h : ((𝟭 C).mapDerivedCategoryHomologyFunctorIso n).hom ≫
      whiskerRight (mapDerivedCategoryIdIso C).hom (DerivedCategory.homologyFunctor C n) =
      (DerivedCategory.homologyFunctor C n).rightUnitor.hom ≫
        (DerivedCategory.homologyFunctor C n).leftUnitor.inv := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun L => ?_)
    simp only [NatTrans.comp_app, whiskerRight_app, rightUnitor_hom_app, leftUnitor_inv_app]
    rw [mapDerivedCategoryHomologyFunctorIso_hom_app_Q, mapDerivedCategoryIdIso_hom_app_Q]
    have h₂ : (DerivedCategory.homologyFunctor C n).map
        (DerivedCategory.Q.map ((mapHomologicalComplexIdIso C (.up ℤ)).hom.app L)) = 𝟙 _ :=
      (congrArg _ (DerivedCategory.Q.map_id L)).trans (Functor.map_id _ _)
    simp only [Functor.map_comp, Category.assoc, Functor.id_map]
    rw [← Functor.map_comp_assoc (DerivedCategory.homologyFunctor C n)
        ((𝟭 C).mapDerivedCategoryFactors.inv.app L), Iso.inv_hom_id_app, Functor.map_id,
      Category.id_comp, h₂, mapHomologicalComplexHomologyIso_id_inv_app]
    exact ((congrArg (_ ≫ ·) ((Category.id_comp _).trans (Category.comp_id _))).trans
      (Iso.hom_inv_id_app _ L)).trans (Category.comp_id _).symm
  simpa using congr_app h K

end DerivedCategory

section LeftDerived

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open MonoidalCategory

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [MonoidalCategory C₁] [MonoidalPreadditive C₁] [HasCountableCoproducts C₁]
  [HasColimitsOfShape ℤ C₁] [HasExactColimitsOfShape ℤ C₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).obj X)]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁]

/-- The commutation `H^n(-) ⋙ F ≅ L(F) ⋙ H^n(-)` of the left derived functor of an exact
functor with the homology functors is natural in the functor: it is compatible with an
isomorphism `e : F ≅ G` and the induced isomorphism `L(F) ≅ L(G)`. -/
@[reassoc]
lemma leftDerivedFunctorHomologyFunctorIso_naturality {F G : C₁ ⥤ C₂} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (n : ℤ)
    (K : DerivedCategory C₁) :
    e.hom.app ((DerivedCategory.homologyFunctor C₁ n).obj K) ≫
        (G.leftDerivedFunctorHomologyFunctorIso n).hom.app K =
      (F.leftDerivedFunctorHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor C₂ n).map ((F.leftDerivedFunctorNatIso e).hom.app K) := by
  simp only [leftDerivedFunctorHomologyFunctorIso, leftDerivedFunctorNatIso, Iso.trans_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  rw [mapDerivedCategoryHomologyFunctorIso_hom_app_naturality_assoc,
    ← Functor.map_comp_assoc _ (F.leftDerivedFunctorIsoMapDerivedCategory.inv.app K),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]

/-- The commutation `H^n(-) ⋙ I ≅ L(I) ⋙ H^n(-)` of the left derived functor of an exact
functor `I` with the homology functors is, through the isomorphism `L(I) ≅ 𝟭` induced by
`ι : I ≅ 𝟭`, the isomorphism `ι` itself. -/
lemma leftDerivedFunctorHomologyFunctorIso_idIso {I : C₁ ⥤ C₁} [I.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I] (ι : I ≅ 𝟭 C₁) (n : ℤ)
    (K : DerivedCategory C₁) :
    (I.leftDerivedFunctorHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor C₁ n).map ((leftDerivedFunctorIdIso ι).hom.app K) =
      ι.hom.app ((DerivedCategory.homologyFunctor C₁ n).obj K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp]
  rw [← leftDerivedFunctorHomologyFunctorIso_naturality_assoc]
  simp only [leftDerivedFunctorHomologyFunctorIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp_assoc _
      ((𝟭 C₁).leftDerivedFunctorIsoMapDerivedCategory.inv.app K),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    mapDerivedCategoryHomologyFunctorIso_id_hom_app]
  exact Category.comp_id _

section FlatTwo

variable [MonoidalCategory C₂] [MonoidalPreadditive C₂] [HasCountableCoproducts C₂]
  [HasColimitsOfShape ℤ C₂] [HasExactColimitsOfShape ℤ C₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₂), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).obj X)]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₂]

/-- The commutation `H^n(-) ⋙ (F ⋙ G) ≅ L(F ⋙ G) ⋙ H^n(-)` of the left derived functor of a
composite of exact functors with the homology functors is, through the composition isomorphism
`L(F ⋙ G) ≅ L(F) ⋙ L(G)`, the composite of the commutations for `F` and for `G`. -/
@[reassoc]
lemma leftDerivedFunctorHomologyFunctorIso_comp (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (n : ℤ) (K : DerivedCategory C₁) :
    ((F ⋙ G).leftDerivedFunctorHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor C₃ n).map ((F.leftDerivedFunctorCompIso G).hom.app K) =
      G.map ((F.leftDerivedFunctorHomologyFunctorIso n).hom.app K) ≫
        (G.leftDerivedFunctorHomologyFunctorIso n).hom.app (F.leftDerivedFunctor.obj K) := by
  have hG : G.map ((DerivedCategory.homologyFunctor C₂ n).map
        (F.leftDerivedFunctorIsoMapDerivedCategory.inv.app K)) ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.app (F.leftDerivedFunctor.obj K) =
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.app (F.mapDerivedCategory.obj K) ≫
        (DerivedCategory.homologyFunctor C₃ n).map
          (G.mapDerivedCategory.map (F.leftDerivedFunctorIsoMapDerivedCategory.inv.app K)) :=
    (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality _
  simp only [leftDerivedFunctorHomologyFunctorIso, leftDerivedFunctorCompIso, Iso.trans_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app,
    whiskerLeft_app, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _
      ((F ⋙ G).leftDerivedFunctorIsoMapDerivedCategory.inv.app K),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    mapDerivedCategoryHomologyFunctorIso_comp_hom_app_assoc, reassoc_of% hG]

/-- The commutation `H^n(-) ⋙ A ≅ L(A) ⋙ H^n(-)` is compatible with the isomorphism
`L(A) ≅ L(B) ⋙ L(B')` induced by an isomorphism `e : A ≅ B ⋙ B'` of exact functors. -/
lemma leftDerivedFunctorHomologyFunctorIso_factorIso {A : C₁ ⥤ C₃} {B : C₁ ⥤ C₂}
    {B' : C₂ ⥤ C₃} [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [B'.Additive] [PreservesFiniteLimits B'] [PreservesFiniteColimits B'] (e : A ≅ B ⋙ B')
    (n : ℤ) (K : DerivedCategory C₁) :
    (A.leftDerivedFunctorHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor C₃ n).map ((leftDerivedFunctorFactorIso e).hom.app K) =
      e.hom.app ((DerivedCategory.homologyFunctor C₁ n).obj K) ≫
        B'.map ((B.leftDerivedFunctorHomologyFunctorIso n).hom.app K) ≫
          (B'.leftDerivedFunctorHomologyFunctorIso n).hom.app (B.leftDerivedFunctor.obj K) := by
  rw [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
    ← leftDerivedFunctorHomologyFunctorIso_naturality_assoc,
    leftDerivedFunctorHomologyFunctorIso_comp]

end FlatTwo

end LeftDerived

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open scoped CategoryTheory.Functor CategoryTheory.Obj

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}}

/-- The commutation `H^n(-) ⋙ f^* ≅ L(f^*) ⋙ H^n(-)` of the derived pullback of module objects
over `Λ` with the homology functors. -/
noncomputable abbrev leftDerivedUpperStarHomologyIso (f : X ⟶ Y) (n : ℤ) :
    DerivedCategory.homologyFunctor _ n ⋙ (f)^*⟦Λ⟧ ≅
      L((f)^*⟦Λ⟧) ⋙ DerivedCategory.homologyFunctor _ n :=
  (f)^*⟦Λ⟧.leftDerivedFunctorHomologyFunctorIso n

/-- The commutation of the derived pullbacks of module objects with the homology functors is
compatible with the composition isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` and
`(f ≫ g)^* ≅ g^* ⋙ f^*`. -/
lemma leftDerivedUpperStarHomologyIso_comp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (leftDerivedUpperStarHomologyIso Λ (f ≫ g) n).hom.app M ≫
        (DerivedCategory.homologyFunctor _ n).map ((leftDerivedUpperStarComp Λ f g).hom.app M) =
      (upperStarComp Λ f g).hom.app ((DerivedCategory.homologyFunctor _ n).obj M) ≫
        (f)^*⟦Λ⟧.map ((leftDerivedUpperStarHomologyIso Λ g n).hom.app M) ≫
          (leftDerivedUpperStarHomologyIso Λ f n).hom.app (L((g)^*⟦Λ⟧).obj M) := by
  rw [leftDerivedUpperStarComp_eq_leftDerivedFunctorFactorIso]
  exact Functor.leftDerivedFunctorHomologyFunctorIso_factorIso (upperStarComp Λ f g) n M

/-- The commutation of the derived pullback along `f : X ⟶ X` with the homology functors is,
through the isomorphism `L(f^*) ≅ 𝟭` induced by an isomorphism `κ : f^* ≅ 𝟭`, the
isomorphism `κ` itself. -/
lemma leftDerivedUpperStarHomologyIso_hom_app_idIso (f : X ⟶ X) (κ : (f)^*⟦Λ⟧ ≅ 𝟭 _) (n : ℤ)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (leftDerivedUpperStarHomologyIso Λ f n).hom.app M ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((Functor.leftDerivedFunctorIdIso κ).hom.app M) =
      κ.hom.app ((DerivedCategory.homologyFunctor _ n).obj M) :=
  Functor.leftDerivedFunctorHomologyFunctorIso_idIso κ n M

/-- The commutation of the derived pullback along `𝟙 X` with the homology functors is, through
the identity isomorphism `L(𝟙 X)^* ≅ 𝟭`, the identity isomorphism `(𝟙 X)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarHomologyIso_hom_app_id (X : Scheme.{u}) (n : ℤ)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (leftDerivedUpperStarHomologyIso Λ (𝟙 X) n).hom.app M ≫
        (DerivedCategory.homologyFunctor _ n).map ((leftDerivedUpperStarId Λ X).hom.app M) =
      (upperStarId Λ X).hom.app ((DerivedCategory.homologyFunctor _ n).obj M) :=
  leftDerivedUpperStarHomologyIso_hom_app_idIso Λ (𝟙 X) (upperStarId Λ X) n M

end AlgebraicGeometry.ProEtale.CondensedRing
