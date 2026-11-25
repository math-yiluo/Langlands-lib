/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitMate
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange

/-!
# Derived adjunctions and exact restriction functors

Let `G ⊣ F` and `G' ⊣ F'` be adjunctions of additive functors between abelian categories and
let `P₁`, `P₂` be exact functors ("restrictions of scalars") with isomorphisms
`e : P₁ ⋙ G ≅ G' ⋙ P₂` and `k : F' ⋙ P₁ ≅ P₂ ⋙ F` compatible with the units. We show that the
induced isomorphism `D(P₂) ⋙ RF ≅ RF' ⋙ D(P₁)` of right derived functors is the mate of the
induced isomorphism of the derived left adjoints, both for the derived adjunction
`LG ⊣ RF` (`CategoryTheory.Adjunction.mateEquiv_derivedAdjunction_restrict`) and, for exact
`G`, for the adjunction `D(G) ⊣ RF`
(`CategoryTheory.Adjunction.mateEquiv_mapDerivedCategoryRightDerivedAdjunction_restrict`).

This is the input for the compatibility of the derived base change map with the restriction of
scalars along a morphism of coefficient rings.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory

section HomotopyCategory

variable {V₁ V₂ W₁ W₂ : Type*} [Category V₁] [Category V₂] [Category W₁] [Category W₂]
  [Preadditive V₁] [Preadditive V₂] [Preadditive W₁] [Preadditive W₂]
  {F₁ : V₁ ⥤ V₂} {F₂ : V₂ ⥤ W₂} {G₁ : V₁ ⥤ W₁} {G₂ : W₁ ⥤ W₂}
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]

/-- The square of functors between homotopy categories induced by a square
`F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂` of additive functors. -/
noncomputable def NatTrans.mapHomotopyCategorySquare (e : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂)
    {ι : Type*} (c : ComplexShape ι) :
    F₁.mapHomotopyCategory c ⋙ F₂.mapHomotopyCategory c ⟶
      G₁.mapHomotopyCategory c ⋙ G₂.mapHomotopyCategory c :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl _) c).hom ≫
    NatTrans.mapHomotopyCategory e c ≫ (Functor.mapHomotopyCategoryCompIso (Iso.refl _) c).inv

lemma NatTrans.mapHomotopyCategorySquare_app_quotient_obj (e : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂)
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex V₁ c) :
    (NatTrans.mapHomotopyCategorySquare e c).app ((HomotopyCategory.quotient V₁ c).obj K) =
      (HomotopyCategory.quotient W₂ c).map ((NatTrans.mapHomologicalComplex e c).app K) := by
  have h₁ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) c).hom.app
      ((HomotopyCategory.quotient V₁ c).obj K) = 𝟙 _ := by
    rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  have h₂ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) c).inv.app
      ((HomotopyCategory.quotient V₁ c).obj K) = 𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) c).hom.app _),
      Iso.hom_inv_id_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app]
    simp
  simp only [NatTrans.mapHomotopyCategorySquare, NatTrans.comp_app, h₁, h₂,
    NatTrans.mapHomotopyCategory_app]
  simp
  rfl

end HomotopyCategory
section UnitSquare

variable {C₁ C₂ C₁' C₂' : Type*} [Category C₁] [Category C₂] [Category C₁'] [Category C₂']
  [Abelian C₁] [Abelian C₂] [Abelian C₁'] [Abelian C₂']
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} {G' : C₁' ⥤ C₂'} {F' : C₂' ⥤ C₁'} {P₁ : C₁' ⥤ C₁}
  {P₂ : C₂' ⥤ C₂} [G.Additive] [F.Additive] [G'.Additive] [F'.Additive] [P₁.Additive]
  [P₂.Additive]

/-- A square `e` of left adjoints and a square `k` of right adjoints compatible with the units
induce squares of the adjunctions on homotopy categories which are compatible with the
units. -/
lemma Adjunction.mapHomotopyCategory_unit_square (adj : G ⊣ F) (adj' : G' ⊣ F')
    (e : P₁ ⋙ G ⟶ G' ⋙ P₂) (k : F' ⋙ P₁ ⟶ P₂ ⋙ F)
    (h : ∀ N, P₁.map (adj'.unit.app N) ≫ k.app (G'.obj N) =
      adj.unit.app (P₁.obj N) ≫ F.map (e.app N))
    (N : HomotopyCategory C₁' (ComplexShape.up ℤ)) :
    (P₁.mapHomotopyCategory _).map ((adj'.mapHomotopyCategory _).unit.app N) ≫
        (NatTrans.mapHomotopyCategorySquare k _).app ((G'.mapHomotopyCategory _).obj N) =
      (adj.mapHomotopyCategory _).unit.app ((P₁.mapHomotopyCategory _).obj N) ≫
        (F.mapHomotopyCategory _).map ((NatTrans.mapHomotopyCategorySquare e _).app N) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective N
  have h₁ := Adjunction.mapHomotopyCategory_unit_app_quotient (ComplexShape.up ℤ) adj
    ((P₁.mapHomologicalComplex _).obj K)
  have h₂ := Adjunction.mapHomotopyCategory_unit_app_quotient (ComplexShape.up ℤ) adj' K
  have h₃ := NatTrans.mapHomotopyCategorySquare_app_quotient_obj k (ComplexShape.up ℤ)
    ((G'.mapHomologicalComplex _).obj K)
  have h₄ := NatTrans.mapHomotopyCategorySquare_app_quotient_obj e (ComplexShape.up ℤ) K
  erw [h₁, h₂, h₃, h₄]
  erw [Functor.mapHomotopyCategory_map, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  erw [← Functor.map_comp]
  congr 1
  ext n
  exact h (K.X n)

end UnitSquare
section DerivedSquare

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- On the image `Qh X` of an object of the homotopy category, the isomorphism
`D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` induced by `e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂` is the square induced by
`e` on homotopy categories, up to the comparisons `Functor.mapDerivedCategoryFactorsh`. -/
lemma Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj_comp (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (X : HomotopyCategory A (.up ℤ)) :
    (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj X) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        G₂.mapDerivedCategoryFactorsh.hom.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        F₂.mapDerivedCategoryFactorsh.hom.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategorySquare e.hom (.up ℤ)).app X) := by
  have h := mapDerivedCategorySquareIso_hom_app_Qh_obj e X
  simp only [NatTrans.mapHomotopyCategorySquare, NatTrans.comp_app]
  rw [← h]
  simp [← Functor.map_comp_assoc]

end DerivedSquare

section RightDerived

variable {C₁ C₂ C₁' C₂' : Type*} [Category C₁] [Category C₂] [Category C₁'] [Category C₂']
  [Abelian C₁] [Abelian C₂] [Abelian C₁'] [Abelian C₂']
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₁']
  [HasDerivedCategory C₂'] [HasKInjectiveResolutions C₂] [HasKInjectiveResolutions C₂']
  {F : C₂ ⥤ C₁} {F' : C₂' ⥤ C₁'} {P₁ : C₁' ⥤ C₁} {P₂ : C₂' ⥤ C₂}
  [F.Additive] [F'.Additive] [P₁.Additive] [P₂.Additive]
  [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]

/-- The isomorphism `D(P₂) ⋙ RF ≅ RF' ⋙ D(P₁)` induced by an isomorphism
`k : F' ⋙ P₁ ≅ P₂ ⋙ F` of functors with exact `P₁` and `P₂`, provided the unit of `RF` is an
isomorphism at the images under `P₂` of K-injective complexes, precomposed with the image of
the unit of `RF'`. -/
lemma Functor.map_rightDerivedFunctorUnit_app_comp_restrictIso_inv_app
    (k : F' ⋙ P₁ ≅ P₂ ⋙ F)
    (hG : ∀ (K : CochainComplex C₂' ℤ) [K.IsKInjective], IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj
        ((P₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))))
    (X : HomotopyCategory C₂' (.up ℤ)) :
    P₁.mapDerivedCategory.map (F'.rightDerivedFunctorUnit.app X) ≫
        ((mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso P₂ F hG).symm ≪≫
          rightDerivedFunctorNatIso k.symm ≪≫
          rightDerivedFunctorCompMapDerivedCategoryIso F' P₁).inv.app
          (DerivedCategory.Qh.obj X) =
      P₁.mapDerivedCategoryFactorsh.hom.app ((F'.mapHomotopyCategory (.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategorySquare k.hom (.up ℤ)).app X) ≫
        F.rightDerivedFunctorUnit.app ((P₂.mapHomotopyCategory (.up ℤ)).obj X) ≫
        F.rightDerivedFunctor.map (P₂.mapDerivedCategoryFactorsh.inv.app X) := by
  have := isRightDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor_of_isIso P₂ F hG
  have hu : (rightDerivedFunctorCompMapDerivedCategoryUnit F' P₁).app X =
      DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (F' ⋙ P₁)) (.up ℤ)).inv.app X) ≫
        P₁.mapDerivedCategoryFactorsh.inv.app ((F'.mapHomotopyCategory (.up ℤ)).obj X) ≫
        P₁.mapDerivedCategory.map (F'.rightDerivedFunctorUnit.app X) := by
    simp [rightDerivedFunctorCompMapDerivedCategoryUnit]
  have hC : (rightDerivedFunctorCompMapDerivedCategoryUnit F' P₁).app X ≫
      (rightDerivedFunctorCompMapDerivedCategoryIso F' P₁).inv.app (DerivedCategory.Qh.obj X) =
      (F' ⋙ P₁).rightDerivedFunctorUnit.app X := by
    simp [rightDerivedFunctorCompMapDerivedCategoryIso]
  have hB : (F' ⋙ P₁).rightDerivedFunctorUnit.app X ≫
      (rightDerivedFunctorNatIso k.symm).inv.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory k.hom (.up ℤ)).app X) ≫
        (P₂ ⋙ F).rightDerivedFunctorUnit.app X := by
    simp only [rightDerivedFunctorNatIso, rightDerivedFunctorNatTrans, Iso.symm_inv]
    exact rightDerivedNatTrans_app _ _ _ _ _ _ X
  have hA : (P₂ ⋙ F).rightDerivedFunctorUnit.app X ≫
      (mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso P₂ F hG).hom.app
        (DerivedCategory.Qh.obj X) =
      (mapDerivedCategoryCompRightDerivedFunctorUnit P₂ F).app X := by
    simp [mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso]
  have hv := mapDerivedCategoryCompRightDerivedFunctorUnit_app P₂ F X
  have hc : P₁.mapDerivedCategory.map (F'.rightDerivedFunctorUnit.app X) =
      P₁.mapDerivedCategoryFactorsh.hom.app ((F'.mapHomotopyCategory (.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (F' ⋙ P₁)) (.up ℤ)).hom.app X) ≫
        (rightDerivedFunctorCompMapDerivedCategoryUnit F' P₁).app X := by
    rw [hu, ← DerivedCategory.Qh.map_comp_assoc, Iso.hom_inv_id_app]
    simp
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  rw [hc]
  simp only [Category.assoc]
  rw [reassoc_of% hC, reassoc_of% hB, hA, hv]
  simp [NatTrans.mapHomotopyCategorySquare]

end RightDerived
section MateRestrict

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C₁ C₂ C₁' C₂' : Type*} [Category C₁] [Category C₂] [Category C₁'] [Category C₂']
  [Abelian C₁] [Abelian C₂] [Abelian C₁'] [Abelian C₂']
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₁']
  [HasDerivedCategory C₂'] [HasKInjectiveResolutions C₂] [HasKInjectiveResolutions C₂']
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} {G' : C₁' ⥤ C₂'} {F' : C₂' ⥤ C₁'} {P₁ : C₁' ⥤ C₁}
  {P₂ : C₂' ⥤ C₂} [G.Additive] [F.Additive] [G'.Additive] [F'.Additive] [P₁.Additive]
  [P₂.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]

/-- The unit of `RF' ⋙ D(P₁)` as a right derived functor factors through `D(P₁)` of the unit
of `RF'`. -/
lemma Functor.exists_rightDerivedFunctorCompMapDerivedCategoryUnit_app_eq
    (X : HomotopyCategory C₂' (.up ℤ)) :
    ∃ e, (rightDerivedFunctorCompMapDerivedCategoryUnit F' P₁).app X =
      e ≫ P₁.mapDerivedCategory.map (F'.rightDerivedFunctorUnit.app X) :=
  ⟨DerivedCategory.Qh.map ((mapHomotopyCategoryCompIso (Iso.refl (F' ⋙ P₁)) (.up ℤ)).inv.app X) ≫
    P₁.mapDerivedCategoryFactorsh.inv.app _,
    by simp [rightDerivedFunctorCompMapDerivedCategoryUnit]⟩

variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- **The comparison of right derived functors is the mate of the comparison of the exact left
adjoints.** Let `G ⊣ F` and `G' ⊣ F'` be adjunctions with exact left adjoints and let
`P₁`, `P₂` be exact functors with isomorphisms `e : P₁ ⋙ G ≅ G' ⋙ P₂` and
`k : F' ⋙ P₁ ≅ P₂ ⋙ F` compatible with the units. Then the isomorphism
`RF' ⋙ D(P₁) ≅ D(P₂) ⋙ RF` induced by `k` is the mate of `D(P₁) ⋙ D(G) ≅ D(G') ⋙ D(P₂)`
for the adjunctions `D(G) ⊣ RF` and `D(G') ⊣ RF'`. -/
lemma Adjunction.mateEquiv_mapDerivedCategoryRightDerivedAdjunction_restrict (adj : G ⊣ F)
    (adj' : G' ⊣ F') (e : P₁ ⋙ G ≅ G' ⋙ P₂) (k : F' ⋙ P₁ ≅ P₂ ⋙ F)
    (h : ∀ N, P₁.map (adj'.unit.app N) ≫ k.hom.app (G'.obj N) =
      adj.unit.app (P₁.obj N) ≫ F.map (e.hom.app N))
    (hG : ∀ (K : CochainComplex C₂' ℤ) [K.IsKInjective], IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj
        ((P₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))) :
    mateEquiv adj'.mapDerivedCategoryRightDerivedAdjunction
        adj.mapDerivedCategoryRightDerivedAdjunction (Functor.mapDerivedCategorySquareIso e).hom =
      ((Functor.mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso P₂ F hG).symm ≪≫
        Functor.rightDerivedFunctorNatIso k.symm ≪≫
        Functor.rightDerivedFunctorCompMapDerivedCategoryIso F' P₁).inv :=
  mateEquiv_eq_of_isRightDerivedFunctor (adj.mapHomotopyCategory _) (adj'.mapHomotopyCategory _)
    (NatTrans.mapHomotopyCategorySquare e.hom _) (NatTrans.mapHomotopyCategorySquare k.hom _)
    (Adjunction.mapHomotopyCategory_unit_square adj adj' e.hom k.hom h)
    adj.mapDerivedCategoryRightDerivedAdjunction adj'.mapDerivedCategoryRightDerivedAdjunction
    G.mapDerivedCategoryFactorsh.hom F.rightDerivedFunctorUnit G'.mapDerivedCategoryFactorsh.hom
    F'.rightDerivedFunctorUnit
    ((adj.mapHomotopyCategory _).derivedη_fac_app (HomotopyCategory.quasiIso C₁ (.up ℤ)) _ _)
    ((adj'.mapHomotopyCategory _).derivedε_fac_app (HomotopyCategory.quasiIso C₂' (.up ℤ)) _ _)
    P₁.mapDerivedCategoryFactorsh P₂.mapDerivedCategoryFactorsh _
    (Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj_comp e)
    (HomotopyCategory.quasiIso C₂' (.up ℤ))
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F' P₁)
    Functor.exists_rightDerivedFunctorCompMapDerivedCategoryUnit_app_eq _
    (Functor.map_rightDerivedFunctorUnit_app_comp_restrictIso_inv_app k hG)

end MateRestrict
section DerivedAdjunctionRestrict

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C₁ C₂ C₁' C₂' : Type*} [Category C₁] [Category C₂] [Category C₁'] [Category C₂']
  [Abelian C₁] [Abelian C₂] [Abelian C₁'] [Abelian C₂']
  [MonoidalCategory C₁] [MonoidalPreadditive C₁] [HasCountableCoproducts C₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₁] [HasExactColimitsOfShape ℤ C₁]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).obj X)]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁]
  [MonoidalCategory C₁'] [MonoidalPreadditive C₁'] [HasCountableCoproducts C₁']
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁'), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁'), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁'), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₁'] [HasExactColimitsOfShape ℤ C₁']
  [∀ (X : C₁'), PreservesColimitsOfShape ℤ ((curriedTensor C₁').obj X)]
  [∀ (X : C₁'), PreservesColimitsOfShape ℤ ((curriedTensor C₁').flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁']
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₁']
  [HasDerivedCategory C₂'] [HasKInjectiveResolutions C₂] [HasKInjectiveResolutions C₂']
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} {G' : C₁' ⥤ C₂'} {F' : C₂' ⥤ C₁'} {P₁ : C₁' ⥤ C₁}
  {P₂ : C₂' ⥤ C₂} [G.Additive] [F.Additive] [G'.Additive] [F'.Additive] [P₁.Additive]
  [P₂.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

omit [HasKInjectiveResolutions C₂] [HasKInjectiveResolutions C₂'] in
/-- The isomorphism `D(P₁) ⋙ LG ≅ LG' ⋙ D(P₂)` of left derived functors of exact functors
induced by `e : P₁ ⋙ G ≅ G' ⋙ P₂` is computed on the images `Qh N` of the homotopy category by
the square induced by `e`, up to the counits of the left derived functors. -/
lemma Functor.leftDerivedFunctorRestrictIso_hom_app_Qh_obj_comp (e : P₁ ⋙ G ≅ G' ⋙ P₂)
    (N : HomotopyCategory C₁' (.up ℤ)) :
    (isoWhiskerLeft P₁.mapDerivedCategory G.leftDerivedFunctorIsoMapDerivedCategory ≪≫
        mapDerivedCategorySquareIso e ≪≫
        isoWhiskerRight G'.leftDerivedFunctorIsoMapDerivedCategory.symm
          P₂.mapDerivedCategory).hom.app (DerivedCategory.Qh.obj N) ≫
        P₂.mapDerivedCategory.map (G'.leftDerivedFunctorCounit.app N) ≫
        P₂.mapDerivedCategoryFactorsh.hom.app ((G'.mapHomotopyCategory (.up ℤ)).obj N) =
      G.leftDerivedFunctor.map (P₁.mapDerivedCategoryFactorsh.hom.app N) ≫
        G.leftDerivedFunctorCounit.app ((P₁.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategorySquare e.hom (.up ℤ)).app N) := by
  have h₁ := NatTrans.congr_app G'.leftDerivedFunctorIsoMapDerivedCategory_hom_fac N
  have h₂ := NatTrans.congr_app G.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((P₁.mapHomotopyCategory (.up ℤ)).obj N)
  have h₃ := G.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (P₁.mapDerivedCategoryFactorsh.hom.app N)
  have h₄ := mapDerivedCategorySquareIso_hom_app_Qh_obj_comp e N
  simp only [NatTrans.comp_app, whiskerLeft_app] at h₁ h₂
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] at h₄
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    isoWhiskerRight_hom, whiskerRight_app, Iso.symm_hom, Category.assoc]
  rw [← h₁, ← h₂]
  simp only [Functor.map_comp, Category.assoc]
  rw [← P₂.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.map_id, Category.id_comp]
  rw [reassoc_of% h₃, h₄]
/-- **The comparison of right derived functors is the mate of the comparison of the derived
left adjoints.** Let `G ⊣ F` and `G' ⊣ F'` be adjunctions with exact left adjoints and let
`P₁`, `P₂` be exact functors with isomorphisms `e : P₁ ⋙ G ≅ G' ⋙ P₂` and
`k : F' ⋙ P₁ ≅ P₂ ⋙ F` compatible with the units. Then the isomorphism
`RF' ⋙ D(P₁) ≅ D(P₂) ⋙ RF` induced by `k` is the mate of the isomorphism
`D(P₁) ⋙ LG ≅ LG' ⋙ D(P₂)` induced by `e`, for the derived adjunctions `LG ⊣ RF` and
`LG' ⊣ RF'`. -/
lemma Adjunction.mateEquiv_derivedAdjunction_restrict (adj : G ⊣ F) (adj' : G' ⊣ F')
    (e : P₁ ⋙ G ≅ G' ⋙ P₂) (k : F' ⋙ P₁ ≅ P₂ ⋙ F)
    (h : ∀ N, P₁.map (adj'.unit.app N) ≫ k.hom.app (G'.obj N) =
      adj.unit.app (P₁.obj N) ≫ F.map (e.hom.app N))
    (hG : ∀ (K : CochainComplex C₂' ℤ) [K.IsKInjective], IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj
        ((P₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))) :
    mateEquiv adj'.derivedAdjunction adj.derivedAdjunction
        (Functor.isoWhiskerLeft P₁.mapDerivedCategory G.leftDerivedFunctorIsoMapDerivedCategory ≪≫
          Functor.mapDerivedCategorySquareIso e ≪≫
          Functor.isoWhiskerRight G'.leftDerivedFunctorIsoMapDerivedCategory.symm
            P₂.mapDerivedCategory).hom =
      ((Functor.mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso P₂ F hG).symm ≪≫
        Functor.rightDerivedFunctorNatIso k.symm ≪≫
        Functor.rightDerivedFunctorCompMapDerivedCategoryIso F' P₁).inv :=
  mateEquiv_eq_of_isRightDerivedFunctor (adj.mapHomotopyCategory _) (adj'.mapHomotopyCategory _)
    (NatTrans.mapHomotopyCategorySquare e.hom _) (NatTrans.mapHomotopyCategorySquare k.hom _)
    (Adjunction.mapHomotopyCategory_unit_square adj adj' e.hom k.hom h)
    adj.derivedAdjunction adj'.derivedAdjunction
    G.leftDerivedFunctorCounit F.rightDerivedFunctorUnit G'.leftDerivedFunctorCounit
    F'.rightDerivedFunctorUnit
    ((adj.mapHomotopyCategory _).derivedη_fac_app (HomotopyCategory.quasiIso C₁ (.up ℤ)) _ _)
    ((adj'.mapHomotopyCategory _).derivedε_fac_app (HomotopyCategory.quasiIso C₂' (.up ℤ)) _ _)
    P₁.mapDerivedCategoryFactorsh P₂.mapDerivedCategoryFactorsh _
    (Functor.leftDerivedFunctorRestrictIso_hom_app_Qh_obj_comp e)
    (HomotopyCategory.quasiIso C₂' (.up ℤ))
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F' P₁)
    Functor.exists_rightDerivedFunctorCompMapDerivedCategoryUnit_app_eq _
    (Functor.map_rightDerivedFunctorUnit_app_comp_restrictIso_inv_app k hG)

end DerivedAdjunctionRestrict

end CategoryTheory
