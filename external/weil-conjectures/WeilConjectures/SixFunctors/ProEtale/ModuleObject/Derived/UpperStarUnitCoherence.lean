/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-!
# The coherence isomorphisms of the derived pullbacks at the unit

Let `Λ` be a commutative condensed ring. The derived pullback `Lf^*` of module objects over `Λ`
is strong monoidal (`ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`), with unit
comparison `ε_f : Λ_X ≅ Lf^* Λ_Y`, and so is its restriction to bounded constructible complexes
(`ProEtale.CondensedRing.monoidal_boundedConstructibleUpperStar`). This file shows that the
identity isomorphism `L(𝟙 X)^* ≅ 𝟭` and the composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` are compatible with the unit comparisons, that is, are monoidal at the
unit:
```
L(𝟙 X)^* Λ_X ≅ Λ_X  is  ε_{𝟙 X}⁻¹,
L(f ≫ g)^* Λ_Z ≅ Lf^* Lg^* Λ_Z ≅ Lf^* Λ_Y ≅ Λ_X  is  ε_{f ≫ g}⁻¹.
```
Consequently the identity isomorphism `R(𝟙 X)_* ≅ 𝟭` of the pushforward is, at the unit, the
unit of `L(𝟙 X)^* ⊣ R(𝟙 X)_*` followed by `R(𝟙 X)_* ε_{𝟙 X}⁻¹`.

All the derived isomorphisms involved are determined by their compatibility with the counits of
the left derived functors of the exact pullbacks, and on the unit `Λ[0]` the unit comparisons are
induced by those of the underived pullbacks. The statements thus reduce to the underived ones,
`ProEtale.CondensedRing.upperStarId_hom_app_unit` and
`ProEtale.CondensedRing.upperStarComp_hom_app_unit`, through the compatibilities of
`CategoryTheory.Functor.mapHomotopyCategorySingleHom` with transformations of additive functors.

## Main definitions

- `CategoryTheory.Functor.mapHomotopyCategorySingleHom`: the morphism `F(A[0]) ⟶ B[0]` of the
  homotopy category induced by a morphism `F A ⟶ B`.

## Main results

- `ProEtale.CondensedRing.leftDerivedUpperStarId_hom_app_unit`,
  `ProEtale.CondensedRing.leftDerivedUpperStarComp_hom_app_unit`: the statements for the derived
  pullbacks on `D(Mod_{Λ_X})`.
- `ProEtale.CondensedRing.boundedConstructibleUpperStarId_hom_app_unit`,
  `ProEtale.CondensedRing.boundedConstructibleUpperStarComp_hom_app_unit`: the statements on
  bounded constructible complexes.
- `ProEtale.CondensedRing.boundedConstructibleLowerStarId_inv_app_unit`: the identity isomorphism
  of the pushforward at the unit.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Functor

/-! ### Morphisms out of complexes concentrated in degree `0` -/

section Homotopy

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject C₃]

/-- The morphism `F(A[0]) ⟶ B[0]` of the homotopy category induced by a morphism
`φ : F A ⟶ B`, for an additive functor `F`: the identification `F(A[0]) ≅ (F A)[0]` followed by
`φ[0]`. -/
noncomputable def mapHomotopyCategorySingleHom (F : C₁ ⥤ C₂) [F.Additive] {A : C₁} {B : C₂}
    (φ : F.obj A ⟶ B) :
    (F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient C₁ (.up ℤ)).obj
        ((HomologicalComplex.single C₁ (.up ℤ) 0).obj A)) ⟶
      (HomotopyCategory.quotient C₂ (.up ℤ)).obj ((HomologicalComplex.single C₂ (.up ℤ) 0).obj B) :=
  (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app _ ≫ (HomotopyCategory.quotient _ _).map
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app A ≫
      (HomologicalComplex.single C₂ (.up ℤ) 0).map φ)

omit [HasZeroObject C₁] [HasZeroObject C₂] in
/-- The comparison `K(C₁) ⥤ K(C₂)` of `F.mapHomotopyCategory` with the quotient functors is the
identity. -/
lemma mapHomotopyCategoryFactors_hom_app_eq_id (F : C₁ ⥤ C₂) [F.Additive]
    (K : CochainComplex C₁ ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := by
  simp [Functor.mapHomotopyCategoryFactors]
  rfl

omit [HasZeroObject C₁] [HasZeroObject C₂] in
lemma mapHomotopyCategory_map_quotient_map (F : C₁ ⥤ C₂) [F.Additive]
    {K L : CochainComplex C₁ ℤ} (g : K ⟶ L) :
    (F.mapHomotopyCategory (.up ℤ)).map ((HomotopyCategory.quotient C₁ (.up ℤ)).map g) =
      (HomotopyCategory.quotient C₂ (.up ℤ)).map ((F.mapHomologicalComplex (.up ℤ)).map g) :=
  rfl

omit [HasZeroObject C₁] [HasZeroObject C₂] in
lemma natTransMapHomotopyCategory_app_quotient_obj {F G : C₁ ⥤ C₂} [F.Additive] [G.Additive]
    (τ : F ⟶ G) (K : CochainComplex C₁ ℤ) :
    (NatTrans.mapHomotopyCategory τ (.up ℤ)).app ((HomotopyCategory.quotient C₁ (.up ℤ)).obj K) =
      (HomotopyCategory.quotient C₂ (.up ℤ)).map ((NatTrans.mapHomologicalComplex τ _).app K) :=
  rfl

/-- A transformation `τ : I ⟶ 𝟭` of additive functors induces, on `A[0]`, the morphism
`I(A[0]) ⟶ A[0]` induced by `τ_A`. -/
lemma mapHomotopyCategorySingleHom_id {I : C₁ ⥤ C₁} [I.Additive] (τ : I ⟶ 𝟭 C₁) (A : C₁) :
    (NatTrans.mapHomotopyCategory τ (.up ℤ)).app ((HomotopyCategory.quotient C₁ (.up ℤ)).obj
        ((HomologicalComplex.single C₁ (.up ℤ) 0).obj A)) ≫
      (mapHomotopyCategoryIdIso C₁ (.up ℤ)).hom.app _ =
    mapHomotopyCategorySingleHom I (τ.app A) := by
  rw [mapHomotopyCategoryIdIso_hom_app_eq_id]
  erw [Category.comp_id]
  rw [mapHomotopyCategorySingleHom, mapHomotopyCategoryFactors_hom_app_eq_id]
  erw [Category.id_comp, natTransMapHomotopyCategory_app_quotient_obj]
  congr 1
  ext n
  by_cases hn : n = 0
  · subst hn
    simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
    have h := τ.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom
    simp only [Functor.id_map] at h
    erw [reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
  · exact (I.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)).eq_of_src _ _

/-- A transformation `τ : F ⟶ G ⋙ H` of additive functors is compatible with the morphisms
`G(A[0]) ⟶ B[0]` and `H(B[0]) ⟶ D[0]` induced by `φ : G A ⟶ B` and `ψ : H B ⟶ D`: their
composite with `τ` is the morphism `F(A[0]) ⟶ D[0]` induced by `τ_A ≫ H φ ≫ ψ`. -/
lemma mapHomotopyCategorySingleHom_comp {F : C₁ ⥤ C₃} {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₃}
    [F.Additive] [G.Additive] [H.Additive] (τ : F ⟶ G ⋙ H) {A : C₁} {B : C₂} {D : C₃}
    (φ : G.obj A ⟶ B) (ψ : H.obj B ⟶ D) :
    (NatTrans.mapHomotopyCategory τ (.up ℤ)).app ((HomotopyCategory.quotient C₁ (.up ℤ)).obj
        ((HomologicalComplex.single C₁ (.up ℤ) 0).obj A)) ≫
      (H.mapHomotopyCategory (.up ℤ)).map (mapHomotopyCategorySingleHom G φ) ≫
        mapHomotopyCategorySingleHom H ψ =
    mapHomotopyCategorySingleHom F (τ.app A ≫ H.map φ ≫ ψ) := by
  simp only [mapHomotopyCategorySingleHom, mapHomotopyCategoryFactors_hom_app_eq_id]
  erw [Category.id_comp, Category.id_comp, Category.id_comp,
    natTransMapHomotopyCategory_app_quotient_obj, mapHomotopyCategory_map_quotient_map,
    ← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  by_cases hn : n = 0
  · subst hn
    simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc,
      Functor.map_comp]
    have h := τ.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom
    simp only [Functor.comp_map] at h
    erw [reassoc_of% h]
    rw [← H.map_comp_assoc (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj A)).inv,
      Iso.inv_hom_id, H.map_id, Category.id_comp,
      ← H.map_comp_assoc (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv, Iso.inv_hom_id,
      H.map_id, Category.id_comp]
  · exact (F.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)).eq_of_src _ _

end Homotopy

section Derived

open _root_.DerivedCategory

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
  [MonoidalCategory C₂] [MonoidalPreadditive C₂] [HasCountableCoproducts C₂]
  [HasColimitsOfShape ℤ C₂] [HasExactColimitsOfShape ℤ C₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₂), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).obj X)]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₂]

/-- The composition comparison of exact derived functors respects morphisms out of complexes
concentrated in degree `0`, after composing with the derived counits. -/
private lemma leftDerivedFunctorFactorIso_hom_app_single
    {F : C₁ ⥤ C₃} {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₃}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G ⋙ H) {A : C₁} {B : C₂} {D : C₃}
    (φ : G.obj A ⟶ B) (ψ : H.obj B ⟶ D) :
    (leftDerivedFunctorFactorIso e).hom.app
        (Qh.obj ((HomotopyCategory.quotient C₁ (.up ℤ)).obj
          ((HomologicalComplex.single C₁ (.up ℤ) 0).obj A))) ≫
      H.leftDerivedFunctor.map (G.leftDerivedFunctorCounit.app _ ≫
        Qh.map (mapHomotopyCategorySingleHom G φ)) ≫
      (H.leftDerivedFunctorCounit.app _ ≫ Qh.map (mapHomotopyCategorySingleHom H ψ)) =
    F.leftDerivedFunctorCounit.app _ ≫
      Qh.map (mapHomotopyCategorySingleHom F (e.hom.app A ≫ H.map φ ≫ ψ)) := by
  rw [← mapHomotopyCategorySingleHom_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% (leftDerivedFunctorCounit_naturality
    (A := H) (mapHomotopyCategorySingleHom G φ)),
    reassoc_of% (leftDerivedFunctorFactorIso_hom_app_comp_counit e _)]

end Derived

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme DerivedCategory

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The derived pullbacks on `D(Mod_{Λ_X})` -/

/-- The unit comparison `Lf^* Λ_Y ≅ Λ_X` is the counit of the left derived functor followed by
the morphism induced in degree `0` by the inverse of the unit comparison of `f^*`. -/
lemma leftDerivedUpperStarUnitIso_hom_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (leftDerivedUpperStarUnitIso Λ f).hom =
      (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (𝟙_ _) ≫
        Qh.map (Functor.mapHomotopyCategorySingleHom (f)^*⟦Λ⟧
          (Functor.Monoidal.εIso (f)^*⟦Λ⟧).inv) :=
  rfl

/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback of module objects is, at the
unit, the unit comparison `L(𝟙 X)^* Λ_X ≅ Λ_X`. -/
lemma leftDerivedUpperStarId_hom_app_unit (X : Scheme.{u}) :
    (leftDerivedUpperStarId Λ X).hom.app (𝟙_ _) = (leftDerivedUpperStarUnitIso Λ (𝟙 X)).hom := by
  rw [leftDerivedUpperStarUnitIso_hom_eq, ← upperStarId_hom_app_unit,
    ← Functor.mapHomotopyCategorySingleHom_id]
  exact Functor.leftDerivedFunctorIdIso_hom_app_Qh_obj (upperStarId Λ X) (𝟙_ _)

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of the derived pullbacks of module
objects is compatible with the unit comparisons. -/
lemma leftDerivedUpperStarComp_hom_app_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (leftDerivedUpperStarComp Λ f g).hom.app (𝟙_ _) ≫
        L((f)^*⟦Λ⟧).map (leftDerivedUpperStarUnitIso Λ g).hom ≫
          (leftDerivedUpperStarUnitIso Λ f).hom =
      (leftDerivedUpperStarUnitIso Λ (f ≫ g)).hom := by
  have h := Functor.leftDerivedFunctorFactorIso_hom_app_single (upperStarComp Λ f g)
    (Functor.Monoidal.εIso (g)^*⟦Λ⟧).inv (Functor.Monoidal.εIso (f)^*⟦Λ⟧).inv
  simp only [upperStarComp_hom_app_unit,
    ← leftDerivedUpperStarComp_eq_leftDerivedFunctorFactorIso] at h
  exact h

/-! ### Bounded constructible complexes -/

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- On the ambient derived category, the inverse of the unit comparison of the derived pullback
on bounded constructible complexes is `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso`. -/
lemma boundedConstructibleUpperStar_εIso_inv_hom (f : X ⟶ Y) :
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        f)).inv.hom =
      (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) f.left).hom :=
  rfl

variable (X) in
/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback on bounded constructible
complexes is, at the unit, the inverse of the unit comparison `ε : Λ_X ≅ L(𝟙 X)^* Λ_X`. -/
lemma boundedConstructibleUpperStarId_hom_app_unit :
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom.app (𝟙_ _) =
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙
          X))).inv := by
  ext1
  rw [boundedConstructibleUpperStarId_hom_app_hom, boundedConstructibleUpperStar_εIso_inv_hom]
  exact leftDerivedUpperStarId_hom_app_unit (Profinite.padicAlgClRingObj ℓ) X.left

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] in
private lemma leftDerivedUpperStarUnitIso_hom_comp_left (f : X ⟶ Y) (g : Y ⟶ Z) :
    (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) (f ≫ g).left).hom =
      (leftDerivedUpperStarUnitIso (Profinite.padicAlgClRingObj ℓ) (f.left ≫ g.left)).hom :=
  rfl

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [IsSeparated Z.hom] in
private lemma leftDerivedUpperStarComp_hom_app_unit_obj (f : X ⟶ Y) (g : Y ⟶ Z) :
    (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left).hom.app (𝟙_
        Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj =
      (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left).hom.app (𝟙_ _) :=
  rfl

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of the derived pullbacks on bounded
constructible complexes is compatible with the unit comparisons:
`L(f ≫ g)^* Λ_Z ≅ Lf^* Lg^* Λ_Z ≅ Lf^* Λ_Y ≅ Λ_X` is the inverse of the unit comparison of
`L(f ≫ g)^*`. -/
lemma boundedConstructibleUpperStarComp_hom_app_unit (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f g).hom.app (𝟙_ _) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
              g)).inv ≫
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            f)).inv =
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f ≫
          g))).inv := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStarComp_hom_app_hom,
    boundedConstructibleUpperStar_map_hom, boundedConstructibleUpperStar_εIso_inv_hom]
  exact (congrArg (· ≫ _) (leftDerivedUpperStarComp_hom_app_unit_obj ℓ f g)).trans
    ((leftDerivedUpperStarComp_hom_app_unit (Profinite.padicAlgClRingObj ℓ) f.left g.left).trans
      (leftDerivedUpperStarUnitIso_hom_comp_left ℓ f g).symm)

variable (X) in
/-- The identity isomorphism `R(𝟙 X)_* ≅ 𝟭` of the derived pushforward on bounded constructible
complexes is, at the unit, the unit of `L(𝟙 X)^* ⊣ R(𝟙 X)_*` followed by the inverse of the unit
comparison of `L(𝟙 X)^*`. -/
lemma boundedConstructibleLowerStarId_inv_app_unit :
    (boundedConstructibleLowerStarId ℓ X).inv.app (𝟙_ _) =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X)).unit.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ (𝟙 X)).map
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙
              X))).inv := by
  have h := homEquiv_comp_conjugateEquiv_app Adjunction.id
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X))
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).hom (𝟙 (𝟙_ _))
  erw [Adjunction.id_homEquiv_apply, Category.id_comp, Category.comp_id] at h
  rw [boundedConstructibleUpperStarId_hom_app_unit, Adjunction.homEquiv_unit] at h
  rw [boundedConstructibleLowerStarId, conjugateIsoEquiv_apply_inv, Iso.symm_inv]
  exact h

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
