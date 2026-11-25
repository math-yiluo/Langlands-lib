/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalOfIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFac

/-!
# The derived (Pull) isomorphism is monoidal, for an arbitrary coefficient change

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat, write
`T = L(Ext_a) = Λ' ⊗ᴸ_Λ -` for the derived extensions of scalars and let `f : X ⟶ Y` be a
morphism of schemes. The derived (Pull) isomorphism
`Lf^* ⋙ T ≅ T ⋙ Lf^*` (`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso`) is compatible
with the tensor comparisons of the derived pullbacks (`leftDerivedUpperStarTensor`) and of the
derived extensions of scalars (`derivedExtendScalarsTensorIso`)
(`ProEtale.CondensedRing.comparisonCompatible_derivedUpperStarExtendScalarsIso`). This is the
analogue without flatness of `ProEtale.CondensedRing.comparisonCompatible_derivedPullIso`.

The proof applies
`CategoryTheory.Functor.map_leftDerivedTensorComparison_comp_eq_of_counit_of_iso`:
through the counits of the left derived functors, `derivedUpperStarExtendScalarsIso a f` is the
underived (Pull) isomorphism (`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIsoFac`),
which is monoidal (`ProEtale.CondensedRing.isMonoidal_pullIso_hom`), and
`L(Ext_{a_Y}) ⋙ Lf^* ≅ L(Ext_{a_Y} ⋙ f^*)` is compatible with the counits.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Functor

/-- The morphism `mapHomotopyCategoryCommIsoHom c e` induced on the homotopy categories by an
isomorphism `e : P ⋙ H ≅ H' ⋙ P'` is, componentwise, `NatTrans.mapHomotopyCategory e.hom`. -/
lemma mapHomotopyCategoryCommIsoHom_app {J : Type*} (c : ComplexShape J)
    {A A' B B' : Type*} [Category* A] [Category* A']
    [Category* B] [Category* B'] [Preadditive A] [Preadditive A'] [Preadditive B]
    [Preadditive B'] {P : A ⥤ A'} {H : A' ⥤ B'} {H' : A ⥤ B} {P' : B ⥤ B'} [P.Additive]
    [H.Additive] [H'.Additive] [P'.Additive] (e : P ⋙ H ≅ H' ⋙ P')
    (K : HomotopyCategory A c) :
    (mapHomotopyCategoryCommIsoHom c e).app K =
      (NatTrans.mapHomotopyCategory e.hom c).app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rw [mapHomotopyCategoryCommIsoHom, NatTrans.comp_app,
    mapHomotopyCategoryCompIso_hom_app_quotient_obj,
    mapHomotopyCategoryCompIso_inv_app_quotient_obj, ← Functor.map_comp]
  refine congrArg _ ?_
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    mapHomologicalComplexCompIso_hom_app_f, mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv,
    NatTrans.id_app]
  exact Category.comp_id _

end CategoryTheory.Functor

namespace CategoryTheory

/-- Transport a counit factorization across a naturality square of isomorphisms. -/
private lemma inv_comp_counit_of_iso_naturality {C : Type*} [Category* C]
    {A B B' D D' E Z : C} (e : A ≅ B) (d : B ≅ B') (d' : D ≅ D')
    {ε : A ⟶ Z} {m : B ⟶ D} {m' : B' ⟶ D'} {c : D ⟶ E} {c' : D' ⟶ E} {q : E ⟶ Z}
    (h₁ : e.hom ≫ m ≫ c ≫ q = ε) (h₂ : m ≫ d'.hom = d.hom ≫ m')
    (h₃ : d'.hom ≫ c' = c) :
    (d.inv ≫ e.inv) ≫ ε = m' ≫ c' ≫ q := by
  rw [← h₁]
  simp only [Category.assoc, e.inv_hom_id_assoc]
  rw [← h₃]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, d.inv_hom_id_assoc]

namespace Adjunction

/-- Reverse a tensor comparison square after identifying its chosen comparison maps. -/
private lemma comparisonCompatible_symm_of_composite_eq
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
    {F : D ⥤ C} {F' : D' ⥤ C'} {N_D : D ⥤ D'} {N_C : C ⥤ C'}
    (α : F ⋙ N_C ≅ N_D ⋙ F')
    (φ ψ : (Functor.postcompose₂.obj F).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (φ' ψ' : (Functor.postcompose₂.obj F').obj (curriedTensor D') ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj (curriedTensor C'))
    (m_C : (Functor.postcompose₂.obj N_C).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ C').obj N_C).obj N_C).obj (curriedTensor C'))
    (m_D : (Functor.postcompose₂.obj N_D).obj (curriedTensor D) ≅
      (((Functor.whiskeringLeft₂ D').obj N_D).obj N_D).obj (curriedTensor D'))
    (hφ : φ = ψ) (hφ' : φ' = ψ')
    (h : ∀ K M, F'.map ((m_D.hom.app K).app M) ≫
        (ψ'.app (N_D.obj K)).app (N_D.obj M) =
      α.inv.app (K ⊗ M) ≫ N_C.map ((ψ.app K).app M) ≫
        (m_C.hom.app (F.obj K)).app (F.obj M) ≫ (α.hom.app K ⊗ₘ α.hom.app M)) :
    ComparisonCompatible α.symm φ φ' m_C m_D := by
  subst ψ ψ'
  intro K M
  simp only [Iso.symm_inv, Iso.symm_hom, curriedTensor_obj_obj,
    curriedTensor_map_app, curriedTensor_obj_map]
  rw [reassoc_of% (h K M), Iso.hom_inv_id_app_assoc, ← MonoidalCategory.tensorHom_def,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app]
  erw [MonoidalCategory.id_tensorHom_id, Category.comp_id]

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The left derived functor of the composite `Ext_{a_Y} ⋙ f^*_Λ'` is the composite of the left
derived functors: `L(Ext_{a_Y} ⋙ f^*_Λ') ≅ L(Ext_{a_Y}) ⋙ Lf^*_Λ'`, the pullback being exact. -/
noncomputable def leftDerivedExtendScalarsUpperStarCompIso :
    (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧).leftDerivedFunctor ≅
      L(Mod.extendScalars (coefficientMap a Y)) ⋙ L((f)^*⟦Λ'⟧) :=
  Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso
      (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧ ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ' f).symm

/-- `L(Ext_{a_Y} ⋙ f^*_Λ') ≅ L(Ext_{a_Y}) ⋙ Lf^*_Λ'` is compatible with the counits. -/
lemma leftDerivedExtendScalarsUpperStarCompIso_inv_app_comp_counit
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (.up ℤ)) :
    (leftDerivedExtendScalarsUpperStarCompIso a f).inv.app (DerivedCategory.Qh.obj K) ≫
        (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app K =
      L((f)^*⟦Λ'⟧).map ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K) ≫
        ((f)^*⟦Λ'⟧).leftDerivedFunctorCounit.app
          (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.extendScalars (coefficientMap a Y) ⋙ (f)^*⟦Λ'⟧)) (.up ℤ)).hom.app K) := by
  have h₁ := Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso_hom_app_comp_counit
    (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧ K
  have h₂ := (leftDerivedUpperStarIsoMapDerivedCategory Λ' f).inv.naturality
    ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit.app K)
  have h₃ := leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_counit f Λ'
    (((Mod.extendScalars (coefficientMap a Y)).mapHomotopyCategory (.up ℤ)).obj K)
  exact inv_comp_counit_of_iso_naturality
    ((Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso
      (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧).app (DerivedCategory.Qh.obj K))
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ' f).symm.app _)
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ' f).symm.app _) h₁ h₂ h₃

/-- **(Pull) is monoidal**: for an arbitrary coefficient change `a`, the derived (Pull)
isomorphism `Lf^* ⋙ T ≅ T ⋙ Lf^*` is compatible with the tensor comparisons of the derived
pullbacks and of the derived extensions of scalars. -/
theorem comparisonCompatible_derivedUpperStarExtendScalarsIso :
    Adjunction.ComparisonCompatible (derivedUpperStarExtendScalarsIso a f).symm
      (leftDerivedUpperStarTensor Λ f) (leftDerivedUpperStarTensor Λ' f)
      (derivedExtendScalarsTensorIso a X) (derivedExtendScalarsTensorIso a Y) := by
  let := Mod.extendScalarsMonoidal (coefficientMap a X)
  let := Mod.extendScalarsMonoidal (coefficientMap a Y)
  have := isMonoidal_pullIso_hom a f
  refine Adjunction.comparisonCompatible_symm_of_composite_eq
    (derivedUpperStarExtendScalarsIso a f) _ _ _ _ _ _
    (leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison Λ f)
    (leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison Λ' f) ?_
  intro K M
  exact Functor.map_leftDerivedTensorComparison_comp_eq_of_counit_of_iso
    (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧ (f)^*⟦Λ⟧
    (Mod.extendScalars (coefficientMap a X)) (pullIso a f)
    (derivedUpperStarExtendScalarsIso a f) (leftDerivedExtendScalarsUpperStarCompIso a f).inv
    (fun K ↦ (derivedUpperStarExtendScalarsIsoFac a f K).trans
      (congrArg (fun t ↦ _ ≫ _ ≫ DerivedCategory.Qh.map t)
        (Functor.mapHomotopyCategoryCommIsoHom_app (.up ℤ) (pullIso a f) K)))
    (leftDerivedExtendScalarsUpperStarCompIso_inv_app_comp_counit a f) K M

end AlgebraicGeometry.ProEtale.CondensedRing
