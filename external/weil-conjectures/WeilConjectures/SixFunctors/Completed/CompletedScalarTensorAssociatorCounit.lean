/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantCompletedOrdinaryAssociativity
import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
import WeilConjectures.SmoothPurity.PurStrictScalar.CompletedScalarAssociatorLocalization

/-! # The scalar associator on computation counits

Source: Stacks Tags 06YY and 07A6.
(blueprint: lem-sf-completed-scalar-associator-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.completedCoefficientMap
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  WeilConjectures.completedScalarComparison
  WeilConjectures.completedScalarChangeData
attribute [local irreducible] CategoryTheory.sheafCompose CategoryTheory.presheafToSheaf
  CategoryTheory.Functor.leftAdjoint SheafOfModules.changeOfRings
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
section
variable (l : ℕ) [Fact l.Prime]
  (E L M : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (T : Scheme.{u})
open CategoryTheory.Limits
section
attribute [local semireducible] HasDerivedCategory.standard

private theorem pbc_counit_eq (P : CochainComplex (integralTowerModules l E T) ℤ) :
    pbcComplexCounit (completedCoefficientMap l E L i T) P =
      completedScalarCounit l E L i T P := by
  dsimp only [pbcComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors]
  erw [(pbcDerivedExtend (completedCoefficientMap l E L i T)).map_id,
    DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id]
  rfl
end

private theorem exact_associator_factors
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (J : A ⥤ C)
    [F.Additive] [G.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (e : F ⋙ G ≅ J) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj P) ≫
      J.mapDerivedCategoryFactors.hom.app P =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_Q_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
  congr 3
  ext n
  simp [Functor.mapHomologicalComplexCompIso]

private theorem model_naturality
    {A B : Type*} [Category A] [Category B]
    (G G' : A ⥤ B) (e : G ≅ G') {X Y Z : A} {W : B}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : G'.obj Z ⟶ W) :
    G.map a ≫ e.hom.app Y ≫ G'.map b ≫ c =
      G.map (a ≫ b) ≫ e.hom.app Z ≫ c := by
  rw [← Category.assoc (e.hom.app Y), ← e.hom.naturality b]
  simp only [Functor.map_comp, Category.assoc]

private theorem scalar_counit_isIso
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    IsIso (completedScalarCounit l E L i T P) := by
  have := (PurStrictScalar.completedTensor_exact l E L i T).1
  have := (PurStrictScalar.completedTensor_exact l E L i T).2
  rw [← pbc_counit_eq l E L i T P]
  rw [← PurStrictScalar.completedTensorModel_counit l E L i T P]
  infer_instance

/-- The scalar tensor associator preserves the successive computation counits.
Source: Stacks 06YY (lemma-derived-base-change) and 07A6 (lemma-adjoint).
(blueprint: lem-sf-completed-scalar-associator-counit).
Proof: express the associator through the three counit-normalized exact models.
The exact derived-composition factorization identifies its cochain representative.
Naturality moves the middle model comparison past the first factor map.
The three model-counit equations then give the successive-counit formula. -/
theorem completedScalarTensorAssociatorCounit
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (PurCompactSupport.tensorComposition _ _ _
      (PurCompactSupport.completedMap_composition l E L i M j T)).hom.app
        (DerivedCategory.Q.obj P) ≫
      pbcComplexCounit (completedCoefficientMap l E M (j.comp i) T) P =
    (pbcDerivedExtend (completedCoefficientMap l L M j T)).map
      (pbcComplexCounit (completedCoefficientMap l E L i T) P) ≫
    pbcComplexCounit (completedCoefficientMap l L M j T)
      (((pbcExtend (completedCoefficientMap l E L i T)).mapHomologicalComplex (.up ℤ)).obj P)
      ≫ DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (PurStrictScalar.ordinaryScalarAssociator _ _ _
            (PurCompactSupport.completedMap_composition l E L i M j T)) (.up ℤ)).hom.app P) := by
  let F := pbcExtend (completedCoefficientMap l E L i T)
  let G := pbcExtend (completedCoefficientMap l L M j T)
  let J := pbcExtend (completedCoefficientMap l E M (j.comp i) T)
  have := (PurStrictScalar.completedTensor_exact l E L i T).1
  have := (PurStrictScalar.completedTensor_exact l E L i T).2
  have := (PurStrictScalar.completedTensor_exact l L M j T).1
  have := (PurStrictScalar.completedTensor_exact l L M j T).2
  have := (PurStrictScalar.completedTensor_exact l E M (j.comp i) T).1
  have := (PurStrictScalar.completedTensor_exact l E M (j.comp i) T).2
  let e := PurStrictScalar.ordinaryScalarAssociator _ _ _
    (PurCompactSupport.completedMap_composition l E L i M j T)
  have hc := PurStrictScalar.completedTensorModel_composition l E L i M j T
    (DerivedCategory.Q.obj P)
  rw [← PurStrictScalar.completedTensorModel_counit l E M (j.comp i) T P]
  rw [← Category.assoc, hc]
  simp only [Category.assoc]
  rw [exact_associator_factors F G J e P]
  rw [model_naturality]
  erw [reassoc_of% (PurStrictScalar.completedTensorModel_counit l L M j T
    ((F.mapHomologicalComplex (.up ℤ)).obj P))]
  erw [PurStrictScalar.completedTensorModel_counit l E L i T]

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian in
private theorem completed_associator_counit
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (PurCompactSupport.tensorComposition _ _ _
      (PurCompactSupport.completedMap_composition l E L i M j T)).hom.app
        (DerivedCategory.Q.obj P) ≫
      completedScalarCounit l E M (j.comp i) T P =
    (completedDerivedScalarExtension l L M j T).map
      (completedScalarCounit l E L i T P) ≫
    completedScalarCounit l L M j T ((completedOrdinaryScalarComplex l E L i T).obj P) ≫
      DerivedCategory.Q.map
        ((CompletedLineTensor.scalarAssociatorComplex l E T L i M j
          (PurStrictScalar.ordinaryScalarAssociator _ _ _
            (PurCompactSupport.completedMap_composition l E L i M j T))).hom.app P) := by
  have hc := completedScalarTensorAssociatorCounit l E L M i j T P
  rw [pbc_counit_eq l E M (j.comp i) T,
    pbc_counit_eq l E L i T, pbc_counit_eq l L M j T] at hc
  exact hc

end
end WeilConjectures
