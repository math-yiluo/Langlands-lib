/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PrincipalIntrinsicCompletion.PrincipalIntrinsicCompletion
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.Scalar.IntegralScalarUnitNormalization
import all WeilConjectures.DeligneLaumon.FiniteReductionTower.FiniteReductionScalarNormalization
import all WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralReductionKoszulModel
import all WeilConjectures.DeligneLaumon.QuotientTensorScalarTowerComparison

/-! # Koszul quotient comparisons preserve units

Source: the finite-free quotient resolution in the first paragraph of the current
blueprint `lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 06YY, 08J7 and 07A6.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses)
namespace WeilConjectures.IntegralHom
attribute [local implicit_reducible] completedIntegralCoefficientSheaf

open CategoryTheory.MonoidalCategory
attribute [local instance 20000] abSheafify abLocallyBijective
attribute [local instance] countableColimits
  ordinaryTensorZero ordinaryTensorObjZero

attribute [local implicit_reducible] homComplex totalTensor coefficientTotalTensor
  evaluate projection homComplexπ SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.Functor.map₂HomologicalComplex
  SheafOfModules.monoidalCategory principalAugmentation principalReduction
  principalQuotient principalKoszul principalKoszulScalarComplex principalKoszulTower
attribute [local irreducible] homComplexFunctor completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard derivedInternalHomOfUniverses

private theorem koszul_inclusion_quotient
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (a : (SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)).sections)
    (n : ℕ) :
    CochainComplex.mappingCone.inr (principalKoszulScalarComplex R a n) ≫
        principalAugmentation R a n =
      (CochainComplex.singleFunctor (Modules.{t, u} Y R) 0).map
        (cokernel.π (endoPow (globalSectionMultiplication R a) (n + 1))) := by
  let F := CochainComplex.singleFunctor (Modules.{t, u} Y R) 0
  let a' := endoPow (globalSectionMultiplication R a) (n + 1)
  let S : ShortComplex (CochainComplex (Modules.{t, u} Y R) ℤ) :=
    ShortComplex.mk (F.map a') (F.map (cokernel.π a')) (by
      rw [← F.map_comp, cokernel.condition, F.map_zero])
  change CochainComplex.mappingCone.inr (principalKoszulScalarComplex R a n) ≫
    CochainComplex.mappingCone.descShortComplex S = F.map (cokernel.π a')
  exact CochainComplex.mappingCone.inr_descShortComplex S

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCommRingSheaf CategoryTheory.sheafCompose
  PrincipalKoszulStrictReplacement.tensorWith PrincipalKoszulStrictReplacement.sourceTower
  PrincipalKoszulStrictReplacement.residue
  IntegralOnSlice.Site IntegralOnSlice.siteCategory IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring IntegralOnSlice.finite IntegralOnSlice.projection
  IntegralOnSlice.level IntegralOnSlice.tower
  SheafOfModules.restrictScalars completedIntegralCommRingProjectionUnrestricted
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  SheafOfModules.KFlatTotalTensorModel.tensor SheafOfModules.KFlatTotalTensorModel.monoidal

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence tensorScalarLevelIso
  FiniteReductionTower.scalarTowerIso

private theorem map_comp_with_sides
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y Z : C} {W V : D} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (u : W ⟶ F.obj X) (v : F.obj Z ⟶ V) (e : f ≫ g = h) :
    u ≫ F.map f ≫ F.map g ≫ v = u ≫ F.map h ≫ v := by
  rw [← F.map_comp_assoc, e]

private theorem koszul_unit_scalar
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (P : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ) (n : ℕ) :
    PrincipalIntrinsicCompletion.levelUnit l E Y P n ≫
        (PrincipalKoszulStrictReplacement.comparison l E Y P).app (op n) ≫
        (FiniteReductionTower.scalarTowerIso l E Y P).hom.app (op n) =
      unrestrictedTowerUnit l E Y P n := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let F := CochainComplex.singleFunctor (PrincipalKoszulStrictReplacement.Modules l E Y) 0
  have hc : CochainComplex.mappingCone.inr (principalKoszulScalarComplex R
      (PrincipalKoszulStrictReplacement.uniformizer l E Y) n) ≫
        PrincipalKoszulStrictReplacement.augmentation l E Y n =
      F.map (PrincipalKoszulStrictReplacement.projection l E Y n) := by
    dsimp only [PrincipalKoszulStrictReplacement.augmentation]
    rw [← Category.assoc, koszul_inclusion_quotient]
    change F.map _ ≫ F.map _ = _
    rw [← F.map_comp]
    congr 1
    exact cokernel.π_desc _ _ _
  change CochainComplex.mappingCone.inr
    ((CochainComplex.singleFunctor (PrincipalKoszulStrictReplacement.Modules l E Y) 0).map
      (PrincipalKoszulStrictReplacement.multiplication l E Y n)) ≫
        PrincipalKoszulStrictReplacement.augmentation l E Y n = _ at hc
  rw [FiniteReductionTower.scalarTowerIso_hom_app]
  dsimp only [PrincipalIntrinsicCompletion.levelUnit,
    PrincipalKoszulStrictReplacement.comparison, NatTrans.ofOpSequence]
  rw [Category.assoc]
  change (PrincipalIntrinsicCompletion.tensorUnit l E Y P).inv ≫
    (PrincipalKoszulStrictReplacement.tensorWith l E Y P).map _ ≫
    (PrincipalKoszulStrictReplacement.tensorWith l E Y P).map _ ≫
      (tensorScalarLevelIso l E Y n P).hom = _
  exact (map_comp_with_sides (PrincipalKoszulStrictReplacement.tensorWith l E Y P)
    _ _ _ (PrincipalIntrinsicCompletion.tensorUnit l E Y P).inv
    (tensorScalarLevelIso l E Y n P).hom hc).trans
      ((tensorScalarLevelIso_unit l E Y n P).trans
        (integralScalarAugmentation_eq_unrestrictedUnit l E Y P n))

private theorem scalarReductionTowerIso_hom_app
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) (n : ℕᵒᵖ) :
    (scalarReductionTowerIso l E Y D hl P).hom.app n =
      (by
        exact DerivedCategory.Q.map
          ((FiniteReductionTower.scalarTowerIso l E Y P).hom.app n)) := by
  dsimp only [scalarReductionTowerIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    NatIso.ofComponents_hom_app, Iso.refl_hom]
  exact Category.comp_id _

attribute [local irreducible] scalarReductionTowerIso

/-- On a K-flat representative the strict Koszul comparison preserves quotient units.

Source: the finite-free quotient resolution in paragraph 1 of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 06YY and 07A6
(blueprint: lem-sf-integral-koszul-quotient-units).

Proof: the cone inclusion followed by its quotient augmentation is the degree-zero
quotient map, by `mappingCone.inr_descShortComplex` and `cokernel.π_desc`.
Tensor this identity with P. The pure-tensor formula for scalar normalization
identifies its composite with the actual scalar-extension unit. Tensoring the
Koszul augmentation with K-flat P is a quasi-isomorphism, so its localization
and the scalar tower isomorphism give the desired isomorphism. Mapping the
unit identity through localization proves compatibility at every level.
This uses exponent n+1 and applies without boundedness of P, including P=0. -/
theorem integralReductionTower_koszul_quotient_units
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheaf l E Y D hl) P) :
    ∃ r : PrincipalKoszulStrictReplacement.sourceTower l E Y P ⋙ DerivedCategory.Q ≅
        integralReductionTower l E Y D hl P,
      ∀ n : ℕ,
        DerivedCategory.Q.map (PrincipalIntrinsicCompletion.levelUnit l E Y P n) ≫
            r.hom.app (op n) =
          DerivedCategory.Q.map (integralTowerUnit l E Y D hl P n) := by
  let b := Functor.whiskerRight
    (PrincipalKoszulStrictReplacement.comparison l E Y P) DerivedCategory.Q
  have hb : IsIso b := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    have := koszul_augmentation_tensor_quasiIso l E Y P hP n.unop
    change IsIso (DerivedCategory.Q.map
      ((PrincipalKoszulStrictReplacement.comparison l E Y P).app n))
    infer_instance
  refine ⟨asIso b ≪≫ scalarReductionTowerIso l E Y D hl P, ?_⟩
  intro n
  dsimp only [Iso.trans_hom, asIso_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [scalarReductionTowerIso_hom_app]
  rw [integralTowerUnit_eq]
  change DerivedCategory.Q.map (PrincipalIntrinsicCompletion.levelUnit l E Y P n) ≫
    DerivedCategory.Q.map ((PrincipalKoszulStrictReplacement.comparison l E Y P).app
      (op n)) ≫ DerivedCategory.Q.map
      ((FiniteReductionTower.scalarTowerIso l E Y P).hom.app (op n)) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (koszul_unit_scalar l E Y P n)

end WeilConjectures.IntegralHom
