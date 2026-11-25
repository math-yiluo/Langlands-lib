/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SixFunctors.OpenFactorCoherence.TensorCompletionConstruction.TensorQuotientChainData
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Fixed calculus tensor and descent data

Source: Stacks 07A4, 0941, 099N; fix-prop-coherence, quotient tensor realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open OpenFactorCoherence

attribute [local irreducible] IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  integralOperationsRoos integralOperationsRoosMap IntegralOnSlice.tower
  integralOperationsTensorTowerFunctor HasDerivedCategory.standard

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
/-- The calculus tensor with its own representative comparison, restricted to flat terms.
Source: Stacks 07A4 (blueprint: def-sf-integral-ringed-tensor-descent-data). -/
def integralRingedOrdinaryTensor (W : Scheme.{u}) :
    ProEtaleTensorModel W ((PurCompactSupport.completed l E).ring W) where
  tensor := (calculus l E W).integralClosed.tensor
  representative := by
    let i := ObjectProperty.ιOfLE (fun P hP ↦
      (TensorCompletionConstruction.flat_good l E W P hP).1)
    exact Functor.isoWhiskerLeft (i.prod i) (calculus l E W).integralTensorModel.comparison

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
private theorem normalizeAugmentation {K : Type*} [Category* K]
    {A B D : K} (r : A ≅ B) (e : B ⟶ A) (x : B ⟶ D) (y : A ⟶ D)
    (he : e = r.inv) (h : x = e ≫ y) : r.hom ≫ x = y := by
  rw [h, he, ← Category.assoc, r.hom_inv_id, Category.id_comp]

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
private abbrev tensorTotal (W : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
private abbrev tensorLocalization (W : Scheme.{u}) :=
  (integralOperationsGoodLocalization l E W).prod
    (integralOperationsGoodLocalization l E W)

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
private abbrev tensorGoodTotal (W : Scheme.{u}) := IntegralOnSlice.totalTensorOnGood l E W

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
@[irreducible] private def tensorRepresentativeDescent (W : Scheme.{u}) :
    tensorLocalization l E W ⋙ (integralRingedOrdinaryTensor l E W).tensor ≅
      tensorGoodTotal l E W ⋙ IntegralOnSlice.qGood l E W none := by
  let i := ObjectProperty.ιOfLE
    (fun P (hP : integralOperationsGoodComplex l E W P) ↦ hP.1)
  with_unfolding_all
    exact (Functor.isoWhiskerLeft (i.prod i)
      (calculus l E W).integralTensorModel.comparison).symm

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
private theorem tensorRepresentativeDescent_app (W : Scheme.{u})
    (P Q : Cx l E W)
    (hP : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W) P)
    (hQ : proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W) Q) :
    (tensorRepresentativeDescent l E W).hom.app
        (⟨P, TensorCompletionConstruction.flat_good l E W P hP⟩,
          ⟨Q, TensorCompletionConstruction.flat_good l E W Q hQ⟩) =
      (integralRingedOrdinaryTensor l E W).representative.inv.app (⟨P, hP⟩, ⟨Q, hQ⟩) := by
  unfold tensorRepresentativeDescent
  rfl

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
@[irreducible] private def tensorRoosDescent (W : Scheme.{u}) :
    tensorGoodTotal l E W ⋙ IntegralOnSlice.roosGood l E W none ≅
      integralOperationsTensorOnGood l E W := by
  let G := integralOperationsGoodComplex l E W
  let R : (ℕᵒᵖ ⥤ Cx l E W) ⥤ Cx l E W := integralOperationsRoosFunctor
  let Qd : Cx l E W ⥤ Integral l E W := DerivedCategory.Q
  with_unfolding_all
    exact IntegralAmbient.liftedTowerRoosComparison
      (IntegralOnSlice.Good l E W none) (G.ι.prod G.ι)
      (tensorTotal l E W)
      (fun P ↦ IntegralOnSlice.totalTensorGood l E W P.1 P.2)
      (IntegralOnSlice.tower l E W none) (integralOperationsTensorTowerFunctor l E W)
      R Qd (IntegralAmbient.tensorTowerIso l E W)

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
private theorem tensorRoosDescent_app (W : Scheme.{u})
    (p q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (tensorRoosDescent l E W).hom.app (p, q) =
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map
        ((IntegralAmbient.tensorTowerIso l E W).hom.app (p.obj, q.obj))) := by
  let G := integralOperationsGoodComplex l E W
  let R : (ℕᵒᵖ ⥤ Cx l E W) ⥤ Cx l E W := integralOperationsRoosFunctor
  let Qd : Cx l E W ⥤ Integral l E W := DerivedCategory.Q
  have h := IntegralAmbient.liftedTowerRoosComparison_app
    (IntegralOnSlice.Good l E W none) (G.ι.prod G.ι) (tensorTotal l E W)
    (fun P ↦ IntegralOnSlice.totalTensorGood l E W P.1 P.2)
    (IntegralOnSlice.tower l E W none) (integralOperationsTensorTowerFunctor l E W)
    R Qd (IntegralAmbient.tensorTowerIso l E W) (p, q)
  unfold tensorRoosDescent
  exact h

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
@[irreducible] private def tensorDescent (W : Scheme.{u}) :
    IntegralAmbient.DescendedCompletion (tensorLocalization l E W) (C l E W) (eta l E W)
      (tensorRepresentativeDescent l E W) (IntegralOnSlice.completionComparison l E W none)
      (tensorRoosDescent l E W) (integralCompletedTensorComparison l E W)
      (fun P ↦ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E W none P.obj)) :=
  IntegralAmbient.descendCompletion (tensorLocalization l E W)
    (Classical.choice (good_prod_whisker_fullyFaithful l E W (Integral l E W)))
    (C l E W) (eta l E W) (tensorRepresentativeDescent l E W)
    (IntegralOnSlice.completionComparison l E W none) (tensorRoosDescent l E W)
    (integralCompletedTensorComparison l E W)
    (fun P ↦ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E W none P.obj))
    (IntegralOnSlice.completionUnit_existsUnique l E W none).exists.choose_spec

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
private theorem tensorChain_derived (W : Scheme.{u}) (P Q : Cx l E W) :
    DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E W none
        ((tensorTotal l E W).obj (P, Q))) ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map
        ((IntegralAmbient.tensorTowerIso l E W).hom.app (P, Q))) =
      DerivedCategory.Q.map ((TensorCompletionConstruction.quotientChain l E W).app (P, Q)) := by
  let qd : Cx l E W ⥤ Integral l E W := DerivedCategory.Q
  exact (qd.map_comp (IntegralOnSlice.roosUnit l E W none
    ((tensorTotal l E W).obj (P, Q)))
    (integralOperationsRoosFunctor.map
      ((IntegralAmbient.tensorTowerIso l E W).hom.app (P, Q)))).symm.trans
        (congrArg qd.map (TensorCompletionConstruction.quotientChain_app l E W P Q).symm)

end WeilConjectures.IntegralSystemRealization
