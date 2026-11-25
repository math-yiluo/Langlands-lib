/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedTensorDescentData
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedTensorDescentData
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # Completion of the fixed calculus tensor

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

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
private theorem tensorCompletion_ofDescent (W : Scheme.{u})
    (a : IntegralAmbient.DescendedCompletion (tensorLocalization l E W) (C l E W) (eta l E W)
      (tensorRepresentativeDescent l E W) (IntegralOnSlice.completionComparison l E W none)
      (tensorRoosDescent l E W) (integralCompletedTensorComparison l E W)
      (fun P ↦ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E W none P.obj))) :
    IsTensorCompletion l E W (integralRingedOrdinaryTensor l E W)
      (TensorCompletionConstruction.flat_good l E W) a.comparison
      (TensorCompletionConstruction.quotientChain l E W) := by
  intro P Q hP hQ
  let p : (integralOperationsGoodComplex l E W).FullSubcategory :=
    ⟨P, TensorCompletionConstruction.flat_good l E W P hP⟩
  let q : (integralOperationsGoodComplex l E W).FullSubcategory :=
    ⟨Q, TensorCompletionConstruction.flat_good l E W Q hQ⟩
  have h := a.augmentation (p, q)
  have hh := normalizeAugmentation
    ((tensorRepresentativeDescent l E W).app (p, q)).symm _ _ _ rfl h
  have he := (Iso.inv_eq_inv ((tensorRepresentativeDescent l E W).app (p, q))
    ((integralRingedOrdinaryTensor l E W).representative.app
      (⟨P, hP⟩, ⟨Q, hQ⟩)).symm).mpr
        (tensorRepresentativeDescent_app l E W P Q hP hQ)
  refine (congrArg (fun z ↦ z ≫ (eta l E W).app
    ((integralRingedOrdinaryTensor l E W).tensor.obj ((tensorLocalization l E W).obj (p, q))) ≫
    a.comparison.hom.app ((tensorLocalization l E W).obj (p, q)) ≫
    (integralCompletedTensorComparison l E W).hom.app (p, q)) he.symm).trans ?_
  refine hh.trans ?_
  dsimp only [tensorGoodTotal, IntegralOnSlice.totalTensorOnGood,
    ObjectProperty.lift, Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj]
  erw [tensorRoosDescent_app l E W p q]
  exact tensorChain_derived l E W P Q

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- The quotient completion comparison for the fixed calculus tensor, including its
representative augmentation equation. This concerns tensor alone, on one scheme.
Source: Stacks 07A4, 0941, 099N; fix-prop-coherence, tensor-model step
(blueprint: lem-sf-integral-ringed-tensor-completion).

Proof: restrict the calculus's K-flat tensor presentation to flat-term K-flat pairs.
The quotient Roos augmentation of their ordinary total tensor has first coordinate
x tensor y sent to (1 tensor x) tensor (1 tensor y), and zero shifted coordinate.
The strict tensor-tower isomorphism identifies its target with the published tensor
operation complex. On the product of the good-complex localizations, completion of
the ordinary tensor and the published completed tensor therefore have naturally
isomorphic presentations. Fully faithful whiskering by that product localization
descends the comparison and its inverse. The descent equation, precomposed with
the ordinary representative comparison, is IsTensorCompletion. All maps use the
same signed total tensor and quotient tower; zero inputs and empty schemes require
no change. No constructibility, quasi-compactness or invertibility of l on W is used. -/
theorem integralRingedTensorCompletion (W : Scheme.{u}) :
    ∃ β : (integralRingedOrdinaryTensor l E W).tensor ⋙ C l E W ≅
        integralCompletedTensor l E W,
      IsTensorCompletion l E W (integralRingedOrdinaryTensor l E W)
        (TensorCompletionConstruction.flat_good l E W) β
        (TensorCompletionConstruction.quotientChain l E W) := by
  exact ⟨(tensorDescent l E W).comparison,
    tensorCompletion_ofDescent l E W (tensorDescent l E W)⟩

end WeilConjectures.IntegralSystemRealization
