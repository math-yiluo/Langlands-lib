/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedTensorCompletion
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedPullCompletion
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedOpenBaseChange
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedClopenComparison
import WeilConjectures.SixFunctors.OpenFactorCoherence.TensorOperationUnitNormalization
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData

/-! # Canonical integral model construction steps

Source: blueprint fix-prop-coherence, strict-system realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
/-- Completed tensor/pull models and their ordinary open comparisons. The proper/open
transformation and its adjunct equation are deliberately not part of this assertion.
Source: Stacks 07A4, 099N, 03DI, 09AE and 0E8I; blueprint fix-prop-coherence,
last model-construction step of strict-system realization
(blueprint: lem-sf-integral-ringed-model-existence).

Proof: choose the canonical flat-term K-flat tensor localization, using the same
integralTensorModel representatives as calculus. The identity on pure tensors
identifies its ordinary tensor with integralClosed.tensor and identifies their
representative isomorphisms, giving tensorClosed and tensorRepresentative.
Apply the quotient Roos augmentation to the ordinary total tensor and pullback
complexes. The first coordinate is the quotient of each scalar-unit tensor and the
shifted coordinate is zero. The strict quotient tower equations and localization
therefore give precisely OpenFactorCoherence.Tensor and Pull with their recorded
normalizations. Assemble these into RingedModels. Exact open restriction is fully
faithful after extension, so its actual unit is invertible. The slice base-change
comparison is invertible for a cartesian open square, and the open projection
comparison is invertible by the extension-by-zero tensor formula. Specify their
inverses as the displayed unit/tensor adjunction transposes. For a clopen immersion,
extension by zero equals direct image; its map is the transpose under the geometric
adjunction of the inverse open unit. These constructions and equations give
RingedOpenComparisons. Empty opens, identity opens and zero tensor inputs obey the
same slice and pure-tensor formulas, with no nonempty assumption. -/
theorem integralRingedModelExistence :
    ∃ d : RingedModels l E, Nonempty (RingedOpenComparisons l E d) := by
  classical
  have ht := fun W : Scheme.{u} ↦ integralRingedTensorCompletion l E W
  choose β hβ using ht
  let t : ∀ W : Scheme.{u}, OpenFactorCoherence.Tensor l E W := fun W ↦
    { ordinary := integralRingedOrdinaryTensor l E W
      good := OpenFactorCoherence.TensorCompletionConstruction.flat_good l E W
      comparison := β W
      chain := OpenFactorCoherence.TensorCompletionConstruction.quotientChain l E W
      canonical := ⟨OpenFactorCoherence.tensorOperationUnit_normalized l E W _
        (OpenFactorCoherence.TensorCompletionConstruction.quotientChain_app l E W), hβ W⟩ }
  let d : RingedModels l E :=
    { tensor := t
      pull := fun f ↦ Classical.choice (integralRingedPullCompletion l E f)
      tensorClosed := fun _ ↦ rfl
      tensorRepresentative := by
        intro W P Q hP hQ
        dsimp only [t, integralRingedOrdinaryTensor, eqToIso_refl, Iso.refl_hom,
          Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
        with_unfolding_all exact Category.comp_id _ }
  refine ⟨d, ⟨?_⟩⟩
  refine
    { unitIso := fun j _ M ↦ ?_
      beta := fun a j' j g _ _ h sq ↦ ?_
      beta_transpose := ?_
      projection := fun j _ ↦ ?_
      projection_transpose := ?_
      clopen := fun j _ _ ↦ ?_
      clopen_transpose := ?_ }
  · let := integralRingedOpenUnit_isIso l E j
    infer_instance
  · let := integralRingedOpenMate_isIso l E a j' j g h sq
    exact (asIso (integralRingedOpenMate l E a j' j g h)).symm
  · intro U' U X' X a j' j g hj hj' h sq M
    exact ((ringedOpenAdj l E j').homEquiv _ _).apply_symm_apply _
  · refine (NatIso.ofComponents
      (F := ringedTensorRight l E d j) (G := ringedTensorLeft l E d j)
      (fun MN ↦ (PurCompactSupport.openProjectionIso (PurCompactSupport.completed l E) j
        (d.tensor _).ordinary (d.tensor _).ordinary MN.1 MN.2).symm) ?_).symm
    intro MN MN' f
    exact PurCompactSupport.openProjectionInverse_naturality
      (PurCompactSupport.completed l E) j _ _ f.1 f.2
  · intro U X j hj M N
    exact ((ringedOpenAdj l E j).homEquiv _ _).apply_symm_apply _
  · let := integralRingedClopenMap_isIso l E j
    exact asIso (integralRingedClopenMap l E j)
  · intro U X j hj hc M
    let := integralRingedOpenUnit_isIso l E j
    change ((ringedAdj l E j).homEquiv _ _)
      ((inv (ringedOpenAdj l E j).unit).app M) = _
    exact congrArg ((ringedAdj l E j).homEquiv _ _)
      (NatIso.isIso_inv_app (ringedOpenAdj l E j).unit M)

end WeilConjectures.IntegralSystemRealization
