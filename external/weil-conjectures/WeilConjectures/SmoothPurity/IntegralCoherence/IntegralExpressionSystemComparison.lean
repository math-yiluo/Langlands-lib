/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralCoherenceData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorCoherence
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
/-! # Recursive strict-to-derived expression comparison

Source: Stacks 07A4 and 0941. The comparison is constructed recursively from
cochain tensor models and exact-localization factors, before completion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] SheafOfModules.monoidalCategory
universe t u s i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Opposite AlgebraicGeometry
namespace WeilConjectures.IntegralCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} {W : S → Scheme.{t}}
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal

private theorem good_pull {a b : S} (f : W a ⟶ W b)
    (P : Complex l E (W b)) (hP : Good l E (W := W) b P) :
    Good l E (W := W) a ((pull l E f).obj P) := by
  obtain ⟨A, TA, _⟩ := ringedDerived_closed_symmetric_monoidal.{t + 1, t, u,
    (max u (t + 1)) + 1} (coefficientSequenceTopology (Scheme.ProEt.topology (W b)))
      (coefficientSequenceCommRingSheaf l E (W b))
  obtain ⟨B, TB, _⟩ := ringedDerived_closed_symmetric_monoidal.{t + 1, t, u,
    (max u (t + 1)) + 1} (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
      (coefficientSequenceCommRingSheaf l E (W a))
  obtain ⟨K, hK, _⟩ := AmbientPullbackTensor.tensorData_existsUnique l E f none A B TA TB
  exact hK.2.2.2 P hP

private theorem good_tensor {a : S} (P Q : Complex l E (W a))
    (hP : Good l E (W := W) a P) (hQ : Good l E (W := W) a Q) :
    Good l E (W := W) a (P ⊗ Q) := by
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (coefficientSequenceCommRingSheaf l E (W a)) P Q hP.1 hQ.1 hP.2 hQ.2
  exact ⟨h.1, h.2.1⟩

private theorem good_unit (M : CompletedOperations.Models l E W) (a : S) :
    Good l E (W := W) a (𝟙_ (Complex l E (W a))) := by
  refine ⟨(by with_unfolding_all exact (M.system a).unitKFlat), ?_⟩
  intro n
  let R := coefficientSequenceCommRingSheaf l E (W a)
  let J := coefficientSequenceTopology (Scheme.ProEt.topology (W a))
  by_cases hn : n = 0
  · subst n
    have h : ObjectProperty.flat (𝟙_ (coefficientSequenceModules l E (W a))) :=
      ObjectProperty.flat_of_tensorIso
        (leftUnitor (𝟙_ (coefficientSequenceModules l E (W a))))
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2
  · have hz := HomologicalComplex.isZero_single_obj_X (V := coefficientSequenceModules l E (W a))
      (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) n hn
    have hz' : IsZero ((𝟙_ (Complex l E (W a))).X n) := by
      with_unfolding_all exact hz
    have h : ObjectProperty.flat ((𝟙_ (Complex l E (W a))).X n) :=
      ObjectProperty.flat_of_isZero hz'
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2

/-- Tensor and inverse image preserve flat-term K-flat strict expression models.
Source: Stacks 07A4 and 0G7E
(blueprint: stage3-pur-integral-expression-system-comparison). -/
theorem goodExpression (M : CompletedOperations.Models l E W)
    {I : Type i} {location : I → S} (N : ∀ k : I, Complex l E (W (location k)))
    (hN : ∀ k, Good l E (W := W) (location k) (N k))
    {a : S} (P : CompletedOperations.Expression W location a) :
    Good l E (W := W) a (value l E N P) := by
  induction P with
  | input k => exact hN k
  | unit a => exact good_unit l E M a
  | tensor P Q hp hq => exact good_tensor l E _ _ hp hq
  | pullback f P hp => exact good_pull l E f _ hp

/-- The specified recursive comparison, formed before any derived inverse limit.
Source: Stacks 07A4 and 0941
(blueprint: stage3-pur-integral-expression-system-comparison). -/
def systemComparison (M : CompletedOperations.Models l E W)
    {I : Type i} {location : I → S} (N : ∀ k : I, Complex l E (W (location k)))
    (hN : ∀ k, Good l E (W := W) (location k) (N k))
    {a : S} (P : CompletedOperations.Expression W location a) :
    DerivedCategory.Q.obj (value l E N P) ≅
      (CompletedOperations.systemValue l E M P).obj (fun k ↦ DerivedCategory.Q.obj (N k)) :=
  match P with
  | .input k => Iso.refl _
  | .unit a => by with_unfolding_all exact Iso.refl (CompletedOperations.unit l E (W := W) a)
  | .tensor P Q =>
      CoefficientTensorModels.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
        (coefficientSequenceCommRingSheaf l E (W a)) (M.system a).closed (M.system a).models
        (value l E N P) (value l E N Q)
        (goodExpression l E M N hN P).1 (goodExpression l E M N hN Q).1 ≪≫
      (CompletedOperations.tensor l E M a).mapIso
        (Iso.prod (systemComparison M N hN P) (systemComparison M N hN Q))
  | .pullback f P =>
      ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app
        (value l E N P)).symm ≪≫
      (integralComparisonDerivedSequencePullback l E f).mapIso (systemComparison M N hN P)

end WeilConjectures.IntegralCoherence
