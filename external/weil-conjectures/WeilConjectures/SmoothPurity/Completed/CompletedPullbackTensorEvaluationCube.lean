/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationModelDiagonal
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationPasting
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Categorical evaluation tensor cube transport

This is the abstract transport step for the representative evaluation square.
Source: Stacks 07A4, Tags 0941 and 03D2.
(blueprint: lem-pur-completed-pullback-tensor-evaluation-cube-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  sfIntrinsicPullback coefficientSequenceEvaluation
  pullbackTensorSequenceInverse pullbackTensorSystemComparison
  pullbackTensorInverseEvaluationComplex finitePullbackTensorConstruction
  coefficientTotalTensor DerivedCategory.Q DerivedCategory instCategoryDerivedCategory
  CochainComplex.IsKFlatIndependentCoefficients
  CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorCalculus pullbackTensorSequenceDerived
  finiteIntrinsicDerivedTensor finiteIntrinsicClosed

attribute [local instance] sfIntrinsicPullback_additive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem finite_comparison_app {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finitePullbackTensorConstructionIso l E f n).hom.app (M, N) =
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M N).hom := by
  unfold finitePullbackTensorConstructionIso finitePullbackTensorConstruction
  rfl

-- The pasted cube uses several chosen derived models with large implicit types.
/-- Transport the K-flat evaluation squares through the canonical finite comparison.
Source: Stacks, sites-cohomology.tex, Tags 07A4, 0941 and 03D2
(blueprint: lem-pur-completed-pullback-tensor-evaluation-cube-model).
Proof: evaluate the sequence pullback of the K-flat inputs and transport K-flatness
across the ordinary evaluation mate. Apply finite pullback tensor normalization to
obtain its ordinary cochain comparison. The ordinary cochain evaluation identity,
after the derived quotient, and naturality of the exact-functor factorizations give
the diagonal face of the cube. The other faces are the sequence comparison
normalization, the two supplied evaluation normalizations, and finite normalization.
Naturality pastes these faces. Cancelling the invertible tensor-model comparisons
and exact-functor factorizations gives the displayed equality.
-/
theorem completedPullbackTensor_evaluation_cube_model {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (A : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : A.val.obj (op U)),
      (c.hom.app A).val.app (op ((proEtaleBaseChange f).obj U))
        (((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1}
            (finiteCoefficientRing l E (n + 1))))).unit.app A).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app A).val.app (op U) x)
    (e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f)
    (he : ∀ A : CochainComplex (coefficientSequenceModules l E Y) ℤ,
      e.hom.app (DerivedCategory.Q.obj A) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app A) ≫
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app A) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj A)))
    (hn : CoefficientEvaluationTensorNormalization l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction)
    (hx : CoefficientEvaluationTensorNormalization l E X
      (pullbackTensorCalculus l E X).toCoefficientDerivedSystemReduction)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) Q) :
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSystemComparison l E f).hom.app (M, N)) ≫
      ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
        ((pullbackTensorSequenceDerived l E f).obj M,
          (pullbackTensorSequenceDerived l E f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (e.hom.app M)
          (e.hom.app N)) =
    e.hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M, N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M, N)) ≫
      (finitePullbackTensorConstructionIso l E f n).hom.app
      ((coefficientSequenceDerivedEvaluation l E Y n).obj M,
        (coefficientSequenceDerivedEvaluation l E Y n).obj N) := by
  intro M N
  let FC : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
      CochainComplex (coefficientSequenceModules l E X) ℤ :=
        (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
  let VC : CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
      CochainComplex (normalizedDVRModules l E Y n) ℤ :=
        (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)
  let WC : CochainComplex (coefficientSequenceModules l E X) ℤ ⥤
      CochainComplex (normalizedDVRModules l E X n) ℤ :=
        (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)
  let GC : CochainComplex (normalizedDVRModules l E Y n) ℤ ⥤
      CochainComplex (normalizedDVRModules l E X n) ℤ := (sfIntrinsicPullback
    (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ)
  let d (A : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
      WC.obj (FC.obj A) ≅ GC.obj (VC.obj A) :=
    (pullbackTensorInverseEvaluationComplex l E f n).symm.app A ≪≫
      (NatIso.mapHomologicalComplex c (.up ℤ)).app (VC.obj A)
  have hFP := pullbackTensorSequenceGood l E f P hP
  have hFQ := pullbackTensorSequenceGood l E f Q hQ
  have hVP := (coefficientTensorModelPreservation l E Y).2 P hP n
  have hVQ := (coefficientTensorModelPreservation l E Y).2 Q hQ n
  have hWFP := (coefficientTensorModelPreservation l E X).2 (FC.obj P) hFP n
  have hWFQ := (coefficientTensorModelPreservation l E X).2 (FC.obj Q) hFQ n
  have hGVP := SheafOfModules.kFlat_iso_independent
    (integralCoefficientCommRingSheaf l E X n) (d P) hWFP
  have hGVQ := SheafOfModules.kFlat_iso_independent
    (integralCoefficientCommRingSheaf l E X n) (d Q) hWFQ
  obtain ⟨k, hk, hfinite⟩ := finitePullbackTensor_kflat_normalization l E f n
    (VC.obj P) (VC.obj Q) hVP hVQ hGVP hGVQ
  have hfinite' := hfinite
  rw [← finite_comparison_app l E f n] at hfinite'
  have hdiag' := completedPullbackTensor_evaluation_model_diagonal
    l E f n c hc e he P Q k hk
  have hpaste := completedPullbackTensor_evaluation_pasting l E f n c e he hn hx P Q hP hQ
    hVP hVQ hGVP hGVQ k hfinite' hdiag'
  exact hpaste

end WeilConjectures
