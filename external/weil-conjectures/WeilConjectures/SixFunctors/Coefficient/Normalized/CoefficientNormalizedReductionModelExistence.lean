/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.CoefficientSequenceReductionAdjunction
import WeilConjectures.SixFunctors.Coefficient.CoefficientReductionModelTensor
import WeilConjectures.SixFunctors.Coefficient.CoefficientPrescribedPairTensorModels
import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedEvaluationTensorChain
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement

/-! # Existence of the normalized coefficient reduction model

Source: Stacks 06YS, 06YY, 07A4 and 0941
(blueprint: lem-coef-normalized-reduction-model-existence).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

section Projection
universe a b c v w r
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v} A] [Category.{w} B] [Category.{r} C]

private theorem unitProjection_of_counitProjection
    (L : A ⥤ B) (R : B ⥤ A) (V : B ⥤ C) (F : A ⥤ C) (G : C ⥤ A)
    (adj : L ⊣ R) (a : F ⊣ G) (e : L ⋙ V ≅ F) (π : R ⟶ V ⋙ G)
    (hπ : ∀ N, a.homEquiv _ _ (e.inv.app (R.obj N) ≫ V.map (adj.counit.app N)) =
      π.app N) (P : A) :
    adj.unit.app P ≫ π.app (L.obj P) = a.unit.app P ≫ G.map (e.inv.app P) := by
  apply (a.homEquiv P (V.obj (L.obj P))).symm.injective
  rw [← hπ, a.homEquiv_naturality_left_symm]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Equiv.symm_apply_apply, ← Category.assoc, e.inv.naturality, Category.assoc]
  change e.inv.app P ≫ V.map (L.map (adj.unit.app P)) ≫
    V.map (adj.counit.app (L.obj P)) = _
  rw [← V.map_comp, adj.left_triangle_components, V.map_id]
  exact (Category.comp_id (e.inv.app P)).trans
    ((a.homEquiv P (V.obj (L.obj P))).symm_apply_apply (e.inv.app P)).symm

end Projection

attribute [local implicit_reducible] CategoryTheory.uniformProd
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceCommRingTransition
  coefficientSequenceEvaluation coefficientSequenceHasDerived
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  coefficientTotalTensor CoefficientClosedStructure.tensor
  coefficientIntegralTensorModelIso coefficientFiniteTensorModelIso
  coefficientSystemTensorModelIso coefficientScalarTensorIso coefficientEvaluationTensorIso
  CoefficientTensorModels.iso

private theorem finiteTensor_exists (T : CoefficientDerivedSystemTensors l E W) (n : ℕ) :
    Nonempty (T.integralClosed.tensor ⋙ coefficientFiniteDerivedExtension l E W n ≅
      (coefficientFiniteDerivedExtension l E W n).prod
        (coefficientFiniteDerivedExtension l E W n) ⋙ (T.finiteClosed n).tensor) := by
  let J := Scheme.ProEt.topology W
  let (A : Sheaf J CommRingCat.{max u (t+1)}) :
      HasDerivedCategory.{max (t+2) (u+1)} (SheafOfModules.scalarModules J A) :=
    HasDerivedCategory.standard _
  obtain ⟨tc⟩ := coefficientPrescribedPairTensorComparison.{t+1, t, u, max (t+2) (u+1)}
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (coefficientActualScalarDerivedPair l E W n) T.integralClosed (T.finiteClosed n)
    T.integralTensorModel (T.finiteTensorModel n)
  exact ⟨tc.iso⟩

private theorem evaluationTensor_exists (T : CoefficientDerivedSystemTensors l E W) (n : ℕ) :
    Nonempty (T.systemClosed.tensor ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      (coefficientSequenceDerivedEvaluation l E W n).prod
        (coefficientSequenceDerivedEvaluation l E W n) ⋙ (T.finiteClosed n).tensor) := by
  let A := coefficientSequenceModules l E W
  let J := Scheme.ProEt.topology W
  let Rs := coefficientSequenceCommRingSheaf l E W
  let PR : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  obtain ⟨b, _⟩ := coefficientNormalizedEvaluationTensorChain l E W n
  let F := coefficientSequenceEvaluation l E W n
  let B := normalizedDVRModules l E W n
  let PS : ObjectProperty (CochainComplex B ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) (DerivedCategory B)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  obtain ⟨μ, _, _⟩ := tensorComparisonDescent DerivedCategory.Q DerivedCategory.Q
    (F.mapHomologicalComplex (.up ℤ)) (coefficientSequenceDerivedEvaluation l E W n)
    F.mapDerivedCategoryFactors.hom PR PS
    (fun P hP ↦ (coefficientTensorModelPreservation l E W).2 P hP n) ff'
    (coefficientTotalTensor.{u, t+1, t} (coefficientSequenceTopology J) Rs)
    (coefficientTotalTensor.{u, t+1, t} J (integralCoefficientCommRingSheaf l E W n))
    T.systemClosed.tensor (T.finiteClosed n).tensor
    T.systemTensorModel.comparison (T.finiteTensorModel n).comparison b
    (fun _ _ ↦ by infer_instance) (fun _ _ _ _ ↦ by infer_instance)
  exact ⟨μ⟩

/--
The sequence projection and scalar-extension construction yields a reduction record
whose tensor presentation is the prescribed one.  The construction uses the normalized
sequence projection adjunction, its finite scalar evaluations, and the actual K-flat
change-of-rings models; the tensor fields are retained definitionally from `T`.
Source: Stacks 06YS, 06YY, 07A4 and 0941.
(blueprint: lem-coef-normalized-reduction-model-existence)
-/
theorem coefficientNormalizedReductionModel_exists
    (T : CoefficientDerivedSystemTensors l E W) :
    ∃ R : CoefficientDerivedSystemReduction l E W,
      R.toCoefficientDerivedSystemTensors = T := by
  classical
  obtain ⟨L, adj, ρ, hmodel, hnorm, hcounit⟩ :=
    coefficientSequenceReductionAdjunction_exists l E W
  obtain ⟨μ⟩ := coefficientReductionModelTensor_exists l E W T L adj ρ hmodel
  let R : CoefficientDerivedSystemReduction l E W :=
    { toCoefficientDerivedSystemReductionModel :=
        { toCoefficientDerivedSystemTensors := T
          reduction := L
          adjunction := adj
          reductionEvaluation := ρ
          reductionModel := hmodel
          reduction_normalized := hnorm }
      unit_projection := fun P n ↦ unitProjection_of_counitProjection L
        (coefficientSequenceLimit l E W) (coefficientSequenceDerivedEvaluation l E W n)
        (coefficientFiniteDerivedExtension l E W n) (coefficientFiniteDerivedRestriction l E W n)
        adj (coefficientFiniteAdjunction l E W n) (ρ n)
        (coefficientSequenceProjection l E W n) (fun N ↦ hcounit N n) P
      counit_projection := hcounit
      reductionTensor := μ
      finiteTensor := fun n ↦ (finiteTensor_exists l E W T n).some
      evaluationTensor := fun n ↦ (evaluationTensor_exists l E W T n).some }
  exact ⟨R, rfl⟩

end WeilConjectures
