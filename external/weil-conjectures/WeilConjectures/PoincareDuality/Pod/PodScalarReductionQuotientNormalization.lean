/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodQuotientTransition.PodQuotientTransitionGenerators
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientModelComparison
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarCompletionQuotientPresentation

/-! # Scalar reduction on strict quotient models

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-scalar-reduction-quotient-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.integralComparisonSequenceScalarModel

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem canonicalPresentation (W : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E W)
    (D : CompletionUnit.DerivedModel l E W (podReindexCalculus l E W) M)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    let C := (M.quotient l E W).obj P.obj
    letI := D.reduction_isIso P.obj P.property.1 P.property.2
    let e := asIso (D.reductionComparison.app P.obj)
    let κ (n : ℕ) := (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P.obj
    CoefficientReductionPresentation l E W
        (podReindexCalculus l E W).toCoefficientDerivedSystemReduction
        P.obj P.property.1 C e κ ∧
      IsIntegralComparisonPresentationCoherent l E W (podReindexCalculus l E W)
        P.obj C e κ := by
  dsimp only
  have := D.reduction_isIso P.obj P.property.1 P.property.2
  constructor
  · refine ⟨?_, ?_⟩
    · intro n
      exact D.reduction_evaluation P.obj P.property.1 P.property.2 n
    · intro m n h
      apply HomologicalComplex.hom_ext
      intro i
      exact M.transition (P.obj.X i) h
  · unfold IsIntegralComparisonPresentationCoherent
    let C := (M.quotient l E W).obj P.obj
    let I := (CompletionUnit.tower l E W).obj C
    let a := (M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P.obj
    let b := (((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E W)).mapHomologicalComplex
      (.up ℤ)).homEquiv P.obj I).symm a
    refine ⟨b, ?_, ?_⟩
    · intro n i U x
      exact ordinary_unit_section l E W M P.obj n i U x
    · have h := derivedTranspose l E W (podReindexCalculus l E W) M D P.obj C (𝟙 _)
      have hid : D.reductionComparison.app P.obj ≫ DerivedCategory.Q.map (𝟙 C) =
          D.reductionComparison.app P.obj := by
        rw [(DerivedCategory.Q (C := coefficientSequenceModules l E W)).map_id]
        exact Category.comp_id _
      rw [hid] at h
      erw [Adjunction.homEquiv_id] at h
      simpa only [Adjunction.homEquiv_unit, b, a, asIso_hom] using! h

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem adjoint_unit_injective
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (ad : F ⊣ G) {N : A} {Z : B} {f g : F.obj N ⟶ Z}
    (h : ad.unit.app N ≫ G.map f = ad.unit.app N ≫ G.map g) : f = g :=
  (ad.homEquiv N Z).injective h

attribute [local irreducible] SheafOfModules.monoidalCategory constantSheaf
  completedIntegralCommRingSheafUnrestricted coefficientSequenceCommRingSheaf
  scalarReductionExtension integralComparisonSequenceTensorSection

private theorem quotient_unit_ext (W : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E W) (N : scalarReductionSource l E W)
    (Z : coefficientSequenceModules l E W) (f g : M.tensor.obj N ⟶ Z)
    (h : ∀ (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj U),
      f.val.app (op (n, U.unop)) (PodQuotientTransition.unitSection l E W M N n U x) =
        g.val.app (op (n, U.unop)) (PodQuotientTransition.unitSection l E W M N n U x)) :
    f = g := by
  have he (n : ℕ) : (coefficientSequenceEvaluation l E W n).map f =
      (coefficientSequenceEvaluation l E W n).map g := by
    apply (cancel_epi ((M.evaluation n).inv.app N)).1
    apply adjoint_unit_injective (scalarReductionExtension_adjunction l E W n).choose
    ext U x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    erw [scalarUnit_tensor]
    simpa only [PodQuotientTransition.unitSection, sequenceSection_eq] using! h n U x
  ext U x
  exact congrArg (fun k ↦ k.val.app (op U.unop.2) x) (he U.unop.1)

private theorem scalar_quotient_unit_ext (W : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E W) (N : scalarReductionSource l E W)
    (Z : coefficientSequenceModules l L W)
    (f g : (integralComparisonSequenceScalarModel l E L ι W).E.obj (M.tensor.obj N) ⟶ Z)
    (h : ∀ (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj U),
      f.val.app (op (n, U.unop))
          (integralComparisonSequenceTensorSection l E L ι W (M.tensor.obj N)
            (op (n, U.unop)) 1 (PodQuotientTransition.unitSection l E W M N n U x)) =
        g.val.app (op (n, U.unop))
          (integralComparisonSequenceTensorSection l E L ι W (M.tensor.obj N)
            (op (n, U.unop)) 1 (PodQuotientTransition.unitSection l E W M N n U x))) :
    f = g := by
  apply adjoint_unit_injective (sequenceScalarAdjunction l E L ι W).choose
  apply quotient_unit_ext l E W M N
  intro n U x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  dsimp only [SheafOfModules.restrictScalars, PresheafOfModules.restrictScalars,
    ModuleCat.restrictScalars]
  erw [sequenceScalarAdjunction_unit]
  exact h n U x

/-- The scalar counit on a good complex is the ordinary balanced quotient comparison.
Source: Stacks 06YY, 0941, and the scalar-normalization step of the blueprint
theorem-poincare-duality-frobenius--2, Steps 1 and 5.
(blueprint: lem-pod-scalar-reduction-quotient-normalization).

Proof: the derived model DE gives a coherent presentation of P by its ordinary
quotient complex. Apply scalarCompletionQuotientPresentation to this presentation.
Its resulting presentation of ordinary scalar extension has unit generators given
by nested unit tensors. The inverse strict comparison has precisely the generator
formula prescribed for alpha. The coherent quotient model comparison with DL identifies the
resulting presentation with DL.reductionComparison followed by Q(alpha inverse).
The final equation of scalarCompletionQuotientPresentation is the claimed equation
after expanding podScalarReduction and combining the two reduction images.
The comparison takes place in the whole derived sequence category. No finite
quotient evaluation is assumed faithful. No reindexing, completeness or geometric
invertibility is used. Identity embeddings, ramified embeddings and zero complexes
use the same balanced tensor unit formula. -/
theorem podScalarReduction_quotient_normalization (W : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l L W)
    (S : IntegralComparisonScalarModel l E L ι W (podReindexCalculus l E W) ρ)
    (ME : CompletionUnit.OrdinaryModel l E W) (ML : CompletionUnit.OrdinaryModel l L W)
    (DE : CompletionUnit.DerivedModel l E W (podReindexCalculus l E W) ME)
    (DL : CompletionUnit.DerivedModel l L W (podReindexCalculus l L W) ML)
    (α : ME.tensor ⋙ (integralComparisonSequenceScalarModel l E L ι W).E ≅
      integralOrdinaryScalar l E L ι W ⋙ ML.tensor)
    (hα : PodQuotientTransition.ScalarNormalized l E L ι W ME ML α)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (podReindexCalculus l L W).reduction.map
        ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj) ≫
      DL.reductionComparison.app
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).inv.app P.obj) =
    (podScalarReduction l E L ι W ρ S).app (DerivedCategory.Q.obj P.obj) ≫
      (integralComparisonDerivedSequenceScalar l E L ι W).map
        (DE.reductionComparison.app P.obj) ≫
      (integralComparisonSequenceScalarModel l E L ι W).ε.app ((ME.quotient l E W).obj P.obj) := by
  have := DE.reduction_isIso P.obj P.property.1 P.property.2
  let C := (ME.quotient l E W).obj P.obj
  let e := asIso (DE.reductionComparison.app P.obj)
  let κ (n : ℕ) := (NatIso.mapHomologicalComplex (ME.evaluation n) (.up ℤ)).app P.obj
  have hpres := canonicalPresentation l E W ME DE P
  obtain ⟨eS, κS, hpS, hcS, hgen, heq⟩ :=
    ScalarExtensionTower.scalarCompletionQuotientPresentation l E L ι W
      (podReindexCalculus l E W) (podReindexCalculus l L W) ρ S P C e κ
      hpres.1 hpres.2
  let PS := ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P.obj
  let CS := ((integralComparisonSequenceScalarModel l E L ι W).E.mapHomologicalComplex
    (.up ℤ)).obj C
  obtain ⟨a, ha, hκ⟩ := coherentQuotientModelComparison l L W
    (podReindexCalculus l L W) ML DL PS CS eS κS hcS
  have haeq : a.inv = (NatIso.mapHomologicalComplex α (.up ℤ)).hom.app P.obj := by
    apply HomologicalComplex.hom_ext
    intro i
    apply scalar_quotient_unit_ext l E L ι W ME (P.obj.X i)
    intro n U x
    change (a.inv.f i).val.app (op (n, U.unop))
        (integralComparisonSequenceTensorSection l E L ι W (ME.tensor.obj (P.obj.X i))
          (op (n, U.unop)) 1 (PodQuotientTransition.unitSection l E W ME (P.obj.X i) n U x)) =
      (α.hom.app (P.obj.X i)).val.app (op (n, U.unop))
        (integralComparisonSequenceTensorSection l E L ι W (ME.tensor.obj (P.obj.X i))
          (op (n, U.unop)) 1 (PodQuotientTransition.unitSection l E W ME (P.obj.X i) n U x))
    erw [hα (P.obj.X i) n U x]
    let z := integralComparisonSequenceTensorSection l E L ι W (ME.tensor.obj (P.obj.X i))
      (op (n, U.unop)) 1 (PodQuotientTransition.unitSection l E W ME (P.obj.X i) n U x)
    have heval :
        ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).map a.inv ≫
          ((NatIso.mapHomologicalComplex (ML.evaluation n) (.up ℤ)).app PS).hom =
        (κS n).hom := by
      rw [← hκ n]
      exact (((coefficientSequenceEvaluation l L W n).mapHomologicalComplex
        (.up ℤ)).mapIso a).inv_hom_id_assoc (κS n).hom
    let k := (ML.evaluation n).app (PS.X i)
    have hinj : Function.Injective (fun y ↦ k.hom.val.app U y) := by
      intro y y' hy
      have hcancel (y) : k.inv.val.app U (k.hom.val.app U y) = y :=
        congrArg (fun f ↦ f.val.app U y) k.hom_inv_id
      exact (hcancel y).symm.trans ((congrArg (fun y ↦ k.inv.val.app U y) hy).trans
        (hcancel y'))
    apply hinj
    have hv := congrArg (fun f ↦ (f.f i).val.app U z) heval
    simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply] at hv
    calc
      _ = ((κS n).hom.f i).val.app U z := hv
      _ = unrestrictedIntegralTensorSection l L W n (PS.X i) U 1
          (integralOrdinaryTensorSection l E L ι W (P.obj.X i) U 1 x) := hgen n i U.unop x
      _ = _ := by
        exact (congrArg (fun f ↦ f.val.app U
          (unrestrictedIntegralTensorSection l L W n (PS.X i) U 1
            (integralOrdinaryTensorSection l E L ι W (P.obj.X i) U 1 x))) k.inv_hom_id).symm
  have hai : a.hom = (NatIso.mapHomologicalComplex α (.up ℤ)).inv.app P.obj := by
    apply (cancel_mono a.inv).1
    rw [a.hom_inv_id, haeq, Iso.inv_hom_id_app]
    rfl
  rw [← hai, ha]
  simpa only [podScalarReduction, ScalarExtensionTower.scalarReduction,
    integralComparisonScalarCounit, e, asIso_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.map_comp,
    Category.assoc] using! heq

end WeilConjectures
