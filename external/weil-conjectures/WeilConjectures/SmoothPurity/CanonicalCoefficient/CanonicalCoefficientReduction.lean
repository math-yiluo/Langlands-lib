/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SmoothPurity.CoefficientClosedStructure.CoefficientClosedTensorComparison

/-! # Explicit change of closed presentations in the coefficient calculus

Source: Stacks 07A4, 08J9, 08JD and 0941.
(blueprint: def-pur-canonical-coefficient-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe a b v w t u c r
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures
namespace CanonicalCoefficient

section Transport
variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
  (SA TA : CoefficientClosedStructure HA) (SB TB : CoefficientClosedStructure HB)
  (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)

/-- Conjugate a tensor comparison by the evaluation-preserving adjoint comparisons. -/
def tensorComparison : TA.tensor ⋙ F ≅ F.prod F ⋙ TB.tensor :=
  (Functor.isoWhiskerRight (CoefficientClosedStructure.comparison SA TA).symm F) ≪≫
    μ ≪≫ Functor.isoWhiskerLeft (F.prod F) (CoefficientClosedStructure.comparison SB TB)

/-- The evaluation-defined Hom comparison is unchanged by conjugation. -/
theorem baseChange_eq (P Q : A) :
    coefficientBaseChangeHom TA TB F (tensorComparison SA TA SB TB F μ) P Q =
      coefficientBaseChangeHom SA SB F μ P Q := by
  unfold coefficientBaseChangeHom
  have he := CoefficientClosedStructure.comparison_evaluation SA TA P Q
  have hm :
      (tensorComparison SA TA SB TB F μ).inv.app (HA.obj (op P, Q), P) ≫
          F.map (TA.evaluation P Q) =
        (CoefficientClosedStructure.comparison SB TB).inv.app
            (F.obj (HA.obj (op P, Q)), F.obj P) ≫
          (μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q)) := by
    dsimp only [tensorComparison, Iso.trans_inv, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_inv]
    rw [Category.assoc, Category.assoc, ← F.map_comp, he]
    rfl
  rw [hm, CoefficientClosedStructure.comparison_inv_transpose]

/-- The enriched adjunction map is unchanged as an actual morphism. -/
theorem enriched_eq {G : B ⥤ A} (adj : F ⊣ G) (P : A) (N : B) :
    coefficientEnrichedAdjunctionMap TA TB F adj (tensorComparison SA TA SB TB F μ) P N =
      coefficientEnrichedAdjunctionMap SA SB F adj μ P N := by
  unfold coefficientEnrichedAdjunctionMap
  rw [baseChange_eq]

/-- Conjugation preserves the tensor-Hom transpose formula. -/
theorem transpose_eq
    (h : CoefficientEvaluationCompatible SA SB F μ) (T P Q : A)
    (f : TA.tensor.obj (T, P) ⟶ Q) :
    F.map (TA.transpose T P Q f) ≫
        coefficientBaseChangeHom TA TB F (tensorComparison SA TA SB TB F μ) P Q =
      TB.transpose (F.obj T) (F.obj P) (F.obj Q)
        ((tensorComparison SA TA SB TB F μ).inv.app (T, P) ≫ F.map f) := by
  rw [baseChange_eq, ← CoefficientClosedStructure.comparison_transpose SA TA]
  rw [h.transpose, F.map_comp]
  dsimp only [tensorComparison, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_inv, Functor.prod_obj]
  rw [Category.assoc, Category.assoc,
    CoefficientClosedStructure.comparison_inv_transpose]

/-- The uncurried evaluation formula for the conjugated comparison. -/
theorem evaluation_eq (P Q : A) :
    (tensorComparison SA TA SB TB F μ).inv.app (HA.obj (op P, Q), P) ≫
        F.map (TA.evaluation P Q) =
      (CoefficientClosedStructure.comparison SB TB).inv.app
          (F.obj (HA.obj (op P, Q)), F.obj P) ≫
        μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q) := by
  dsimp only [tensorComparison, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_inv, Functor.prod_obj]
  rw [Category.assoc, Category.assoc, ← F.map_comp,
    CoefficientClosedStructure.comparison_evaluation]

/-- An actual fiber evaluation equation survives the change of presentations. -/
theorem fiberEvaluation (P Q : A)
    (β : F.obj (HA.obj (op P, Q)) ⟶ HB.obj (op (F.obj P), F.obj Q))
    (h : μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q) =
      SB.tensor.map (Prod.mkHom β (𝟙 _)) ≫ SB.evaluation (F.obj P) (F.obj Q)) :
    (tensorComparison SA TA SB TB F μ).inv.app (HA.obj (op P, Q), P) ≫
        F.map (TA.evaluation P Q) =
      TB.tensor.map (Prod.mkHom β (𝟙 _)) ≫ TB.evaluation (F.obj P) (F.obj Q) := by
  rw [evaluation_eq, h]
  apply (cancel_epi ((CoefficientClosedStructure.comparison SB TB).hom.app
    (F.obj (HA.obj (op P, Q)), F.obj P))).mp
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hn := (CoefficientClosedStructure.comparison SB TB).hom.naturality
    (Prod.mkHom β (𝟙 (F.obj P)))
  rw [← hn, Category.assoc,
    CoefficientClosedStructure.comparison_evaluation]

/-- Naturality and inverse cancellation preserve an entire representative square. -/
theorem tensorSquare {K : Type*} [Category K] (Q : K ⥤ B)
    {X Y Z : A} {X' Y' Z' N : K}
    (s : Z ⟶ SA.tensor.obj (X, Y))
    (p : F.obj X ⟶ Q.obj X') (q : F.obj Y ⟶ Q.obj Y')
    (z : F.obj Z ⟶ Q.obj Z') (e : Z' ⟶ N)
    (t : Q.obj N ⟶ SB.tensor.obj (Q.obj X', Q.obj Y'))
    (h : CoefficientTensorComparisonSquare SA.tensor SB.tensor F Q s μ.hom p q z e t) :
    CoefficientTensorComparisonSquare TA.tensor TB.tensor F Q
      (s ≫ (CoefficientClosedStructure.comparison SA TA).hom.app (X, Y))
      (tensorComparison SA TA SB TB F μ).hom p q z e
      (t ≫ (CoefficientClosedStructure.comparison SB TB).hom.app (Q.obj X', Q.obj Y')) := by
  unfold CoefficientTensorComparisonSquare at h ⊢
  dsimp only [tensorComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Functor.prod_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc ((CoefficientClosedStructure.comparison SA TA).hom.app (X, Y))
    ((CoefficientClosedStructure.comparison SA TA).inv.app (X, Y)),
    Iso.hom_inv_id_app, F.map_id, Category.id_comp]
  have hn := (CoefficientClosedStructure.comparison SB TB).hom.naturality
    (Prod.mkHom p q)
  rw [← hn]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ (CoefficientClosedStructure.comparison SB TB).hom.app
      (Q.obj X', Q.obj Y')) h

end Transport

section EvaluationTransport
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v} A] [Category.{w} B] [Category.{r} C]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HC : Cᵒᵖ × C ⥤ C}
  (SA TA : CoefficientClosedStructure HA) (SB TB : CoefficientClosedStructure HB)
  (SC TC : CoefficientClosedStructure HC)
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) (e : F ⋙ G ≅ H)
  (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
  (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SC.tensor)
  (ξ : SA.tensor ⋙ H ≅ H.prod H ⋙ SC.tensor)

/-- The evaluated reduction square commutes after simultaneous conjugation. -/
theorem evaluation_transport (P Q : A)
    (h : CoefficientComparisonEquation (G.map (μ.hom.app (P, Q)))
      (ν.hom.app (F.obj P, F.obj Q))
      (SC.tensor.map (Prod.mkHom (e.hom.app P) (e.hom.app Q)))
      (e.hom.app (SA.tensor.obj (P, Q))) (ξ.hom.app (P, Q))) :
    CoefficientComparisonEquation
      (G.map ((tensorComparison SA TA SB TB F μ).hom.app (P, Q)))
      ((tensorComparison SB TB SC TC G ν).hom.app (F.obj P, F.obj Q))
      (TC.tensor.map (Prod.mkHom (e.hom.app P) (e.hom.app Q)))
      (e.hom.app (TA.tensor.obj (P, Q)))
      ((tensorComparison SA TA SC TC H ξ).hom.app (P, Q)) := by
  unfold CoefficientComparisonEquation at h ⊢
  dsimp only [tensorComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Functor.prod_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc ((CoefficientClosedStructure.comparison SB TB).hom.app
      (F.obj P, F.obj Q)) ((CoefficientClosedStructure.comparison SB TB).inv.app
      (F.obj P, F.obj Q)), Iso.hom_inv_id_app, G.map_id, Category.id_comp]
  have hc := (CoefficientClosedStructure.comparison SC TC).hom.naturality
    (Prod.mkHom (e.hom.app P) (e.hom.app Q))
  dsimp only [Functor.comp_obj] at hc
  rw [← hc]
  have h' := congrArg (fun z ↦ G.map (F.map
      ((CoefficientClosedStructure.comparison SA TA).inv.app (P, Q))) ≫ z ≫
      (CoefficientClosedStructure.comparison SC TC).hom.app (H.obj P, H.obj Q)) h
  simp only [Category.assoc] at h'
  rw [h']
  have he := e.hom.naturality ((CoefficientClosedStructure.comparison SA TA).inv.app (P, Q))
  dsimp only [Functor.comp_map] at he
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ ξ.hom.app (P, Q) ≫
    (CoefficientClosedStructure.comparison SC TC).hom.app (H.obj P, H.obj Q)) he

end EvaluationTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] DerivedCategory DerivedCategory.Q
  coefficientTotalTensor coefficientTensorGenerator
  CochainComplex.IsKFlatIndependentCoefficients homComplex homComplexFunctor
  derivedInternalHomOfUniverses SheafOfModules.monoidalCategory

set_option maxHeartbeats 800000 in
-- The independent-universe representative square has large dependent module types.
/-- Change the tensor model by the same adjoint comparison, retaining ordinary uncurrying. -/
def tensorModels {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (S T : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (M : CoefficientTensorModels.{r, c, v, w} J R S) :
    CoefficientTensorModels.{r, c, v, w} J R T where
  comparison := M.comparison ≪≫ Functor.isoWhiskerLeft
    ((coefficientKFlatInclusion.{r, c, v} J R ⋙ DerivedCategory.Q).prod
      (coefficientKFlatInclusion.{r, c, v} J R ⋙ DerivedCategory.Q))
    (CoefficientClosedStructure.comparison S T)
  uncurry_model := by
    intro P L N φ
    obtain ⟨ψ, hψ, he⟩ := M.uncurry_model P L N φ
    refine ⟨ψ, hψ, ?_⟩
    change (M.comparison.hom.app (P, L) ≫
      (CoefficientClosedStructure.comparison S T).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj L.obj)) ≫
      (T.transpose _ _ _).symm
        (DerivedCategory.Q.map φ ≫ (coefficientHomResolutionIso.{r, c, v, w}
          J R L.obj N).inv) = _
    rw [Category.assoc]
    have ht : (CoefficientClosedStructure.comparison S T).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj L.obj) ≫
        (T.transpose _ _ _).symm
          (DerivedCategory.Q.map φ ≫
            (coefficientHomResolutionIso.{r, c, v, w} J R L.obj N).inv) =
      (S.transpose _ _ _).symm
          (DerivedCategory.Q.map φ ≫
            (coefficientHomResolutionIso.{r, c, v, w} J R L.obj N).inv) := by
      apply (S.transpose _ _ _).injective
      rw [CoefficientClosedStructure.comparison_transpose, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    rw [ht]
    exact he

/-- Fixed normalized closed structures, with the old representative models transported
by the uniquely evaluation-preserving comparison. -/
def tensors (S : CoefficientDerivedSystemTensors l E W) :
    CoefficientDerivedSystemTensors l E W where
  integralClosed := (IntegralOnSlice.duality l E W none).closed
  integralTensorModel := tensorModels
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)
    S.integralClosed (IntegralOnSlice.duality l E W none).closed S.integralTensorModel
  systemClosed := (Classical.choice (ringedSiteDualityMaps_exists.{t+1, t, u,
    (max u (t+1))+1} (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W))).closed
  systemTensorModel := tensorModels
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) S.systemClosed _ S.systemTensorModel
  finiteClosed n := (Classical.choice (ringedSiteDualityMaps_exists.{t+1, t, u,
    (max u (t+1))+1} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n))).closed
  finiteTensorModel n := tensorModels
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)
    (S.finiteClosed n) _ (S.finiteTensorModel n)

attribute [local irreducible] tensors tensorModels

/-- Keep the actual reduction functor and adjunction, and conjugate its tensor maps. -/
def reduction (S : CoefficientDerivedSystemReduction l E W) :
    CoefficientDerivedSystemReduction l E W where
  toCoefficientDerivedSystemReductionModel :=
    { toCoefficientDerivedSystemTensors := tensors l E W S.toCoefficientDerivedSystemTensors
      reduction := S.reduction
      adjunction := S.adjunction
      reductionEvaluation := S.reductionEvaluation
      reductionModel := S.reductionModel
      reduction_normalized := S.reduction_normalized }
  unit_projection := S.unit_projection
  counit_projection := S.counit_projection
  reductionTensor := tensorComparison S.integralClosed
    (tensors l E W S.toCoefficientDerivedSystemTensors).integralClosed
    S.systemClosed (tensors l E W S.toCoefficientDerivedSystemTensors).systemClosed
    S.reduction S.reductionTensor
  finiteTensor n := tensorComparison S.integralClosed
    (tensors l E W S.toCoefficientDerivedSystemTensors).integralClosed
    (S.finiteClosed n) ((tensors l E W S.toCoefficientDerivedSystemTensors).finiteClosed n)
    (coefficientFiniteDerivedExtension l E W n) (S.finiteTensor n)
  evaluationTensor n := tensorComparison S.systemClosed
    (tensors l E W S.toCoefficientDerivedSystemTensors).systemClosed
    (S.finiteClosed n) ((tensors l E W S.toCoefficientDerivedSystemTensors).finiteClosed n)
    (coefficientSequenceDerivedEvaluation l E W n) (S.evaluationTensor n)

/-- Quotient adjunctions and K-flat preservation stay fixed; only their tensor maps change. -/
def quotientData (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientData l E W S) :
    CoefficientFiniteQuotientData l E W (tensors l E W S) where
  ordinaryAdjunction := D.ordinaryAdjunction
  adjunction := D.adjunction
  preservesKFlat := D.preservesKFlat
  tensor h := tensorComparison (S.finiteClosed _) ((tensors l E W S).finiteClosed _)
    (S.finiteClosed _) ((tensors l E W S).finiteClosed _)
    (coefficientFiniteQuotientDerived l E W h) (D.tensor h)

end CanonicalCoefficient
end WeilConjectures
