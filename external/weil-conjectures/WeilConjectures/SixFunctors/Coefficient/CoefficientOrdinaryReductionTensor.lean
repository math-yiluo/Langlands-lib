/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorSections
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorAssembly
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorKFlat
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedEvaluationTensorChain

/-! # The ordinary quotient system commutes with total tensor products

Source: Stacks 07A4 (lemma-pullback-tensor-product) and 0941.

For an ordinary quotient-system model `M`, we construct a natural isomorphism of chain
complexes on the ringed sequence site
`M.quotient (P ⊗ Q) ≅ M.quotient P ⊗ M.quotient Q`, whose finite evaluations are the
ordinary scalar tensor comparisons. Both sides are presented levelwise by the finite
scalar extensions of `P ⊗ Q`, compatibly with the strict transitions, and maps of
modules on the sequence site are assembled from compatible finite evaluations.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryQuotient

noncomputable section
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension HasDerivedCategory.standard coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology constantSheaf coefficientSequenceEvaluation
  coefficientTotalTensor coefficientTensorGenerator coefficientEvaluationTensorIso
  coefficientScalarTensorIso coefficientSequenceTransition coefficientOrdinaryQuotient

attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf CategoryTheory.sheafCompose
  CommRingCat.hasForgetToRingCat

/-- Chain maps on the ringed sequence site are determined by their finite evaluations.
Source: Stacks 0941. -/
theorem coefficientSequenceComplex_hom_ext
    {C D : CochainComplex (coefficientSequenceModules l E W) ℤ} {f g : C ⟶ D}
    (h : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map f =
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map g) :
    f = g := by
  ext i : 1
  apply OrdinaryReductionTensor.coefficientSequence_hom_ext l E W
  intro n
  exact congrArg (fun φ ↦ φ.f i) (h n)

section Presentation

variable {l E W}
variable {C D : CochainComplex (coefficientSequenceModules l E W) ℤ}
  {T : CochainComplex (scalarReductionSource l E W) ℤ}

/-- Two compatible presentations of strict system complexes by the same scalar complex
give compatible maps between their finite evaluations. Source: Stacks 0941. -/
theorem presentation_degree_transition
    (κC : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj T)
    (κD : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj T)
    (hC : ∀ {m n : ℕ} (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h) (.up ℤ)).app C ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (κC n).hom =
      (κC m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app T)
    (hD : ∀ {m n : ℕ} (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h) (.up ℤ)).app D ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (κD n).hom =
      (κD m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app T)
    (i : ℤ) {m n : ℕ} (h : n ≤ m) :
    (coefficientSequenceTransition l E W h).app (C.X i) ≫
        (normalizedDVRModuleRes l E W h).map (((κC n).hom ≫ (κD n).inv).f i) =
      ((κC m).hom ≫ (κD m).inv).f i ≫ (coefficientSequenceTransition l E W h).app (D.X i) := by
  have hCi : (coefficientSequenceTransition l E W h).app (C.X i) ≫
      (normalizedDVRModuleRes l E W h).map ((κC n).hom.f i) =
        (κC m).hom.f i ≫ (coefficientOrdinaryQuotient l E W h).app (T.X i) :=
    congrArg (fun f ↦ f.f i) (hC h)
  have hDi : (coefficientSequenceTransition l E W h).app (D.X i) ≫
      (normalizedDVRModuleRes l E W h).map ((κD n).hom.f i) =
        (κD m).hom.f i ≫ (coefficientOrdinaryQuotient l E W h).app (T.X i) :=
    congrArg (fun f ↦ f.f i) (hD h)
  apply (cancel_mono ((normalizedDVRModuleRes l E W h).map ((κD n).hom.f i))).1
  simp only [HomologicalComplex.comp_f, Category.assoc]
  erw [← Functor.map_comp, ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hDm : (κD m).inv.f i ≫ (κD m).hom.f i = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun g ↦ g.f i) (κD m).inv_hom_id
  erw [hDi, hCi, reassoc_of% hDm]

/-- The chain map between two compatible presentations of strict system complexes,
assembled from the finite comparisons. Source: Stacks 03CZ, 0941. -/
def presentationHom
    (κC : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj T)
    (κD : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj T)
    (hC : ∀ {m n : ℕ} (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h) (.up ℤ)).app C ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (κC n).hom =
      (κC m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app T)
    (hD : ∀ {m n : ℕ} (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h) (.up ℤ)).app D ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (κD n).hom =
      (κD m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app T) :
    C ⟶ D where
  f i := OrdinaryReductionTensor.coefficientSequenceAssemble l E W
    (fun n ↦ ((κC n).hom ≫ (κD n).inv).f i)
    (fun h ↦ presentation_degree_transition κC κD hC hD i h)
  comm' i j _ := by
    apply OrdinaryReductionTensor.coefficientSequence_hom_ext l E W
    intro n
    erw [Functor.map_comp, Functor.map_comp,
      OrdinaryReductionTensor.coefficientSequenceAssemble_evaluation,
      OrdinaryReductionTensor.coefficientSequenceAssemble_evaluation]
    have hc := ((κC n).hom ≫ (κD n).inv).comm i j
    simp only [Functor.mapHomologicalComplex_obj_d] at hc
    exact hc

/-- The finite evaluations of the assembled presentation map.
Source: Stacks 0941. -/
theorem presentationHom_evaluation
    (κC : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj T)
    (κD : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj T)
    (hC : ∀ {m n : ℕ} (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h) (.up ℤ)).app C ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (κC n).hom =
      (κC m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app T)
    (hD : ∀ {m n : ℕ} (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h) (.up ℤ)).app D ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (κD n).hom =
      (κD m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app T)
    (n : ℕ) :
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
        (presentationHom κC κD hC hD) = (κC n).hom ≫ (κD n).inv := by
  ext i : 1
  exact OrdinaryReductionTensor.coefficientSequenceAssemble_evaluation l E W _
    (fun h ↦ presentation_degree_transition κC κD hC hD i h) n

/-- The isomorphism between two compatible presentations of strict system complexes.
Source: Stacks 03CZ, 0941. -/
def presentationIso
    (κC : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj T)
    (κD : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj T)
    (hC : ∀ {m n : ℕ} (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h) (.up ℤ)).app C ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (κC n).hom =
      (κC m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app T)
    (hD : ∀ {m n : ℕ} (h : n ≤ m),
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h) (.up ℤ)).app D ≫
        ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map (κD n).hom =
      (κD m).hom ≫
        (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app T) :
    C ≅ D where
  hom := presentationHom κC κD hC hD
  inv := presentationHom κD κC hD hC
  hom_inv_id := by
    apply coefficientSequenceComplex_hom_ext
    intro n
    rw [Functor.map_comp, presentationHom_evaluation, presentationHom_evaluation,
      CategoryTheory.Functor.map_id]
    simp
  inv_hom_id := by
    apply coefficientSequenceComplex_hom_ext
    intro n
    rw [Functor.map_comp, presentationHom_evaluation, presentationHom_evaluation,
      CategoryTheory.Functor.map_id]
    simp

end Presentation

/-- The ordinary quotient system of a complex, presented by its finite evaluations,
commutes with the strict transitions. Source: Stacks 0941. -/
theorem OrdinaryModel.quotient_transition (M : OrdinaryModel l E W)
    (X : CochainComplex (scalarReductionSource l E W) ℤ) {m n : ℕ} (h : n ≤ m) :
    (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h) (.up ℤ)).app
        ((M.quotient l E W).obj X) ≫
      ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app X).hom =
    ((NatIso.mapHomologicalComplex (M.evaluation m) (.up ℤ)).app X).hom ≫
      (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app X := by
  ext i : 1
  exact M.transition (X.X i) h

/-- The ordinary evaluation tensor comparison is natural in both complexes.
Source: Stacks 03EK, 0941. -/
theorem coefficientEvaluationTensorIso_naturality (n : ℕ)
    {P P' Q Q' : CochainComplex (coefficientSequenceModules l E W) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
        ((coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom f g)) ≫
        (coefficientEvaluationTensorIso l E W n P' Q').hom =
      (coefficientEvaluationTensorIso l E W n P Q).hom ≫
        (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map
          (Prod.mkHom
            (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map f)
            (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map g)) := by
  obtain ⟨β, hβ⟩ := coefficientNormalizedEvaluationTensorChain l E W n
  have h := β.hom.naturality (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom f g)
  rw [← hβ, ← hβ]
  exact h

-- Instantiating the generic naturality checks the concrete scalar extension interfaces.
/-- The ordinary scalar tensor comparison is natural in both complexes.
Source: Stacks 03EK, 07A4. -/
theorem coefficientScalarTensorIso_naturality (n : ℕ)
    {P P' Q Q' : CochainComplex (scalarReductionSource l E W) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).map
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).map (Prod.mkHom f g)) ≫
        (coefficientScalarTensorIso l E W n P' Q').hom =
      (coefficientScalarTensorIso l E W n P Q).hom ≫
        (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map
          (Prod.mkHom (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).map f)
            (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).map g)) :=
  OrdinaryReductionTensor.scalarTensor_naturality
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))
    (hF := coefficientFiniteExtensionAdditive l E W n)
    (coefficientOrdinaryScalarAdjunction l E W n) f g
    (coefficientScalarTensorIso l E W n P Q) (coefficientScalarTensorIso l E W n P' Q')
    (coefficientScalarTensorIso_generators l E W n P Q)
    (coefficientScalarTensorIso_generators l E W n P' Q')

/-- A presentation of a tensor product, assembled from natural evaluation and scalar tensor
comparisons and a natural comparison `θ`, is natural in both inputs.
Source: Stacks 07A4. -/
theorem evaluated_tensor_presentation_naturality {A S L : Type*} [Category* A] [Category* S]
    [Category* L] (tA : A × A ⥤ A) (tS : S × S ⥤ S) (tL : L × L ⥤ L) (K : A ⥤ S)
    (Ev : S ⥤ L) (F : A ⥤ L) (θ : K ⋙ Ev ≅ F)
    (e : ∀ X Y : S, Ev.obj (tS.obj (X, Y)) ≅ tL.obj (Ev.obj X, Ev.obj Y))
    (s : ∀ P Q : A, F.obj (tA.obj (P, Q)) ≅ tL.obj (F.obj P, F.obj Q))
    (he : ∀ {X X' Y Y' : S} (f : X ⟶ X') (g : Y ⟶ Y'),
      Ev.map (tS.map (Prod.mkHom f g)) ≫ (e X' Y').hom =
        (e X Y).hom ≫ tL.map (Prod.mkHom (Ev.map f) (Ev.map g)))
    (hs : ∀ {P P' Q Q' : A} (f : P ⟶ P') (g : Q ⟶ Q'),
      F.map (tA.map (Prod.mkHom f g)) ≫ (s P' Q').hom =
        (s P Q).hom ≫ tL.map (Prod.mkHom (F.map f) (F.map g)))
    {P P' Q Q' : A} (f : P ⟶ P') (g : Q ⟶ Q') :
    Ev.map (tS.map (Prod.mkHom (K.map f) (K.map g))) ≫
        (e (K.obj P') (K.obj Q') ≪≫ tL.mapIso ((θ.app P').prod (θ.app Q')) ≪≫
          (s P' Q').symm).hom =
      (e (K.obj P) (K.obj Q) ≪≫ tL.mapIso ((θ.app P).prod (θ.app Q)) ≪≫
          (s P Q).symm).hom ≫ F.map (tA.map (Prod.mkHom f g)) := by
  have hθ : tL.map (Prod.mkHom (Ev.map (K.map f)) (Ev.map (K.map g))) ≫
      tL.map (Prod.mkHom (θ.hom.app P') (θ.hom.app Q')) =
      tL.map (Prod.mkHom (θ.hom.app P) (θ.hom.app Q)) ≫
        tL.map (Prod.mkHom (F.map f) (F.map g)) := by
    rw [← tL.map_comp, ← tL.map_comp]
    congr 1
    exact Prod.ext (θ.hom.naturality f) (θ.hom.naturality g)
  have hs' : tL.map (Prod.mkHom (F.map f) (F.map g)) ≫ (s P' Q').inv =
      (s P Q).inv ≫ F.map (tA.map (Prod.mkHom f g)) := by
    rw [Iso.comp_inv_eq, Category.assoc, hs, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
    Category.assoc]
  rw [reassoc_of% (he (K.map f) (K.map g)), reassoc_of% hθ, hs']

/-- The finite presentations of system tensor products are natural.
Source: Stacks 03EK, 07A4 and 0941. -/
theorem OrdinaryModel.tensorPresentation_naturality (M : OrdinaryModel l E W) (n : ℕ)
    {P P' Q Q' : CochainComplex (scalarReductionSource l E W) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
        ((coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map
            (Prod.mkHom ((M.quotient l E W).map f) ((M.quotient l E W).map g))) ≫
        (M.tensorPresentation l E W n P' Q').hom =
      (M.tensorPresentation l E W n P Q).hom ≫
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).map
          ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).map (Prod.mkHom f g)) :=
  evaluated_tensor_presentation_naturality
    (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W))
    (coefficientTotalTensor.{u, t + 1, t}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W))
    (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n))
    (M.quotient l E W) ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ))
    ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ))
    (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ))
    (coefficientEvaluationTensorIso l E W n) (coefficientScalarTensorIso l E W n)
    (fun f g ↦ coefficientEvaluationTensorIso_naturality l E W n f g)
    (fun f g ↦ coefficientScalarTensorIso_naturality l E W n f g) f g

/-- The component of the tensor comparison for the ordinary quotient system: the strict
comparison between the presentations of `M.quotient (P ⊗ Q)` and
`M.quotient P ⊗ M.quotient Q`. Source: Stacks 07A4 and 0941. -/
def OrdinaryModel.quotientTensorApp (M : OrdinaryModel l E W)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    (M.quotient l E W).obj ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
          ((M.quotient l E W).obj P, (M.quotient l E W).obj Q) :=
  presentationIso
    (fun n ↦ (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app
      ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)))
    (fun n ↦ M.tensorPresentation l E W n P Q)
    (fun h ↦ M.quotient_transition l E W _ h)
    (fun h ↦ M.tensorPresentation_transition l E W P Q h)

/-- The finite evaluations of `OrdinaryModel.quotientTensorApp`.
Source: Stacks 07A4 and 0941. -/
theorem OrdinaryModel.quotientTensorApp_evaluation (M : OrdinaryModel l E W) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
        (M.quotientTensorApp l E W P Q).hom =
      ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q))).hom ≫
        (M.tensorPresentation l E W n P Q).inv :=
  presentationHom_evaluation _ _ (fun h ↦ M.quotient_transition l E W _ h)
    (fun h ↦ M.tensorPresentation_transition l E W P Q h) n

set_option backward.isDefEq.respectTransparency false in
/-- The tensor comparison for the ordinary quotient system.
Source: Stacks 07A4 (lemma-pullback-tensor-product) and 0941. -/
def OrdinaryModel.quotientTensor (M : OrdinaryModel l E W) :
    coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙ M.quotient l E W ≅
      (M.quotient l E W).prod (M.quotient l E W) ⋙
        coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) :=
  NatIso.ofComponents (fun X ↦ M.quotientTensorApp l E W X.1 X.2)
    (fun {X Y} φ ↦ by
      apply coefficientSequenceComplex_hom_ext
      intro n
      rw [← cancel_mono (M.tensorPresentation l E W n Y.1 Y.2).hom]
      erw [Functor.map_comp, Functor.map_comp, M.quotientTensorApp_evaluation,
        M.quotientTensorApp_evaluation]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      erw [M.tensorPresentation_naturality l E W n φ.1 φ.2]
      simp only [Iso.inv_hom_id_assoc]
      exact (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.naturality _)

set_option backward.isDefEq.respectTransparency false in
/-- **Tensor comparison for the ordinary quotient system.** There is a natural isomorphism
`M.quotient (P ⊗ Q) ≅ M.quotient P ⊗ M.quotient Q` whose finite evaluations are the
ordinary scalar tensor comparisons, under the evaluation tensor comparisons.
Source: Stacks 07A4 (lemma-pullback-tensor-product) and 0941. -/
theorem OrdinaryModel.quotientTensor_exists (M : OrdinaryModel l E W) :
    ∃ b : coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙ M.quotient l E W ≅
      (M.quotient l E W).prod (M.quotient l E W) ⋙
        coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W),
    ∀ (n : ℕ) (P Q : CochainComplex (scalarReductionSource l E W) ℤ),
      CoefficientComparisonEquation
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
          (b.hom.app (P, Q)))
        (coefficientEvaluationTensorIso l E W n ((M.quotient l E W).obj P)
          ((M.quotient l E W).obj Q)).hom
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map
            (Prod.mkHom ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P)
              ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q)))
        ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app
          ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)))
        (coefficientScalarTensorIso l E W n P Q).hom := by
  refine ⟨M.quotientTensor l E W, fun n P Q ↦ ?_⟩
  unfold CoefficientComparisonEquation
  erw [M.quotientTensorApp_evaluation l E W n P Q]
  simp only [Category.assoc, OrdinaryModel.tensorPresentation, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.prod_inv]
  erw [Iso.inv_hom_id_assoc]
  congr 1
  conv_rhs => rw [← Category.comp_id (coefficientScalarTensorIso l E W n P Q).hom]
  congr 1
  rw [← Functor.map_comp, prod_comp]
  simp

end
end OrdinaryQuotient
end WeilConjectures
