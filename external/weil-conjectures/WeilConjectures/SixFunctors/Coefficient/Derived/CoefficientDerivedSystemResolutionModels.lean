/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedInternalHomFibers
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsNormalization
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections

/-! # Normalized resolution models for coefficient systems

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YY, 07A4, 07A6,
08J9, 0A95, 0D6E and 0941; the existing sequence-site and semilinear constructions
(blueprint: lem-coef-derived-system-resolution-models).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b c v w r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

section ClosedNaturality

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}

private theorem uncurry_formula (SA : CoefficientClosedStructure HA)
    (T P Q : A) (f : T ⟶ HA.obj (op P, Q)) :
    (SA.transpose T P Q).symm f =
      SA.tensor.map (Prod.mkHom f (𝟙 P)) ≫ SA.evaluation P Q := by
  change (@MonoidalCategory.tensorRight A _ SA.monoidal P).map f ≫
    SA.evaluation P Q = _
  let _ := SA.monoidal
  simp [CoefficientClosedStructure.tensor]

private theorem evaluation_target (SA : CoefficientClosedStructure HA)
    (P Q Q' : A) (g : Q ⟶ Q') :
    SA.tensor.map (Prod.mkHom (HA.map (Prod.mkHom (𝟙 (op P)) g)) (𝟙 P)) ≫
      SA.evaluation P Q' = SA.evaluation P Q ≫ g := by
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR] using (SA.adjunction P).counit.naturality g

private theorem evaluation_source (SA : CoefficientClosedStructure HA)
    (P P' Q : A) (f : P' ⟶ P) :
    SA.tensor.map (Prod.mkHom (HA.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      SA.evaluation P' Q =
    SA.tensor.map (Prod.mkHom (𝟙 (HA.obj (op P, Q))) f) ≫ SA.evaluation P Q := by
  simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
    Prod.sectR] using SA.evaluation_naturality P P' Q f

private theorem evaluation_both (SA : CoefficientClosedStructure HA)
    (P P' Q Q' : A) (f : P' ⟶ P) (g : Q ⟶ Q') :
    SA.tensor.map (Prod.mkHom (HA.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
      SA.evaluation P' Q' =
    SA.tensor.map (Prod.mkHom (𝟙 (HA.obj (op P, Q))) f) ≫ SA.evaluation P Q ≫ g := by
  have hf : Prod.mkHom f.op g =
      Prod.mkHom f.op (𝟙 Q) ≫ Prod.mkHom (𝟙 (op P')) g := by simp
  rw [hf, HA.map_comp]
  have ht : Prod.mkHom
      (HA.map (Prod.mkHom f.op (𝟙 Q)) ≫ HA.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (HA.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (HA.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by simp
  rw [ht, SA.tensor.map_comp, Category.assoc, evaluation_target,
    ← Category.assoc, evaluation_source, Category.assoc]

private theorem uncurry_naturality (SA : CoefficientClosedStructure HA)
    (T P P' Q Q' : A) (z : T ⟶ HA.obj (op P, Q)) (f : P' ⟶ P) (g : Q ⟶ Q') :
    (SA.transpose T P' Q').symm (z ≫ HA.map (Prod.mkHom f.op g)) =
      SA.tensor.map (Prod.mkHom (𝟙 T) f) ≫ (SA.transpose T P Q).symm z ≫ g := by
  rw [uncurry_formula, uncurry_formula]
  have ht : Prod.mkHom (z ≫ HA.map (Prod.mkHom f.op g)) (𝟙 P') =
      Prod.mkHom z (𝟙 P') ≫ Prod.mkHom (HA.map (Prod.mkHom f.op g)) (𝟙 P') := by simp
  rw [ht, SA.tensor.map_comp, Category.assoc, evaluation_both]
  have ht' : Prod.mkHom z (𝟙 P') ≫ Prod.mkHom (𝟙 (HA.obj (op P, Q))) f =
      Prod.mkHom (𝟙 T) f ≫ Prod.mkHom z (𝟙 P) := by simp
  rw [← Category.assoc, ← Category.assoc, ← SA.tensor.map_comp, ht', SA.tensor.map_comp]
  simp only [Category.assoc]

private theorem uncurry_precomp (SA : CoefficientClosedStructure HA)
    {T T' P Q : A} (f : T' ⟶ T) (z : T ⟶ HA.obj (op P, Q)) :
    (SA.transpose T' P Q).symm (f ≫ z) =
      SA.tensor.map (Prod.mkHom f (𝟙 P)) ≫ (SA.transpose T P Q).symm z := by
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensorRight] using (SA.adjunction P).homEquiv_naturality_left_symm f z

-- Naturality requires only the tensor comparison and closed evaluation, not a site lift.
private theorem baseChange_naturality
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (P P' Q Q' : A) (f : P' ⟶ P) (g : Q ⟶ Q') :
    F.map (HA.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom SA SB F μ P' Q' =
      coefficientBaseChangeHom SA SB F μ P Q ≫
        HB.map (Prod.mkHom (F.map f).op (F.map g)) := by
  apply (SB.transpose _ _ _).symm.injective
  rw [uncurry_precomp, uncurry_naturality]
  change SB.tensor.map _ ≫ (SB.transpose _ _ _).symm (SB.transpose _ _ _ _) =
    SB.tensor.map _ ≫ (SB.transpose _ _ _).symm (SB.transpose _ _ _ _) ≫ _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← Category.assoc]
  have hn := μ.inv.naturality (Prod.mkHom (HA.map (Prod.mkHom f.op g)) (𝟙 P'))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [F.map_id] at hn
  rw [hn, Category.assoc, ← F.map_comp, evaluation_both]
  simp only [F.map_comp]
  have hn' := μ.inv.naturality (Prod.mkHom (𝟙 (HA.obj (op P, Q))) f)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn'
  rw [F.map_id] at hn'
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ F.map (SA.evaluation P Q) ≫ F.map g) hn'.symm

private theorem baseChange_transpose
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (T P Q : A) (f : SA.tensor.obj (T, P) ⟶ Q) :
    F.map (SA.transpose T P Q f) ≫ coefficientBaseChangeHom SA SB F μ P Q =
      SB.transpose (F.obj T) (F.obj P) (F.obj Q) (μ.inv.app (T, P) ≫ F.map f) := by
  apply (SB.transpose _ _ _).symm.injective
  rw [uncurry_precomp, Equiv.symm_apply_apply]
  change SB.tensor.map _ ≫ (SB.transpose _ _ _).symm (SB.transpose _ _ _ _) = _
  rw [Equiv.symm_apply_apply, ← Category.assoc]
  have hn := μ.inv.naturality (Prod.mkHom (SA.transpose T P Q f) (𝟙 P))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [F.map_id] at hn
  rw [hn, Category.assoc, ← F.map_comp, ← uncurry_formula, Equiv.symm_apply_apply]

private theorem tensorComparison_inverse
    {C : Type c} [Category.{r} C] {HC : Cᵒᵖ × C ⥤ C}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (F : A ⥤ B) (G : B ⥤ C) (V : A ⥤ C)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SC.tensor)
    (τ : SA.tensor ⋙ V ≅ V.prod V ⋙ SC.tensor) (α : F ⋙ G ≅ V)
    (h : ∀ X Y : A,
      G.map (μ.hom.app (X, Y)) ≫ ν.hom.app (F.obj X, F.obj Y) ≫
        SC.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
      α.hom.app (SA.tensor.obj (X, Y)) ≫ τ.hom.app (X, Y)) (X Y : A) :
    ν.inv.app (F.obj X, F.obj Y) ≫ G.map (μ.inv.app (X, Y)) =
      SC.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) ≫
        τ.inv.app (X, Y) ≫ α.inv.app (SA.tensor.obj (X, Y)) := by
  let i := G.mapIso (μ.app (X, Y)) ≪≫ ν.app (F.obj X, F.obj Y)
  let j := α.app (SA.tensor.obj (X, Y)) ≪≫ τ.app (X, Y)
  have hi : i.hom ≫ SC.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) = j.hom := by
    simpa only [i, j, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] using h X Y
  have hinv : i.inv = SC.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) ≫ j.inv := by
    apply (cancel_epi i.hom).mp
    rw [Iso.hom_inv_id, ← Category.assoc, hi, Iso.hom_inv_id]
  exact hinv

private theorem baseChange_evaluation
    {C : Type c} [Category.{r} C] {HC : Cᵒᵖ × C ⥤ C}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (F : A ⥤ B) (G : B ⥤ C) (V : A ⥤ C)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SC.tensor)
    (τ : SA.tensor ⋙ V ≅ V.prod V ⋙ SC.tensor) (α : F ⋙ G ≅ V)
    (h : ∀ X Y : A,
      G.map (μ.hom.app (X, Y)) ≫ ν.hom.app (F.obj X, F.obj Y) ≫
        SC.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
      α.hom.app (SA.tensor.obj (X, Y)) ≫ τ.hom.app (X, Y)) (P Q : A) :
    G.map (coefficientBaseChangeHom SA SB F μ P Q) ≫
        coefficientBaseChangeHom SB SC G ν (F.obj P) (F.obj Q) =
      α.hom.app (HA.obj (op P, Q)) ≫ coefficientBaseChangeHom SA SC V τ P Q ≫
        HC.map (Prod.mkHom ((α.hom.app P).op) (α.inv.app Q)) := by
  apply (SC.transpose _ _ _).symm.injective
  rw [uncurry_precomp, uncurry_precomp, uncurry_naturality]
  change SC.tensor.map _ ≫ (SC.transpose _ _ _).symm (SC.transpose _ _ _ _) =
    SC.tensor.map _ ≫ (SC.tensor.map _ ≫
      (SC.transpose _ _ _).symm (SC.transpose _ _ _ _) ≫ _)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hn := ν.inv.naturality
    (Prod.mkHom (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 (F.obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [G.map_id] at hn
  rw [← Category.assoc, hn, Category.assoc, ← G.map_comp, ← uncurry_formula]
  simp only [coefficientBaseChangeHom, Equiv.symm_apply_apply, G.map_comp]
  rw [← Category.assoc, tensorComparison_inverse SA SB SC F G V μ ν τ α h]
  have hα := α.inv.naturality (SA.evaluation P Q)
  dsimp only [Functor.comp_map] at hα
  have ht :
      SC.tensor.map (Prod.mkHom (α.hom.app (HA.obj (op P, Q))) (𝟙 (G.obj (F.obj P)))) ≫
          SC.tensor.map (Prod.mkHom (𝟙 (V.obj (HA.obj (op P, Q)))) (α.hom.app P)) =
        SC.tensor.map (Prod.mkHom (α.hom.app (HA.obj (op P, Q))) (α.hom.app P)) := by
    rw [← SC.tensor.map_comp]
    congr 1
    ext <;> simp
  simp only [Category.assoc]
  rw [← hα]
  simp only [← Category.assoc]
  rw [ht]

end ClosedNaturality

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem coefficientDerivedSystemTensors_exist :
    ∃ T : CoefficientDerivedSystemTensors l E W,
      CoefficientDerivedSystemTensorCoherence l E W T := by
  classical
  obtain ⟨SA, TA, βA, cA⟩ := ringedDerived_closed_symmetric_monoidal.{t+1, t, u}
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)
  obtain ⟨SB, TB, βB, cB⟩ := ringedDerived_closed_symmetric_monoidal.{t+1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  have hn (n : ℕ) := ringedDerived_closed_symmetric_monoidal.{t+1, t, u}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)
  choose Sn Tn βn cn using hn
  refine ⟨{
    integralClosed := SA
    integralTensorModel := TA
    systemClosed := SB
    systemTensorModel := TB
    finiteClosed := Sn
    finiteTensorModel := Tn }, ?_⟩
  exact ⟨⟨βA, cA⟩, ⟨βB, cB⟩, fun n ↦ ⟨βn n, cn n⟩⟩

private theorem coefficientSequence_isIso_iff_evaluations
    {M N : coefficientSequenceDerived l E W} (f : M ⟶ N) :
    IsIso f ↔ ∀ n : ℕ, IsIso ((coefficientSequenceDerivedEvaluation l E W n).map f) := by
  constructor
  · intro hf n
    let := hf
    infer_instance
  · intro hf
    obtain ⟨D⟩ := SemilinearSections.semilinearDerivedSections.{t+1, t, u}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W)
    exact D.systems.detects f hf

private theorem fiberHom_eq_baseChange
    (R : CoefficientDerivedSystemReduction l E W)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors)
    (H : CoefficientNormalizedInternalHomFibers l E W R Q)
    (M N : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N) (n : ℕ) :
    (H.fiberHom M N hM hN n).hom =
      coefficientBaseChangeHom R.systemClosed (R.finiteClosed n)
        (coefficientSequenceDerivedEvaluation l E W n) (R.evaluationTensor n) M N := by
  apply ((R.finiteClosed n).transpose _ _ _).symm.injective
  rw [uncurry_formula, ← H.fiber_evaluation M N hM hN n]
  exact ((R.finiteClosed n).transpose _ _ _).symm_apply_apply _ |>.symm

/-- Construct the normalized fiber calculus and the simultaneous sections/limit models.
The enriched isomorphism field is supplied by the proved closed-adjunction calculation;
this assertion does not include gamma's projection, naturality, Hom-zero or composition
identities. It also records ordinary sections projections and the finite scalar
H-zero normalization, which are separate from the enriched gamma equations.
Source: Stacks 06YS, 06YY, 07A4, 07A6, 08J9, 0A95, 0D6E, 0941;
node lem-coef-derived-system-evaluation-calculus, construction steps 1--5
(blueprint: lem-coef-derived-system-resolution-models).

Proof:
1. Apply SequenceProjection.derivedAdjunction and pushforwardLimitProjections to
   the completed coefficient sheaf and its actual quotient tower. Transport across
   strictSystemSequenceEquivalence and the exact scalar-restriction comparison.
   Uniqueness of right derived functors identifies their direct image with the
   specified coefficientSequenceLimit. Transport the adjunction across that isomorphism.
   The projection normalizations give unit_projection and counit_projection. The
   left-derived comparison on one flat-term K-flat representative gives reductionModel.
2. Apply ringedDerived_closed_symmetric_monoidal on the integral, sequence and finite
   ringed sites. Use its tensor models and the canonical tensor-pullback theorem for
   reduction, scalar extension and evaluation. On the same representatives their
   squares are the ordinary pure-tensor squares. The already fixed scalar/evaluation
   comparisons and their uniqueness identify them with coefficientScalarTensorIso and
   coefficientEvaluationTensorIso. The strict quotient maps give the reduction square.
   Iterating scalar extension identifies each reduction transition-adjoint with the
   associativity isomorphism, so every reduced object is normalized. Apply the same
   argument to each finite quotient, retaining the ordinary 1 tensor x unit and the
   localization counit, to obtain quotientCalculus with its three normalizations.
3. Apply semilinearDerivedSections to the actual ring sequence. Its finite-prefix
   adjunction identifies Hom on normalized systems with finite internal Hom, with its
   evaluation and naturality equations. Uniqueness of the closed transpose identifies
   its actual transitions with the finite quotient comparison and the normalization
   isomorphisms. The same transpose calculation for the sequence projection gives beta
   and beta_evaluation; ringedPullbackHomEvaluationComparison gives its evaluation,
   transpose and composition equations. Componentwise acyclicity gives joint detection
   of derived isomorphisms.
4. Use coefficientSequenceGlobalSectionsEvaluation and its normalized derived pairs.
   Transport the ordinary sections functors by their identity-on-sections isomorphisms
   to coefficientOrdinarySections. Uniqueness of the universal derived comparisons
   gives scalarSections and systemSectionsEvaluation with their model equations.
   Define globalEvaluation as systemSectionsEvaluation followed by sections of fiberHom.
   This makes globalEvaluation_model its defining composite, without an arbitrary lift.
5. Apply coefficientSequenceSectionsLimitComparison to those same derived pairs.
   Identify its limit functors with the prescribed coefficientConstantTowerLimit and
   coefficientMappingLimit by their universal derived comparison units. The ordinary
   comparison is coefficientSectionsLimitIso because both commute with every ordinary
   projection. Whisker by the exact sequence restriction. The resulting comparison is
   kappa below; the theorem's resolution equation is exactly globalLimit_model after
   these transports. All scalar-section transports retain their ordinary section
   formulas and universal-unit equations. Package these comparisons and equations as D.
   Retain its actual-projection clause as sections_projection for arbitrary M.
   Normalize finite closed transposition by the Hom-complex evaluation on the chosen
   K-flat/K-injective pair. On degree-zero cocycle classes the finite enriched scalar
   comparison is the extension/restriction Hom bijection; the coefficientHomZeroEquiv
   normalizations give scalar_hom_zero. These are the two ProjectionModels equations.
   Insert the already proved coefficientClosedEnriched_isIso as the enriched field.
No projection identity for gamma, composition identity, reconstruction isomorphism, or
invertibility of beta on arbitrary inputs is used in this construction. -/
theorem coefficientDerivedSystemResolutionModels :
    ∃ (F : CoefficientDerivedSystemFibers l E W)
      (κ : coefficientSequenceLimit l E W ⋙ coefficientIntegralSections l E W ≅
        coefficientSequenceDerivedRestriction l E W ⋙
          (coefficientTowerSections l E W).rightDerivedFunctor ⋙
            coefficientMappingLimit.{max u (t+1)}),
      let S : CoefficientDerivedSystemCalculus l E W :=
        { toCoefficientDerivedSystemFibers := F
          enriched_isIso := fun P N _ ↦ coefficientClosedEnriched_isIso
            F.integralClosed F.systemClosed F.reduction F.adjunction F.reductionTensor P N
          globalLimit := κ }
      ∃ D : CoefficientDerivedSystemResolutionCoherence l E W S,
        CoefficientDerivedSystemProjectionModels l E W S D := by
  classical
  obtain ⟨T, hT⟩ := coefficientDerivedSystemTensors_exist l E W
  obtain ⟨R, hRT, hR, hF, hE, hRE, ⟨Q⟩⟩ := coefficientNormalizedReductionModels l E W T
  have hTR : CoefficientDerivedSystemTensorCoherence l E W R.toCoefficientDerivedSystemTensors :=
    hRT.symm ▸ hT
  obtain ⟨H⟩ := coefficientNormalizedInternalHomFibers l E W R hTR hR hF hE Q
  obtain ⟨C⟩ := coefficientDerivedSectionsNormalization l E W R hF
  let F : CoefficientDerivedSystemFibers l E W :=
    { toCoefficientDerivedSystemReduction := R
      finite_tensor_coherence := by
        unfold CoefficientDerivedSystemTensorCoherence at hTR
        exact hTR.2.2
      reductionTensor_normalization := hR
      finiteTensor_normalization := hF
      evaluationTensor_normalization := hE
      reductionTensor_evaluation := hRE
      quotientCalculus := Q
      reduction_compatible :=
        { naturality := fun P Q P' Q' f g ↦ baseChange_naturality
            R.integralClosed R.systemClosed R.reduction R.reductionTensor P P' Q Q' f g
          transpose := baseChange_transpose
            R.integralClosed R.systemClosed R.reduction R.reductionTensor
          composition := H.reduction_composition }
      finite_compatible := fun n ↦
        { naturality := fun P Q P' Q' f g ↦ baseChange_naturality
            R.integralClosed (R.finiteClosed n) (coefficientFiniteDerivedExtension l E W n)
            (R.finiteTensor n) P P' Q Q' f g
          transpose := baseChange_transpose R.integralClosed (R.finiteClosed n)
            (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n)
          composition := H.finite_composition n }
      fiberHom := H.fiberHom
      fiber_evaluation := H.fiber_evaluation
      fiber_naturality := by
        intro M N M' N' hM hN hM' hN' f g n
        rw [fiberHom_eq_baseChange l E W R Q H M' N' hM' hN' n,
          fiberHom_eq_baseChange l E W R Q H M N hM hN n]
        exact baseChange_naturality R.systemClosed (R.finiteClosed n)
          (coefficientSequenceDerivedEvaluation l E W n) (R.evaluationTensor n) M M' N N' f g
      fiber_transition := H.fiber_transition
      beta_evaluation := by
        intro P Q n
        rw [fiberHom_eq_baseChange l E W R _ H _ _
          (R.reduction_normalized P) (R.reduction_normalized Q) n]
        exact baseChange_evaluation R.integralClosed R.systemClosed (R.finiteClosed n)
          R.reduction (coefficientSequenceDerivedEvaluation l E W n)
          (coefficientFiniteDerivedExtension l E W n) R.reductionTensor (R.evaluationTensor n)
          (R.finiteTensor n) (R.reductionEvaluation n) (fun X Y ↦ hRE X Y n) P Q
      isIso_iff_evaluations := coefficientSequence_isIso_iff_evaluations l E W
      globalEvaluation := fun M N hM hN n ↦
        (C.systemSectionsEvaluation n).app
            ((coefficientSequenceInternalHom l E W).obj (op M, N)) ≪≫
          (coefficientFiniteSections l E W n).mapIso (H.fiberHom M N hM hN n) }
  refine ⟨F, C.globalLimit, ?_⟩
  let S : CoefficientDerivedSystemCalculus l E W :=
    { toCoefficientDerivedSystemFibers := F
      enriched_isIso := fun P N _ ↦ coefficientClosedEnriched_isIso
        F.integralClosed F.systemClosed F.reduction F.adjunction F.reductionTensor P N
      globalLimit := C.globalLimit }
  let D : CoefficientDerivedSystemResolutionCoherence l E W S :=
    { toCoefficientDerivedSystemScalarCoherence := C.toCoefficientDerivedSystemScalarCoherence
      systemTensorCoherence := hTR.2.1
      systemSectionsEvaluation := C.systemSectionsEvaluation
      globalEvaluation_model := fun _ _ _ _ _ ↦ rfl
      globalLimit_model := C.globalLimit_model }
  exact ⟨D, { sections_projection := C.sections_projection, scalar_hom_zero := C.scalar_hom_zero }⟩

end WeilConjectures
