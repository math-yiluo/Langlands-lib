/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRepresentativeRoos
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoosComparisonSupplement
import all WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRRoosFiniteReduction
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Effectivity of the strict finite-operation towers

Source: Stacks Tags 099M and 099N(5); Bhatt--Scholze, Lemmas 3.5.4--3.5.7
(blueprint: lem-pur-integral-operation-roos-effectivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical projection of the strict Roos complex to its nth tower term.
Source: Stacks Tag 08TC (blueprint: lem-pur-integral-operations-preserve-constructible).
It is the first mapping-cocone projection followed by the nth product projection. -/
def integralOperationRoosProjection (W : AlgebraicGeometry.Scheme.{u})
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj (integralOperationsRoos T) ⟶ DerivedCategory.Q.obj (T.obj (op n)) :=
  DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism (K := fun m ↦ T.obj (op m))
        (integralOperationsTowerStep T)) ≫ Pi.π (fun m ↦ T.obj (op m)) n)

/-- The finite pullback of the nth reduction of a good integral representative.
The coefficient pullback is the canonical pro-etale inverse image with its
constant-ring action; exactness makes this compute `f⁻¹(K tensor^L A_(n+1))`.
Source: Bhatt--Scholze, Lemma 6.5.9(5); Stacks Tag 099N(5)
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralPullbackFiniteComplex {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :=
  ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((unrestrictedIntegralFiniteComplex l E Y n).obj P)

/-- The finite derived tensor on the two reduced K-flat representatives.
This is the recorded total tensor, before restricting its scalar action to the completion.
Source: Bhatt--Scholze, Lemma 6.5.5; Stacks Tag 09BQ
(blueprint: lem-pur-integral-operations-preserve-constructible). -/
def integralTensorFiniteComplex (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :=
  (Functor.uncurry.obj
    ((MonoidalCategory.curriedTensor
      (integralOperationsFiniteModules l E W n)).map₂CochainComplex)).obj
        (((unrestrictedIntegralFiniteComplex l E W n).obj P),
          ((unrestrictedIntegralFiniteComplex l E W n).obj Q))

local instance (priority := 4000) operationSiteSmall (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _
local instance (priority := 4000) operationSequenceSmall (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × W.ProEt) := essentiallySmallSelf.{u} _
private def effectivityTestDatum (p : ℕ) (hp : p.Prime) : FiniteFieldDatum.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_refl 1
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }

private def operationDerivedAdjunction (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    scalarReductionDerivedExtension.{u, u} l E W n ⊣
      scalarReductionDerivedRestriction.{u, u} l E W n :=
  (derivedScalarExtensionRestrictionAdjunction.{u, u} l E W n).choose

private def operationOrdinaryAdjunction (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    scalarReductionExtension.{u, u} l E W n ⊣ scalarReductionRestriction.{u, u} l E W n :=
  (scalarReductionExtension_adjunction.{u, u} l E W n).choose

attribute [local irreducible] operationDerivedAdjunction operationOrdinaryAdjunction

private def operationFiniteFactors (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    DerivedCategory.Q ⋙ scalarReductionDerivedRestriction.{u, u} l E W n ≅
      (scalarReductionRestriction.{u, u} l E W n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  (scalarReductionRestriction.{u, u} l E W n).mapDerivedCategoryFactors

private def operationEvaluationFactors (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    DerivedCategory.Q ⋙ coefficientSequenceDerivedEvaluation.{u, u} l E W n ≅
      (coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  (coefficientSequenceEvaluation.{u, u} l E W n).mapDerivedCategoryFactors

private def operationSequenceFactors (W : AlgebraicGeometry.Scheme.{u}) :
    DerivedCategory.Q ⋙ coefficientSequenceDerivedRestriction.{u, u} l E W ≅
      (coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  (coefficientSequenceRestriction.{u, u} l E W).mapDerivedCategoryFactors

private theorem adjointProductIso
    {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {K L : A} (b : K ≅ L) {X Y : B} (a : Y ≅ X)
    {V : ℕ → A} [HasProduct V] (n : ℕ) (t : V n ≅ G.obj Y)
    (s : L ⟶ G.obj X) (ps : ∀ k : ℕ, L ⟶ V k)
    (hs : ps n = s ≫ G.map a.inv ≫ t.inv)
    (hi : IsIso ((adj.homEquiv K Y).symm
      ((b.hom ≫ Pi.lift ps) ≫ Pi.π V n ≫ t.hom))) :
    IsIso ((adj.homEquiv K X).symm (b.hom ≫ s)) := by
  have he : (b.hom ≫ Pi.lift ps) ≫ Pi.π V n ≫ t.hom =
      (b.hom ≫ s) ≫ G.map a.inv := by
    simp only [Category.assoc, Pi.lift_comp_π_assoc, hs, Iso.inv_hom_id, Category.comp_id]
  rw [he, adj.homEquiv_naturality_right_symm] at hi
  let := hi
  exact IsIso.of_isIso_comp_right _ a.inv

private theorem adjointRealization
    {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {L M K : A} {N N' : B} {Z₀ Z : A}
    (r : L ≅ M) (e : K ≅ M) (p : L ⟶ G.obj N) (q₀ : M ⟶ Z₀) (q₁ : Z₀ ⟶ Z)
    (v : N ≅ N') (j : G.obj N' ≅ Z)
    (hr : r.hom ≫ q₀ ≫ q₁ = p ≫ G.map v.hom ≫ j.hom)
    (hi : IsIso ((adj.homEquiv K N).symm ((e ≪≫ r.symm).hom ≫ p))) :
    IsIso ((adj.homEquiv K N').symm (e.hom ≫ q₀ ≫ q₁ ≫ j.inv)) := by
  have heq : e.hom ≫ q₀ ≫ q₁ ≫ j.inv = (e ≪≫ r.symm).hom ≫ p ≫ G.map v.hom := by
    calc
      _ = e.hom ≫ r.inv ≫ (r.hom ≫ q₀ ≫ q₁) ≫ j.inv := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = _ := by
        rw [hr]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
          Iso.trans_hom, Iso.symm_hom]
  rw [heq, ← Category.assoc, adj.homEquiv_naturality_right_symm]
  let := hi
  infer_instance

private theorem triangleVertexIso
    {A : Type*} [Category A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {K L P : A} (b : K ≅ L) (p : L ⟶ P) (t : P ⟶ P)
    (δ : P ⟶ (shiftFunctor A (1 : ℤ)).obj L)
    (h : Pretriangulated.Triangle.mk p t δ ∈ distTriang A) :
    Pretriangulated.Triangle.mk (b.hom ≫ p) t
      (δ ≫ (shiftFunctor A (1 : ℤ)).map b.inv) ∈ distTriang A := by
  apply Pretriangulated.isomorphic_distinguished _ h
  refine Pretriangulated.Triangle.isoMk _ _ b (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact Category.comp_id _
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change (δ ≫ (shiftFunctor A (1 : ℤ)).map b.inv) ≫
        (shiftFunctor A (1 : ℤ)).map b.hom = 𝟙 _ ≫ δ
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

attribute [local irreducible] scalarReductionDerivedExtension
  coefficientSequenceProjection coefficientSequenceLimit
private theorem normalizedLimit (W : AlgebraicGeometry.Scheme.{u})
    (N : coefficientSequenceDerived.{u, u} l E W)
    (hN : IsNormalizedCoefficientSequence.{u, u} l E W N)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (b : K ≅ (coefficientSequenceLimit.{u, u} l E W).obj N) :
    IsSfDerivedComplete l E W K ∧ ∀ n : ℕ,
      IsIso (((operationDerivedAdjunction l E W n).homEquiv K
        ((coefficientSequenceDerivedEvaluation.{u, u} l E W n).obj N)).symm
        (b.hom ≫ (coefficientSequenceProjection.{u, u} l E W n).app N)) := by
  have H : ∃ p : ℕ, l + 1 ≤ p ∧ p.Prime := Nat.exists_infinite_primes (l + 1)
  rcases H with ⟨p, hpl, hp⟩
  let D := effectivityTestDatum p hp
  have hlp : l ≠ D.p := by change l ≠ p; omega
  have H := coefficientSequence_roosModel.{0, u, u} l E W D hlp N hN
  rcases H with ⟨T, a, hprod, δ, hδ⟩
  let := hprod
  let p₀ := Pi.lift (fun n : ℕ ↦ (coefficientSequenceProjection.{u, u} l E W n).app N ≫
    (normalizedDVRResCompleted.{0, u, u} l E W D hlp n).map (a n).inv ≫
    (T.evaluationIso n).inv)
  let q := b.hom ≫ p₀
  let ε := δ ≫ (shiftFunctor _ (1 : ℤ)).map b.inv
  have hε : IsDerivedLimitTriangle
      (fun n ↦ (normalizedDVRTowerTransition.{0, u, u} l E W D hlp n.le_succ).app
        T.tower) K q ε := by
    exact triangleVertexIso b p₀ _ δ hδ
  have hc := normalizedDVRTower_effectivity.{0, u, u} l E W D hlp T K q ε hε
  refine ⟨(sfDerivedComplete_iff_legacy.{u, 0} l E W D hlp K).2 hc.2.2, ?_⟩
  intro n
  let adj : scalarReductionDerivedExtension l E W n ⊣
      normalizedDVRResCompleted l E W D hlp n :=
    operationDerivedAdjunction l E W n
  have hi := normalizedDVRRoos_finite_reduction.{0, u, u} l E W D hlp T K q ε hε n adj
  have hs : (coefficientSequenceProjection.{u, u} l E W n).app N ≫
      (normalizedDVRResCompleted.{0, u, u} l E W D hlp n).map (a n).inv ≫
      (T.evaluationIso n).inv =
      (coefficientSequenceProjection.{u, u} l E W n).app N ≫
        (normalizedDVRResCompleted.{0, u, u} l E W D hlp n).map (a n).inv ≫
        (T.evaluationIso n).inv := rfl
  have hfinal := adjointProductIso adj b (a n)
    (V := fun k : ℕ ↦ (normalizedDVRTowerEvaluation l E W D hlp k).obj T.tower)
    n (T.evaluationIso n)
    ((coefficientSequenceProjection l E W n).app N)
    (fun k : ℕ ↦ (coefficientSequenceProjection l E W k).app N ≫
      (normalizedDVRResCompleted l E W D hlp k).map (a k).inv ≫
      (T.evaluationIso k).inv) hs hi
  exact hfinal

attribute [local semireducible] coefficientSequenceLimit
attribute [local implicit_reducible] coefficientSequenceLimit
  coefficientConstantTowerEvaluation coefficientFiniteDerivedRestriction
attribute [local irreducible] coefficientConstantTowerLimit coefficientSequenceRestriction
  coefficientRestrictedEvaluationIso coefficientConstantTowerProjection

private def operationEffective (W : AlgebraicGeometry.Scheme.{u})
    (T : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (F : ∀ n : ℕ, CochainComplex (scalarReductionTarget.{u, u} l E W n) ℤ)
    (j : ∀ n : ℕ, T.obj (op n) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj (F n))
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (e : K ≅ DerivedCategory.Q.obj (integralOperationsRoos T)) : Prop :=
    IsSfDerivedComplete l E W K ∧ ∀ n : ℕ,
      IsIso (((operationDerivedAdjunction l E W n).homEquiv K
        (DerivedCategory.Q.obj (F n))).symm
        (e.hom ≫ integralOperationRoosProjection l E W T n ≫ DerivedCategory.Q.map (j n).hom ≫
          (operationFiniteFactors l E W n).inv.app
            (F n)))

private theorem strictRealization (W : AlgebraicGeometry.Scheme.{u})
    (N : coefficientSequenceDerived.{u, u} l E W)
    (hN : IsNormalizedCoefficientSequence.{u, u} l E W N)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
    (m : N ≅ DerivedCategory.Q.obj C)
    (T : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (F : ∀ n : ℕ, CochainComplex (scalarReductionTarget.{u, u} l E W n) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅ F n)
    (t : (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex
      (.up ℤ)).obj C).asFunctor ≅ T)
    (j : ∀ n : ℕ, T.obj (op n) ≅
      ((scalarReductionRestriction.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj (F n))
    (ht : ∀ n : ℕ, t.hom.app (op n) ≫ (j n).hom =
      (coefficientRestrictedComplexEvaluation.{u, u} l E W n).hom.app C ≫
        ((scalarReductionRestriction.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).map (κ n).hom)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (e : K ≅ DerivedCategory.Q.obj (integralOperationsRoos T)) :
    operationEffective l E W T F j K e := by
  unfold operationEffective
  let U := coefficientSequenceRestriction.{u, u} l E W
  let B := (U.mapHomologicalComplex (.up ℤ)).obj C
  have H := coefficientConstantTowerRoosComparison.{u, u} l E W
  rcases H with ⟨β, hβ⟩
  let γ : DerivedCategory.Q.obj (roosF.obj B) ≅
      DerivedCategory.Q.obj (integralOperationsRoos T) :=
    DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso t)
  let r : (coefficientSequenceLimit.{u, u} l E W).obj N ≅
      DerivedCategory.Q.obj (integralOperationsRoos T) :=
    (coefficientSequenceLimit.{u, u} l E W).mapIso m ≪≫
      (coefficientConstantTowerLimit.{u, u} l E W).mapIso
        ((operationSequenceFactors l E W).app C) ≪≫
      β.app B ≪≫ γ
  have hr (n : ℕ) : r.hom ≫ integralOperationRoosProjection l E W T n ≫
      DerivedCategory.Q.map (j n).hom =
      (coefficientSequenceProjection.{u, u} l E W n).app N ≫
        (scalarReductionDerivedRestriction.{u, u} l E W n).map
          ((coefficientSequenceDerivedEvaluation.{u, u} l E W n).map m.hom ≫
            (operationEvaluationFactors l E W n).hom.app C ≫
            DerivedCategory.Q.map (κ n).hom) ≫
        (operationFiniteFactors l E W n).hom.app (F n) := by
    have hγ : γ.hom ≫ integralOperationRoosProjection l E W T n =
        DerivedCategory.Q.map (roosEval B n) ≫ DerivedCategory.Q.map (t.hom.app (op n)) := by
      change DerivedCategory.Q.map (integralOperationsRoosFunctor.map t.hom) ≫
        DerivedCategory.Q.map (CochainComplex.mappingCocone.fst _ ≫ Pi.π _ n) =
        DerivedCategory.Q.map (roosEval B n) ≫ DerivedCategory.Q.map (t.hom.app (op n))
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact congrArg (fun z ↦ DerivedCategory.Q.map z) (towerRoos_naturality t.hom n)
    have hγj : γ.hom ≫ integralOperationRoosProjection l E W T n ≫
        DerivedCategory.Q.map (j n).hom =
        DerivedCategory.Q.map (roosEval B n) ≫
          DerivedCategory.Q.map ((coefficientRestrictedComplexEvaluation l E W n).hom.app C) ≫
          DerivedCategory.Q.map
            (((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
              (κ n).hom) := by
      erw [reassoc_of% hγ]
      have hj := congrArg (fun z ↦ DerivedCategory.Q.map z) (ht n)
      erw [Functor.map_comp, Functor.map_comp] at hj
      exact congrArg (fun z ↦ DerivedCategory.Q.map (roosEval B n) ≫ z) hj
    have hβ' : (β.app B).hom ≫ DerivedCategory.Q.map (roosEval B n) =
        (coefficientConstantTowerProjection.{u, u} l E W n).app (DerivedCategory.Q.obj B) ≫
          (coefficientConstantTowerEvaluationFactors.{u, u} l E W n).hom.app B := by
      rw [← hβ B n]
      change β.hom.app B ≫ (β.inv.app B ≫ _) = _
      exact β.hom_inv_id_app_assoc B _
    dsimp only [r, Iso.trans_hom, Functor.mapIso_hom]
    erw [Category.assoc, Category.assoc, Category.assoc]
    erw [hγj]
    erw [reassoc_of% hβ']
    erw [Category.assoc]
    erw [reassoc_of% (coefficientConstantTowerProjection.{u, u} l E W n).naturality
      ((operationSequenceFactors l E W).hom.app C)]
    erw [reassoc_of% (restrictedEvaluation_factors.{u, u} l E W C n)]
    have hn := projection_naturality
      (coefficientSequenceLimit.{u, u} l E W) (coefficientSequenceDerivedEvaluation.{u, u} l E W n)
      (scalarReductionDerivedRestriction.{u, u} l E W n) DerivedCategory.Q
      ((scalarReductionRestriction.{u, u} l E W n).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q)
      (coefficientSequenceProjection.{u, u} l E W n)
      (operationFiniteFactors l E W n).hom
      (M := N) (X := DerivedCategory.Q.obj C)
      (Z := ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj C)
      (Z' := F n) m.hom
      ((operationEvaluationFactors l E W n).hom.app C)
      (κ n).hom
      ((coefficientConstantTowerProjection.{u, u} l E W n).app
        (U.mapDerivedCategory.obj (DerivedCategory.Q.obj C)))
      ((coefficientRestrictedEvaluationIso.{u, u} l E W n).hom.app (DerivedCategory.Q.obj C))
      (by unfold coefficientSequenceProjection; rfl)
    erw [Category.assoc]
    exact hn
  have H := normalizedLimit l E W N hN K (e ≪≫ r.symm)
  rcases H with ⟨hc, hi⟩
  refine ⟨hc, ?_⟩
  intro n
  let adj := operationDerivedAdjunction l E W n
  let v := (coefficientSequenceDerivedEvaluation.{u, u} l E W n).mapIso m ≪≫
    (operationEvaluationFactors l E W n).app C ≪≫
    DerivedCategory.Q.mapIso (κ n)
  exact adjointRealization adj r e
    ((coefficientSequenceProjection.{u, u} l E W n).app N)
    (integralOperationRoosProjection l E W T n) (DerivedCategory.Q.map (j n).hom)
    v ((operationFiniteFactors l E W n).app (F n))
    (hr n) (hi n)
attribute [local irreducible] operationEffective

private theorem restrictionFull (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    (scalarReductionRestriction.{u, u} l E W n).Full := by
  let q := (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)
  have : Presheaf.IsLocallySurjective (AlgebraicGeometry.Scheme.ProEt.topology W) q.hom :=
    completedProjection_locallySurjective l E W n
  exact SheafOfModules.restriction_full q

private theorem restrictionFaithful (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    (scalarReductionRestriction.{u, u} l E W n).Faithful := by
  constructor
  intro M N f g h
  ext U x
  exact congrArg (fun z ↦ z.val.app U x) h

private theorem liftFiniteComparison (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
    (F : CochainComplex (scalarReductionTarget.{u, u} l E W n) ℤ)
    (z : (((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (.up ℤ)).obj C).asFunctor.obj (op n) ≅
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj F) :
    ∃ κ : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅ F,
      z.hom = (coefficientRestrictedComplexEvaluation l E W n).hom.app C ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map κ.hom := by
  let R := (scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)
  have := restrictionFull l E W n
  have := restrictionFaithful l E W n
  let κ := R.preimageIso (((coefficientRestrictedComplexEvaluation l E W n).app C).symm ≪≫ z)
  refine ⟨κ, ?_⟩
  change z.hom = (coefficientRestrictedComplexEvaluation l E W n).hom.app C ≫
    R.map (R.preimage (((coefficientRestrictedComplexEvaluation l E W n).app C).inv ≫ z.hom))
  rw [R.map_preimage]
  change z.hom = (coefficientRestrictedComplexEvaluation l E W n).hom.app C ≫
    ((coefficientRestrictedComplexEvaluation l E W n).inv.app C ≫ z.hom)
  exact ((coefficientRestrictedComplexEvaluation l E W n).hom_inv_id_app_assoc C z.hom).symm
attribute [local irreducible] SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom
private theorem unitStepDegree (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ) (i : ℤ) :
    (operationOrdinaryAdjunction l E W (n + 1)).unit.app (P.X i) ≫
      (unrestrictedTowerTransition l E W P n).f i =
      (operationOrdinaryAdjunction l E W n).unit.app (P.X i) := by
  unfold operationOrdinaryAdjunction
  have h := integralUnit_step.{0, u, u} l E W D hl P n
  erw [integralTowerTransition_eq, integralTowerUnit_eq, integralTowerUnit_eq] at h
  have hh := congrArg (fun z ↦ z.f i) h
  dsimp only [HomologicalComplex.comp_f, unrestrictedTowerUnit] at hh
  exact hh

private theorem rightMapMate
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ A} {F' : A ⥤ C} {G' : C ⥤ A}
    [G.Full] (adj : F ⊣ G) (adj' : F' ⊣ G') (H : C ⥤ B) (c : H ⋙ G ≅ G')
    (M : A) (v : G.obj (F.obj M) ⟶ G'.obj (F'.obj M))
    (hu : adj.unit.app M ≫ v = adj'.unit.app M) :
    G.map ((coefficientQuotientNatTrans adj adj' H c).app M) ≫
      c.hom.app (F'.obj M) = v := by
  let f : F.obj M ⟶ H.obj (F'.obj M) := G.preimage (v ≫ c.inv.app _)
  have hf : G.map f = v ≫ c.inv.app _ := G.map_preimage _
  have he : (coefficientQuotientNatTrans adj adj' H c).app M = f := by
    apply (adj.homEquiv M _).injective
    change adj.homEquiv M _ ((adj.homEquiv M _).symm _) = _
    rw [Equiv.apply_symm_apply, adj.homEquiv_unit, hf]
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z ↦ z ≫ c.inv.app _) hu)).symm
  rw [he, hf]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem rightMapChosen
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ A} {F' : A ⥤ C} {G' : C ⥤ A}
    [G.Full] (adj : F ⊣ G) (adj' : F' ⊣ G') (H : C ⥤ B) (c : H ⋙ G ≅ G')
    (τ : F ⟶ F' ⋙ H) (M : A)
    (he : τ.app M = (coefficientQuotientNatTrans adj adj' H c).app M)
    (v : G.obj (F.obj M) ⟶ G'.obj (F'.obj M))
    (hu : adj.unit.app M ≫ v = adj'.unit.app M) :
    G.map (τ.app M) ≫ c.hom.app (F'.obj M) = v := by
  rw [he]
  exact rightMapMate adj adj' H c M v hu

attribute [local irreducible] unrestrictedIntegralComplexFunctor
attribute [local irreducible] scalarReductionExtension coefficientQuotientNatTrans
  unrestrictedIntegralTransition coefficientOrdinaryQuotientComponent coefficientOrdinaryQuotient
private theorem reflEqTrans {C : Type*} [Category C] {A B : C}
    (h h' : A = B) : Iso.refl A ≪≫ eqToIso h = eqToIso h' := by
  rw [Iso.refl_trans]
private theorem restrictComp_eq
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (he : f ≫ g = h)
    (e : SheafOfModules.restrictScalars.{r} g ⋙ SheafOfModules.restrictScalars.{r} f =
      SheafOfModules.restrictScalars.{r} h) :
    restrictCompIso f g h he = eqToIso e := by
  unfold restrictCompIso normalizedDVRRestrictionCompIso
  exact reflEqTrans _ _

attribute [local irreducible] coefficientSequenceEvaluation coefficientSequenceTransition
  unrestrictedIntegralReductionExistence
private def complexComparison
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms C]
    (U : C ⥤ (ℕᵒᵖ ⥤ A)) (V : C ⥤ B) (G : B ⥤ A)
    [U.PreservesZeroMorphisms] [V.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (n : ℕᵒᵖ)
    (a : U ⋙ (evaluation ℕᵒᵖ A).obj n ≅ V ⋙ G)
    (K : CochainComplex C ℤ) :
    ((U.mapHomologicalComplex (.up ℤ)).obj K).asFunctor.obj n ≅
      (G.mapHomologicalComplex (.up ℤ)).obj ((V.mapHomologicalComplex (.up ℤ)).obj K) where
  hom :=
    { f := fun i ↦ a.hom.app (K.X i)
      comm' := fun i j _ ↦ (a.hom.naturality (K.d i j)).symm }
  inv :=
    { f := fun i ↦ a.inv.app (K.X i)
      comm' := fun i j _ ↦ (a.inv.naturality (K.d i j)).symm }
  hom_inv_id := by
    ext i
    exact a.hom_inv_id_app (K.X i)
  inv_hom_id := by
    ext i
    exact a.inv_hom_id_app (K.X i)

private theorem assembleObjectTowerIso
    {A : Type*} [Category A] [HasZeroMorphisms A]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (a : ∀ n : ℕ, C.asFunctor.obj (op n) ≅ T.obj (op n))
    (ha : ∀ n : ℕ, C.asFunctor.map (homOfLE (show n ≤ n + 1 from n.le_succ)).op ≫ (a n).hom =
      (a (n + 1)).hom ≫ T.map (homOfLE (show n ≤ n + 1 from n.le_succ)).op) :
    ∃ e : C.asFunctor ≅ T, ∀ n : ℕ, e.hom.app (op n) = (a n).hom := by
  let f : C.asFunctor ⟶ T := NatTrans.ofOpSequence (fun n ↦ (a n).hom) ha
  exact ⟨NatIso.ofComponents (fun n ↦ a n.unop) (fun g ↦ f.naturality g),
    fun _ ↦ rfl⟩

local instance (priority := 4000) operationScalarAdditive
    (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    (scalarReductionExtension l E W n).Additive := scalarReductionExtensionAdditive l E W n

private def evaluationComparison
    {A B C : Type*} [Category A] [Category B] [Category C]
    (U : C ⥤ (ℕᵒᵖ ⥤ A)) (V : C ⥤ B) (G : B ⥤ A) (n : ℕᵒᵖ)
    (a : U ⋙ (evaluation ℕᵒᵖ A).obj n ≅ V ⋙ G) (M : C) :
    (U.obj M).obj n ≅ G.obj (V.obj M) where
  hom := a.hom.app M
  inv := a.inv.app M
  hom_inv_id := a.hom_inv_id_app M
  inv_hom_id := a.inv_hom_id_app M

-- Literal endpoints keep scalar restriction from expanding coefficient actions
-- while comparing evaluation of a composite with successive evaluation.
private def compositeComponent
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : A ⥤ C) (H : C ⥤ B) (τ : F ⟶ G ⋙ H) (M : A) :
    F.obj M ⟶ H.obj (G.obj M) := τ.app M

private theorem quotientSquareComponent
    {A Bm Bn C : Type*} [Category A] [Category Bm] [Category Bn] [Category C]
    (Vm : C ⥤ Bm) (Vn : C ⥤ Bn) (Fm : A ⥤ Bm) (Fn : A ⥤ Bn) (H : Bn ⥤ Bm)
    (σ : Vm ⟶ Vn ⋙ H) (τ : Fm ⟶ Fn ⋙ H) (M : C) (N : A)
    (κm : Vm.obj M ⟶ Fm.obj N) (κn : Vn.obj M ⟶ Fn.obj N)
    (h : σ.app M ≫ H.map κn = κm ≫ τ.app N) :
    compositeComponent Vm Vn H σ M ≫ H.map κn =
      κm ≫ compositeComponent Fm Fn H τ N := by
  exact h

private theorem comparisonWithIso_f
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms C]
    (U : C ⥤ (ℕᵒᵖ ⥤ A)) (V : C ⥤ B) (G : B ⥤ A)
    [U.PreservesZeroMorphisms] [V.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (n : ℕᵒᵖ) (a : U ⋙ (evaluation ℕᵒᵖ A).obj n ≅ V ⋙ G)
    (K : CochainComplex C ℤ) (P : CochainComplex B ℤ)
    (κ : (V.mapHomologicalComplex (.up ℤ)).obj K ≅ P) (i : ℤ) :
    ((complexComparison U V G n a K ≪≫
      (G.mapHomologicalComplex (.up ℤ)).mapIso κ).hom).f i =
      (evaluationComparison U V G n a (K.X i)).hom ≫ G.map (κ.hom.f i) := by
  rfl

private noncomputable def operationEvaluationIso
    (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    coefficientSequenceRestriction l E W ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) ≅
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  eqToIso (coefficientSequenceRestriction_evaluation l E W n)

attribute [local irreducible] operationEvaluationIso

private def operationEvaluationAt (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (M : coefficientSequenceModules l E W) :
    ((coefficientSequenceRestriction l E W).obj M).obj (op n) ≅
      (scalarReductionRestriction l E W n).obj ((coefficientSequenceEvaluation l E W n).obj M) :=
  evaluationComparison (coefficientSequenceRestriction l E W)
    (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n)
    (op n) (operationEvaluationIso l E W n) M

/-- Keep the composite-restriction comparison behind its literal functor endpoints. -/
private noncomputable def operationRestrictionIso
    (W : AlgebraicGeometry.Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    normalizedDVRModuleRes l E W h ⋙ scalarReductionRestriction l E W m ≅
      scalarReductionRestriction l E W n :=
  eqToIso (coefficientRestrictionComp l E W h)

private theorem operationRestrictionIso_eq
    (W : AlgebraicGeometry.Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    operationRestrictionIso l E W m n h =
      eqToIso (coefficientRestrictionComp l E W h) := rfl

attribute [local irreducible] operationRestrictionIso

private def restrictionComparison
    {A B C : Type*} [Category A] [Category B] [Category C]
    (G : B ⥤ A) (G' : C ⥤ A) (H : C ⥤ B) (c : H ⋙ G ≅ G') (N : C) :
    G.obj (H.obj N) ≅ G'.obj N where
  hom := c.hom.app N
  inv := c.inv.app N
  hom_inv_id := c.hom_inv_id_app N
  inv_hom_id := c.inv_hom_id_app N

private theorem restrictionComparison_hom
    {A B C : Type*} [Category A] [Category B] [Category C]
    (G : B ⥤ A) (G' : C ⥤ A) (H : C ⥤ B) (c : H ⋙ G ≅ G') (N : C) :
    (restrictionComparison G G' H c N).hom = c.hom.app N := by
  rfl

private theorem restrictionSquareAllComponents
    {A Bm Bn : Type*} [Category A] [Category Bm] [Category Bn]
    (Fm : A ⥤ Bm) (Fn : A ⥤ Bn) (Gm : Bm ⥤ A) (Gn : Bn ⥤ A) (H : Bn ⥤ Bm)
    (c : H ⋙ Gm ≅ Gn) (τ : Fm ⟶ Fn ⋙ H) (N : A)
    (v : Gm.obj (Fm.obj N) ⟶ Gn.obj (Fn.obj N))
    (h : Gm.map (τ.app N) ≫ c.hom.app (Fn.obj N) = v) :
    Gm.map (compositeComponent Fm Fn H τ N) ≫
      (restrictionComparison Gm Gn H c (Fn.obj N)).hom = v := by
  exact h

private theorem mappedQuotientSquareAllComponents
    {A Bm Bn C : Type*} [Category A] [Category Bm] [Category Bn] [Category C]
    (Vm : C ⥤ Bm) (Vn : C ⥤ Bn) (Fm : A ⥤ Bm) (Fn : A ⥤ Bn)
    (Gm : Bm ⥤ A) (H : Bn ⥤ Bm)
    (σ : Vm ⟶ Vn ⋙ H) (τ : Fm ⟶ Fn ⋙ H) (M : C) (N : A)
    (κm : Vm.obj M ⟶ Fm.obj N) (κn : Vn.obj M ⟶ Fn.obj N)
    (h : σ.app M ≫ H.map κn = κm ≫ τ.app N) :
    Gm.map (compositeComponent Vm Vn H σ M) ≫ Gm.map (H.map κn) =
      Gm.map κm ≫ Gm.map (compositeComponent Fm Fn H τ N) := by
  rw [← Gm.map_comp, ← Gm.map_comp]
  exact congrArg (fun f ↦ Gm.map f) (quotientSquareComponent Vm Vn Fm Fn H σ τ M N κm κn h)

private def operationRestrictionAt (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (N : scalarReductionTarget l E W n) :
    (scalarReductionRestriction l E W m).obj ((normalizedDVRModuleRes l E W h).obj N) ≅
      (scalarReductionRestriction l E W n).obj N :=
  restrictionComparison (scalarReductionRestriction l E W m)
    (scalarReductionRestriction l E W n) (normalizedDVRModuleRes l E W h)
    (operationRestrictionIso l E W m n h) N

private theorem operationRestrictionAt_eq (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (N : scalarReductionTarget l E W n) :
    operationRestrictionAt l E W m n h N =
      restrictionComparison (scalarReductionRestriction l E W m)
        (scalarReductionRestriction l E W n) (normalizedDVRModuleRes l E W h)
        (operationRestrictionIso l E W m n h) N := by
  rfl

private theorem restrictionComponentHom (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (N : scalarReductionTarget l E W n) :
    (operationRestrictionAt l E W m n h N).hom =
      (operationRestrictionIso l E W m n h).hom.app N := by
  rw [operationRestrictionAt_eq]
  exact restrictionComparison_hom (scalarReductionRestriction l E W m)
    (scalarReductionRestriction l E W n) (normalizedDVRModuleRes l E W h)
    (operationRestrictionIso l E W m n h) N

private theorem componentGeneral (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource l E W) :
    coefficientOrdinaryQuotientComponent l E W h M =
      (coefficientQuotientNatTrans
        (operationOrdinaryAdjunction l E W m)
        (operationOrdinaryAdjunction l E W n)
        (normalizedDVRModuleRes l E W h)
        (eqToIso (coefficientRestrictionComp l E W h))).app M := by
  unfold operationOrdinaryAdjunction
  unfold coefficientOrdinaryQuotientComponent
  rfl
private theorem ordinaryQuotientFormula (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource l E W) :
    (coefficientOrdinaryQuotient l E W h).app M =
      (coefficientQuotientNatTrans
        (operationOrdinaryAdjunction l E W m)
        (operationOrdinaryAdjunction l E W n)
        (normalizedDVRModuleRes l E W h)
        (eqToIso (coefficientRestrictionComp l E W h))).app M := by
  have hq : coefficientOrdinaryQuotient l E W h =
      (coefficientOrdinaryQuotient_exists l E W h).choose := by
    unfold coefficientOrdinaryQuotient
    rfl
  exact (congrArg (fun τ ↦ τ.app M) hq).trans
    (((coefficientOrdinaryQuotient_exists l E W h).choose_spec.1 M).trans
      (componentGeneral l E W m n h M))

private theorem ordinaryQuotientComparisonFormula (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource l E W) :
    (coefficientOrdinaryQuotient l E W h).app M =
      (coefficientQuotientNatTrans
        (operationOrdinaryAdjunction l E W m)
        (operationOrdinaryAdjunction l E W n)
        (normalizedDVRModuleRes l E W h)
        (operationRestrictionIso l E W m n h)).app M := by
  exact (ordinaryQuotientFormula l E W m n h M).trans
    (congrArg (fun c ↦ (coefficientQuotientNatTrans
      (operationOrdinaryAdjunction l E W m)
      (operationOrdinaryAdjunction l E W n)
      (normalizedDVRModuleRes l E W h) c).app M)
      (operationRestrictionIso_eq l E W m n h).symm)

private def ordinaryTowerPresentation (W : AlgebraicGeometry.Scheme.{u})
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ) :
    Functor.ofOpSequence (X := fun n ↦ unrestrictedTowerComplex l E W n P)
        (unrestrictedTowerTransition l E W P) ≅
      Functor.ofOpSequence
        (X := fun n ↦ (unrestrictedIntegralComplexFunctor l E W n).obj P)
        (fun n ↦ (unrestrictedIntegralTransition l E W n).app P) := by
  apply eqToIso
  unfold unrestrictedTowerComplex unrestrictedTowerFiniteComplex unrestrictedTowerTransition
    unrestrictedIntegralComplexFunctor
  rfl

private def sequenceEvaluationIso
    {A B : Type*} [Category A] [Category B]
    (F : ℕ → A ⥤ B) (τ : ∀ n, F (n + 1) ⟶ F n) (P : A) :
    Functor.ofOpSequence (X := fun n ↦ (F n).obj P) (fun n ↦ (τ n).app P) ≅
      (Functor.ofOpSequence τ).flip.obj P := by
  let S := Functor.ofOpSequence (X := fun n ↦ (F n).obj P) (fun n ↦ (τ n).app P)
  let T := (Functor.ofOpSequence τ).flip.obj P
  let a (n : ℕ) : S.obj (op n) ≅ T.obj (op n) := Iso.refl _
  have h (n : ℕ) : S.map (homOfLE (show n ≤ n + 1 from n.le_succ)).op ≫ (a n).hom =
      (a (n + 1)).hom ≫ T.map (homOfLE (show n ≤ n + 1 from n.le_succ)).op := by
    dsimp only [S, T, a, Iso.refl_hom, Functor.flip_obj_map]
    rw [Functor.ofOpSequence_map_homOfLE_succ,
      Functor.ofOpSequence_map_homOfLE_succ]
    erw [Category.comp_id, Category.id_comp]
  let z : S ⟶ T := NatTrans.ofOpSequence (fun n ↦ (a n).hom) h
  exact NatIso.ofComponents (fun n ↦ a n.unop) (fun g ↦ z.naturality g)

private theorem ordinaryRestrictedQuotient (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource.{u, u} l E W)
    (v : (scalarReductionRestriction l E W m).obj
        ((scalarReductionExtension l E W m).obj M) ⟶
      (scalarReductionRestriction l E W n).obj ((scalarReductionExtension l E W n).obj M))
    (hu : (operationOrdinaryAdjunction l E W m).unit.app M ≫ v =
      (operationOrdinaryAdjunction l E W n).unit.app M) :
    (scalarReductionRestriction l E W m).map
        ((coefficientOrdinaryQuotient l E W h).app M) ≫
      (operationRestrictionIso l E W m n h).hom.app
        ((scalarReductionExtension l E W n).obj M) = v := by
  let : (scalarReductionRestriction l E W m).Full := restrictionFull l E W m
  exact rightMapChosen
    (operationOrdinaryAdjunction l E W m)
    (operationOrdinaryAdjunction l E W n)
    (normalizedDVRModuleRes l E W h) (operationRestrictionIso l E W m n h)
    (coefficientOrdinaryQuotient l E W h) M (ordinaryQuotientComparisonFormula l E W m n h M) v hu

private def ordinaryFiniteComparison (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (κ : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) :
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C).asFunctor.obj
      (op n) ≅ unrestrictedTowerComplex l E W n P :=
  complexComparison (coefficientSequenceRestriction l E W)
    (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n) (op n)
    (operationEvaluationIso l E W n) C ≪≫
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso κ

private theorem ordinaryFiniteComparison_f (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (κ : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) (i : ℤ) :
    (ordinaryFiniteComparison l E W n C P κ).hom.f i =
      (operationEvaluationAt l E W n (C.X i)).hom ≫
        (scalarReductionRestriction l E W n).map (κ.hom.f i) := by
  exact comparisonWithIso_f (coefficientSequenceRestriction l E W)
    (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n)
    (op n) (operationEvaluationIso l E W n) C
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) κ i

private theorem evaluationComponentHom (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ)
    (M : coefficientSequenceModules l E W) :
    (operationEvaluationAt l E W n M).hom =
      (operationEvaluationIso l E W n).hom.app M := by
  rfl

private def operationTransitionComponent (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (M : coefficientSequenceModules l E W) :
    (coefficientSequenceEvaluation l E W m).obj M ⟶
      (normalizedDVRModuleRes l E W h).obj ((coefficientSequenceEvaluation l E W n).obj M) :=
  compositeComponent (coefficientSequenceEvaluation l E W m)
    (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
    (coefficientSequenceTransition l E W h) M

private def operationQuotientComponent (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (N : scalarReductionSource l E W) :
    (scalarReductionExtension l E W m).obj N ⟶
      (normalizedDVRModuleRes l E W h).obj ((scalarReductionExtension l E W n).obj N) :=
  compositeComponent (scalarReductionExtension l E W m)
    (scalarReductionExtension l E W n) (normalizedDVRModuleRes l E W h)
    (coefficientOrdinaryQuotient l E W h) N

private theorem operationTransitionComponent_generic (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (M : coefficientSequenceModules l E W) :
    operationTransitionComponent l E W m n h M =
      compositeComponent (coefficientSequenceEvaluation l E W m)
        (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
        (coefficientSequenceTransition l E W h) M := rfl

private theorem operationQuotientComponent_generic (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource l E W) :
    operationQuotientComponent l E W m n h M =
      compositeComponent (scalarReductionExtension l E W m)
        (scalarReductionExtension l E W n) (normalizedDVRModuleRes l E W h)
        (coefficientOrdinaryQuotient l E W h) M := rfl

attribute [local semireducible] coefficientSequenceRestriction

-- Compare underlying section maps directly; transporting the old functor-level
-- square through scalar restriction would repeatedly unfold completed actions.
private theorem ordinaryTypedRestrictionSquare (W : AlgebraicGeometry.Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (m n : ℕ) (h : n ≤ m)
    (M : coefficientSequenceModules l E W) :
    ((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op ≫
        (operationEvaluationAt l E W n M).hom =
      (operationEvaluationAt l E W m M).hom ≫
        (scalarReductionRestriction l E W m).map
          (operationTransitionComponent l E W m n h M) ≫
        (operationRestrictionAt l E W m n h
          ((coefficientSequenceEvaluation l E W n).obj M)).hom := by
  rw [evaluationComponentHom, evaluationComponentHom, restrictionComponentHom]
  have hc : completedCompO l E W D hl h = operationRestrictionIso l E W m n h :=
    (restrictComp_eq
      (completedIntegralCoefficientProjection l E W D hl m)
      (normalizedDVRQuotient l E W h)
      (completedIntegralCoefficientProjection l E W D hl n)
      (completedProjectionComp l E W D hl h) (coefficientRestrictionComp l E W h)).trans
        (operationRestrictionIso_eq l E W m n h).symm
  rw [← hc]
  unfold operationEvaluationIso
  have hU := (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  simp only [eqToIso.hom, eqToHom_app]
  apply moduleHom_eq_of_heq (hU.1 M m) (hU.1 M n)
  intro U
  have hτ := restrictionComposite_heq
    (completedIntegralCoefficientProjection l E W D hl m) (normalizedDVRQuotient l E W h)
    (completedIntegralCoefficientProjection l E W D hl n)
    (completedProjectionComp l E W D hl h)
    (operationTransitionComponent l E W m n h M) U
  have hσ : HEq
      (fun x : ((coefficientSequenceEvaluation l E W m).obj M).val.obj U ↦
        (((operationTransitionComponent l E W m n h M).val.app U) x))
      (fun x : M.val.obj (op (m, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
    exact transition_heq l E W M h U
  exact (hU.2.1 M m n h U).trans (hτ.trans hσ).symm

attribute [local irreducible] coefficientSequenceRestriction

private theorem arrowSquare
    {A : Type*} [Category A]
    {Xm Xn Am An B Pm Pn Q : A}
    (u : Xm ⟶ Xn) (am : Xm ⟶ Am) (an : Xn ⟶ An)
    (t : Am ⟶ B) (c : B ⟶ An) (km : Am ⟶ Pm) (kn : An ⟶ Pn)
    (j : B ⟶ Q) (d : Q ⟶ Pn) (f : Pm ⟶ Q) (v : Pm ⟶ Pn)
    (ht : u ≫ an = am ≫ t ≫ c) (hk : t ≫ j = km ≫ f)
    (hc : j ≫ d = c ≫ kn) (hf : f ≫ d = v) :
    u ≫ (an ≫ kn) = (am ≫ km) ≫ v := by
  rw [← Category.assoc, ht]
  simp only [Category.assoc]
  rw [← hc, ← Category.assoc t, hk]
  simp only [Category.assoc]
  rw [hf]

private theorem compositionNaturality
    {A B C : Type*} [Category A] [Category B] [Category C]
    (G : B ⥤ A) (G' : C ⥤ A) (H : C ⥤ B) (c : H ⋙ G ≅ G')
    {X Y : C} (f : X ⟶ Y) :
    G.map (H.map f) ≫ c.hom.app Y = c.hom.app X ≫ G'.map f := by
  exact c.hom.naturality f

private theorem restrictionComparison_naturality
    {A B C : Type*} [Category A] [Category B] [Category C]
    (G : B ⥤ A) (G' : C ⥤ A) (H : C ⥤ B) (c : H ⋙ G ≅ G')
    {X Y : C} (f : X ⟶ Y) :
    G.map (H.map f) ≫ (restrictionComparison G G' H c Y).hom =
      (restrictionComparison G G' H c X).hom ≫ G'.map f := by
  rw [restrictionComparison_hom, restrictionComparison_hom]
  exact compositionNaturality G G' H c f

private theorem ordinaryRestrictionNaturality (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m)
    (M : coefficientSequenceModules l E W) (N : scalarReductionSource l E W)
    (κn : (coefficientSequenceEvaluation l E W n).obj M ⟶
      (scalarReductionExtension l E W n).obj N) :
    (scalarReductionRestriction l E W m).map ((normalizedDVRModuleRes l E W h).map κn) ≫
        (operationRestrictionAt l E W m n h
          ((scalarReductionExtension l E W n).obj N)).hom =
      (operationRestrictionAt l E W m n h
          ((coefficientSequenceEvaluation l E W n).obj M)).hom ≫
        (scalarReductionRestriction l E W n).map κn := by
  rw [operationRestrictionAt_eq, operationRestrictionAt_eq]
  exact restrictionComparison_naturality
    (scalarReductionRestriction l E W m) (scalarReductionRestriction l E W n)
    (normalizedDVRModuleRes l E W h) (operationRestrictionIso l E W m n h)
    (X := (coefficientSequenceEvaluation l E W n).obj M)
    (Y := (scalarReductionExtension l E W n).obj N) κn

private theorem ordinaryMappedQuotientSquare (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m)
    (M : coefficientSequenceModules l E W) (N : scalarReductionSource l E W)
    (κm : (coefficientSequenceEvaluation l E W m).obj M ⟶
      (scalarReductionExtension l E W m).obj N)
    (κn : (coefficientSequenceEvaluation l E W n).obj M ⟶
      (scalarReductionExtension l E W n).obj N)
    (hκ : (coefficientSequenceTransition l E W h).app M ≫
        (normalizedDVRModuleRes l E W h).map κn =
      κm ≫ (coefficientOrdinaryQuotient l E W h).app N) :
    (scalarReductionRestriction l E W m).map (operationTransitionComponent l E W m n h M) ≫
      (scalarReductionRestriction l E W m).map ((normalizedDVRModuleRes l E W h).map κn) =
    (scalarReductionRestriction l E W m).map κm ≫
      (scalarReductionRestriction l E W m).map (operationQuotientComponent l E W m n h N) := by
  rw [operationTransitionComponent_generic, operationQuotientComponent_generic]
  exact mappedQuotientSquareAllComponents
    (coefficientSequenceEvaluation l E W m) (coefficientSequenceEvaluation l E W n)
    (scalarReductionExtension l E W m) (scalarReductionExtension l E W n)
    (scalarReductionRestriction l E W m) (normalizedDVRModuleRes l E W h)
    (coefficientSequenceTransition l E W h) (coefficientOrdinaryQuotient l E W h)
    M N κm κn hκ

private theorem ordinaryTypedRestrictedQuotient (W : AlgebraicGeometry.Scheme.{u})
    (m n : ℕ) (h : n ≤ m) (M : scalarReductionSource.{u, u} l E W)
    (v : (scalarReductionRestriction l E W m).obj
        ((scalarReductionExtension l E W m).obj M) ⟶
      (scalarReductionRestriction l E W n).obj ((scalarReductionExtension l E W n).obj M))
    (hu : (operationOrdinaryAdjunction l E W m).unit.app M ≫ v =
      (operationOrdinaryAdjunction l E W n).unit.app M) :
    (scalarReductionRestriction l E W m).map
        (operationQuotientComponent l E W m n h M) ≫
      (operationRestrictionAt l E W m n h
        ((scalarReductionExtension l E W n).obj M)).hom = v := by
  rw [operationRestrictionAt_eq, operationQuotientComponent_generic]
  exact restrictionSquareAllComponents
    (scalarReductionExtension l E W m) (scalarReductionExtension l E W n)
    (scalarReductionRestriction l E W m) (scalarReductionRestriction l E W n)
    (normalizedDVRModuleRes l E W h) (operationRestrictionIso l E W m n h)
    (coefficientOrdinaryQuotient l E W h) M v
    (ordinaryRestrictedQuotient l E W m n h M v hu)

private theorem ordinaryModuleSquare (W : AlgebraicGeometry.Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (m n : ℕ) (h : n ≤ m)
    (M : coefficientSequenceModules.{u, u} l E W) (N : scalarReductionSource.{u, u} l E W)
    (κm : (coefficientSequenceEvaluation l E W m).obj M ⟶
      (scalarReductionExtension l E W m).obj N)
    (κn : (coefficientSequenceEvaluation l E W n).obj M ⟶
      (scalarReductionExtension l E W n).obj N)
    (hκ : (coefficientSequenceTransition l E W h).app M ≫
        (normalizedDVRModuleRes l E W h).map κn =
      κm ≫ (coefficientOrdinaryQuotient l E W h).app N)
    (v : (scalarReductionRestriction l E W m).obj
        ((scalarReductionExtension l E W m).obj N) ⟶
      (scalarReductionRestriction l E W n).obj ((scalarReductionExtension l E W n).obj N))
    (hu : (operationOrdinaryAdjunction l E W m).unit.app N ≫ v =
      (operationOrdinaryAdjunction l E W n).unit.app N) :
    ((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op ≫
        ((operationEvaluationAt l E W n M).hom ≫
          (scalarReductionRestriction l E W n).map κn) =
      ((operationEvaluationAt l E W m M).hom ≫
        (scalarReductionRestriction l E W m).map κm) ≫ v := by
  have ht := ordinaryTypedRestrictionSquare l E W D hl m n h M
  have hf := ordinaryTypedRestrictedQuotient l E W m n h N v hu
  have hc := ordinaryRestrictionNaturality l E W m n h M N κn
  have hk := ordinaryMappedQuotientSquare l E W m n h M N κm κn hκ
  exact arrowSquare
    (((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op)
    (operationEvaluationAt l E W m M).hom (operationEvaluationAt l E W n M).hom
    ((scalarReductionRestriction l E W m).map (operationTransitionComponent l E W m n h M))
    ((operationRestrictionAt l E W m n h
      ((coefficientSequenceEvaluation l E W n).obj M)).hom)
    ((scalarReductionRestriction l E W m).map κm)
    ((scalarReductionRestriction l E W n).map κn)
    ((scalarReductionRestriction l E W m).map ((normalizedDVRModuleRes l E W h).map κn))
    ((operationRestrictionAt l E W m n h
      ((scalarReductionExtension l E W n).obj N)).hom)
    ((scalarReductionRestriction l E W m).map (operationQuotientComponent l E W m n h N))
    v ht hk hc hf

private theorem ordinaryChainSquare (W : AlgebraicGeometry.Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) (m n : ℕ) (h : n ≤ m)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (κm : ((coefficientSequenceEvaluation l E W m).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W m).mapHomologicalComplex (.up ℤ)).obj P)
    (κn : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (hκ : (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
        (.up ℤ)).app C ≫
      ((normalizedDVRModuleRes l E W h).mapHomologicalComplex (.up ℤ)).map κn.hom =
      κm.hom ≫ (NatTrans.mapHomologicalComplex
        (coefficientOrdinaryQuotient l E W h) (.up ℤ)).app P)
    (v : unrestrictedTowerComplex l E W m P ⟶ unrestrictedTowerComplex l E W n P)
    (hu : ∀ i, (operationOrdinaryAdjunction l E W m).unit.app (P.X i) ≫
      v.f i = (operationOrdinaryAdjunction l E W n).unit.app (P.X i)) :
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C).asFunctor.map
        (homOfLE h).op ≫ (ordinaryFiniteComparison l E W n C P κn).hom =
      (ordinaryFiniteComparison l E W m C P κm).hom ≫ v := by
  apply HomologicalComplex.hom_ext
  intro i
  have hκi : (coefficientSequenceTransition l E W h).app (C.X i) ≫
      (normalizedDVRModuleRes l E W h).map (κn.hom.f i) =
    κm.hom.f i ≫ (coefficientOrdinaryQuotient l E W h).app (P.X i) :=
    congrArg (fun f ↦ f.f i) hκ
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ordinaryFiniteComparison_f, ordinaryFiniteComparison_f]
  exact ordinaryModuleSquare l E W D hl m n h (C.X i) (P.X i)
    (κm.hom.f i) (κn.hom.f i) hκi (v.f i) (hu i)

private theorem assembleSequenceIso
    {A : Type*} [Category A] [HasZeroMorphisms A]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (X : ℕ → CochainComplex A ℤ)
    (τ : ∀ n, X (n + 1) ⟶ X n)
    (b : ∀ n, C.asFunctor.obj (op n) ≅ X n)
    (hb : ∀ n, C.asFunctor.map (homOfLE (show n ≤ n + 1 from n.le_succ)).op ≫
      (b n).hom = (b (n + 1)).hom ≫ τ n) :
    Nonempty (C.asFunctor ≅ Functor.ofOpSequence τ) := by
  obtain ⟨e, _⟩ := assembleObjectTowerIso C (Functor.ofOpSequence τ) b (fun n ↦ by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact hb n)
  exact ⟨e⟩

private noncomputable def operationGlobalTowerIso (W : AlgebraicGeometry.Scheme.{u}) :
    (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E W n)
      (unrestrictedIntegralTransition l E W)).flip ≅ IntegralOnSlice.tower l E W none :=
  eqToIso (IntegralOnSlice.globalTower_eq l E W).symm

private theorem ordinaryTowerComparison (W : AlgebraicGeometry.Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (hκ : ∀ n : ℕ,
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W
        (m := n + 1) (n := n) n.le_succ)
        (.up ℤ)).app C ≫
        ((normalizedDVRModuleRes l E W
          (m := n + 1) (n := n) n.le_succ).mapHomologicalComplex (.up ℤ)).map
          (κ n).hom = (κ (n + 1)).hom ≫ ((NatTrans.mapHomologicalComplex
      (coefficientOrdinaryQuotient l E W (m := n + 1) (n := n) n.le_succ) (.up ℤ)).app P)) :
    Nonempty ((((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (.up ℤ)).obj C).asFunctor ≅ (IntegralOnSlice.tower l E W none).obj P) := by
  let B := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C
  have hb (n : ℕ) := ordinaryChainSquare l E W D hl (n + 1) n n.le_succ C P
    (κ (n + 1)) (κ n) (hκ n) (unrestrictedTowerTransition l E W P n)
    (fun i ↦ unitStepDegree l E W n D hl P i)
  obtain ⟨t⟩ := assembleSequenceIso B (fun n ↦ unrestrictedTowerComplex l E W n P)
    (unrestrictedTowerTransition l E W P) (fun n ↦ ordinaryFiniteComparison l E W n C P (κ n)) hb
  exact ⟨t ≪≫ ordinaryTowerPresentation l E W P ≪≫ sequenceEvaluationIso
    (fun n ↦ unrestrictedIntegralComplexFunctor l E W n)
    (unrestrictedIntegralTransition l E W) P ≪≫
      (operationGlobalTowerIso l E W).app P⟩
private theorem fromOrdinary (W : AlgebraicGeometry.Scheme.{u})
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P)
    (T : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource.{u, u} l E W) ℤ)
    (F : ∀ n : ℕ, CochainComplex (scalarReductionTarget.{u, u} l E W n) ℤ)
    (t₀ : (IntegralOnSlice.tower l E W none).obj P ≅ T)
    (j : ∀ n : ℕ, T.obj (op n) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj (F n))
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (e : K ≅ DerivedCategory.Q.obj (integralOperationsRoos T)) :
    operationEffective l E W T F j K e := by
  classical
  have H := coefficientDerivedSystemEvaluationCalculus.{u, u} l E W
  rcases H with ⟨S, _⟩
  obtain ⟨C, m, κ, _, hκ⟩ := S.reductionModel P hP.1 hP.2
  let N := S.reduction.obj (DerivedCategory.Q.obj P)
  have hN : IsNormalizedCoefficientSequence l E W N := S.reduction_normalized _
  have H : ∃ p : ℕ, l + 1 ≤ p ∧ p.Prime := Nat.exists_infinite_primes (l + 1)
  rcases H with ⟨p, hpl, hp⟩
  let D := effectivityTestDatum p hp
  have hl : l ≠ D.p := by change l ≠ p; omega
  have H := ordinaryTowerComparison l E W D hl C P κ
    (fun n ↦ hκ (n + 1) n n.le_succ)
  rcases H with ⟨tC⟩
  let t := tC ≪≫ t₀
  have H (n : ℕ) := liftFiniteComparison l E W n C (F n) (t.app (op n) ≪≫ j n)
  choose κF hκF using H
  exact strictRealization l E W N hN C m T F κF t j hκF K e
private theorem adjointDropIdentity
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) (Q : C ⥤ A)
    (K X : A) (Y : C) (Z : B) (e : K ⟶ X) (p : X ⟶ Q.obj Y)
    (q : Q.obj Y ⟶ R.obj Z)
    (h : IsIso ((adj.homEquiv K Z).symm (e ≫ p ≫ Q.map (𝟙 Y) ≫ q))) :
    IsIso ((adj.homEquiv K Z).symm (e ≫ p ≫ q)) := by
  rw [Q.map_id, Category.id_comp] at h
  exact h

attribute [local semireducible] operationDerivedAdjunction operationEffective

/-- The Roos limits of finite pullback and finite tensor towers are derived complete,
and their actual projection adjoints compute finite reduction. This assertion uses
only good representatives, with no boundedness or constructibility hypotheses.

Source: Stacks Tags 099M and 099N(5); Bhatt--Scholze, Lemmas 3.5.4--3.5.7
(blueprint: lem-pur-integral-operation-roos-effectivity).

Proof:
1. Compute ordinary reduction of a good completed-coefficient representative by the
simultaneous K-flat coefficient-sequence model. Its finite comparisons commute with
successive quotients, since the quotient map is adjoint to the smaller tensor unit.
2. Restrict its strict sequence representative to the completion. The restriction
comparisons and finite model comparisons form an isomorphism of whole strict towers.
The ambient pullback and tensor tower isomorphisms identify the operation towers
with ordinary reductions of good completed-coefficient representatives.
3. Completion projections are locally surjective, so restriction is full and faithful.
Lift the level isomorphisms to the finite coefficient categories. The canonical Roos
comparison preserves each actual mapping-cocone projection.
4. A normalized coefficient sequence has a normalized DVR Roos model with those same
projections. Transport its distinguished triangle along the vertex isomorphism and
apply normalized DVR effectivity and finite reduction. Adjunction naturality and the
finite evaluation isomorphisms identify the requested adjoints. The legacy comparison
gives IsSfDerivedComplete. No boundedness or constructibility enters the argument. -/
theorem integralOperationRoos_effectivity :
    (∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (K : DerivedCategory (integralTowerModules l E X))
      (e : K ≅ DerivedCategory.Q.obj
        ((integralOperationsPullbackComplexFunctor l E f).obj P.obj)),
      IsSfDerivedComplete l E X K ∧ ∀ n : ℕ,
        IsIso ((((derivedScalarExtensionRestrictionAdjunction l E X n).choose).homEquiv _ _).symm
          (e.hom ≫ integralOperationRoosProjection l E X
            ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n ≫
            (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
              (integralPullbackFiniteComplex l E f P.obj n)))) ∧
    (∀ (W : AlgebraicGeometry.Scheme.{u})
      (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
      (K : DerivedCategory (integralTowerModules l E W))
      (e : K ≅ DerivedCategory.Q.obj
        ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj))),
      IsSfDerivedComplete l E W K ∧ ∀ n : ℕ,
        IsIso ((((derivedScalarExtensionRestrictionAdjunction l E W n).choose).homEquiv _ _).symm
          (e.hom ≫ integralOperationRoosProjection l E W
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)) n ≫
            (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app
              (integralTensorFiniteComplex l E W P.obj Q.obj n)))) := by
  constructor
  · intro X Y f P K e
    let R := (IntegralAmbient.pullComplex l E f).obj P.obj
    have hR :=
      IntegralAmbient.pull_good.{u, u} l E f P.obj P.property
    have H := fromOrdinary l E X R hR
      ((integralOperationsPullbackTowerFunctor l E f).obj P.obj)
      (fun n ↦ integralPullbackFiniteComplex l E f P.obj n)
      ((IntegralAmbient.pullTowerIso.{u, u} l E f).app P.obj)
      (fun _ ↦ Iso.refl _) K e
    rcases H with ⟨hc, hi⟩
    refine ⟨hc, fun n ↦ ?_⟩
    exact adjointDropIdentity
      (operationDerivedAdjunction l E X n) DerivedCategory.Q
      K _ (((integralOperationsPullbackTowerFunctor l E f).obj P.obj).obj (op n))
      (DerivedCategory.Q.obj (integralPullbackFiniteComplex l E f P.obj n)) e.hom
      (integralOperationRoosProjection l E X
        ((integralOperationsPullbackTowerFunctor l E f).obj P.obj) n)
      ((scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
        (integralPullbackFiniteComplex l E f P.obj n))
      (hi n)
  · intro W P Q K e
    let R := (coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)
    have hR :=
      IntegralAmbient.tensor_good.{u, u} l E W P.obj Q.obj P.property Q.property
    have H := fromOrdinary l E W R hR
      ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
      (fun n ↦ integralTensorFiniteComplex l E W P.obj Q.obj n)
      ((IntegralAmbient.tensorTowerIso.{u, u} l E W).app (P.obj, Q.obj))
      (fun _ ↦ Iso.refl _) K e
    rcases H with ⟨hc, hi⟩
    refine ⟨hc, fun n ↦ ?_⟩
    exact adjointDropIdentity
      (operationDerivedAdjunction l E W n) DerivedCategory.Q
      K _ (((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)).obj (op n))
      (DerivedCategory.Q.obj (integralTensorFiniteComplex l E W P.obj Q.obj n)) e.hom
      (integralOperationRoosProjection l E W
        ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)) n)
      ((scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app
        (integralTensorFiniteComplex l E W P.obj Q.obj n))
      (hi n)

end WeilConjectures
