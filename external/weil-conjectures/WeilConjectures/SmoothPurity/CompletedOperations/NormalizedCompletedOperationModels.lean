/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationExpressions
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.SmoothPurity.CoefficientClosedStructure.CoefficientClosedTensorComparison
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.TraceFormula.Supporting.EffectiveQuotientModelDescent
import WeilConjectures.SmoothPurity.Normalized.NormalizedCompletionRealization
import WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionKFlatNormalization
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization

/-! # Simultaneous primitive models for completed operations

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9(4); blueprint
main-20261015, order 2232, coefficient twists; explicit coherent-counit refinement
in original proof steps 1--6 of completed-operation substitution
(blueprint: lem-pur-normalized-completed-operation-models).

All comparisons live in the ordinary derived category of the ringed sequence
site before restriction or total derived limit. The natural-number index n
means positive quotient exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u s i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOperations

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Compatible presentations of the *specified* operations. The tensor structures
are normalized on K-flat total complexes by RingedSiteDualityModel; the reduction
calculus fixes every quotient map and both adjunction projections. Its closed
tensors are compared canonically through their common internal Hom. Completion's
comparison is pinned by the actual quotient/Roos augmentation. Pullback's
comparison is pinned on every simultaneous quotient presentation, not chosen
separately on evaluated objects.
Source: node proof steps 1, 4--5; Stacks 06YY, 07A4, 0941
(blueprint: lem-pur-completed-operation-tower-substitution). -/
structure Models {S : Type s} (W : S → Scheme.{t}) where
  /-- The recorded reduction/total-limit adjunction. -/
  calculus : ∀ a : S, CoefficientDerivedSystemCalculus l E (W a)
  /-- Canonical total tensor, action unit and signed interchange on whole systems. -/
  system : ∀ a : S, RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a))
  /-- Completion as the reduction/total-limit composite. -/
  completion : ∀ a : S, IntegralOnSlice.completion l E (W a) none ≅
    (calculus a).reduction ⋙ coefficientSequenceLimit l E (W a)
  /-- Unit normalization determines this comparison, including its maps. -/
  completion_unit : ∀ (a : S) (K : DerivedCategory (scalarReductionSource l E (W a))),
    (IntegralOnSlice.completionUnit l E (W a) none).app K ≫
        (completion a).hom.app K = (calculus a).adjunction.unit.app K
  /-- The actual total-limit/Roos comparison with its K-injective normalization. -/
  roos : ∀ a : S, IntegralComparisonRoosModel l E (W a)
  /-- Pullback is normalized on all K-flat quotient presentations. -/
  pullback : ∀ {a b : S} (f : W a ⟶ W b),
    IntegralComparisonPullbackModel l E f (calculus b) (roos a)

variable {S : Type s} {W : S → Scheme.{t}} (M : Models l E W)

/-- The system tensor in the fixed canonical total-complex presentation.
Source: node proof steps 1--2 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensor (a : S) := (M.system a).closed.tensor

/-- The coefficient unit system B_n[0], including its actual quotient transitions.
Source: node proof steps 3 and 7 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def unit (a : S) : coefficientSequenceDerived l E (W a) :=
  ringedSiteDualityUnit.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a))

/-- The defining quotient-limit tensor realization. Each factor is fixed by the
reduction tensor model, closed-tensor presentation, or completion augmentation.
Source: node proof step 5 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensorRealization (a : S) : IntegralOnSlice.completedTensor l E (W a) none ≅
    ((M.calculus a).reduction.prod (M.calculus a).reduction) ⋙
      tensor l E M a ⋙ coefficientSequenceLimit l E (W a) :=
  isoWhiskerLeft (IntegralOnSlice.duality l E (W a) none).closed.tensor (M.completion a) ≪≫
    isoWhiskerRight
      (isoWhiskerRight
        (CoefficientClosedStructure.comparison
          (IntegralOnSlice.duality l E (W a) none).closed (M.calculus a).integralClosed)
          (M.calculus a).reduction ≪≫
        (M.calculus a).reductionTensor ≪≫
        isoWhiskerLeft ((M.calculus a).reduction.prod (M.calculus a).reduction)
          (CoefficientClosedStructure.comparison (M.calculus a).systemClosed (M.system a).closed))
      (coefficientSequenceLimit l E (W a))

/-- The primitive tensor comparison is L(T(e_A,e_N)), after its defining realization.
This is a formula using the coherent counit, before any invertibility assertion.
Source: node proof step 6 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensorComparison (a : S) (A N : coefficientSequenceDerived l E (W a)) :
    (IntegralOnSlice.completedTensor l E (W a) none).obj
        ((coefficientSequenceLimit l E (W a)).obj A,
         (coefficientSequenceLimit l E (W a)).obj N) ⟶
      (coefficientSequenceLimit l E (W a)).obj ((tensor l E M a).obj (A, N)) :=
  (tensorRealization l E M a).hom.app _ ≫
    (coefficientSequenceLimit l E (W a)).map
      ((tensor l E M a).map (Prod.mkHom
        ((M.calculus a).adjunction.counit.app A) ((M.calculus a).adjunction.counit.app N)))

/-- The primitive pullback comparison is L(F(e_C)), after quotient-model realization.
Source: node proof step 6 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def pullbackComparison {a b : S} (f : W a ⟶ W b)
    (C : coefficientSequenceDerived l E (W b)) :
    (integralDerivedPullback l E f).obj ((coefficientSequenceLimit l E (W b)).obj C) ⟶
      (coefficientSequenceLimit l E (W a)).obj
        ((integralComparisonDerivedSequencePullback l E f).obj C) :=
  (M.pullback f).realization.hom.app _ ≫
    (coefficientSequenceLimit l E (W a)).map
      ((integralComparisonDerivedSequencePullback l E f).map
        ((M.calculus b).adjunction.counit.app C))

/-- Normalization for the three primitive operations and effectivity of the
specified coherent counit. These assertions involve individual systems only.
Source: original proof steps 1--6 of completed-operation substitution; Stacks
07A4, 07A6 and 0941 (blueprint: lem-pur-normalized-completed-operation-models). -/
structure PrimitiveLaws : Prop where
  counit : ∀ (a : S) (N : coefficientSequenceDerived l E (W a)),
    IsNormalizedCoefficientSequence l E (W a) N →
      IsIso ((M.calculus a).adjunction.counit.app N)
  unit : ∀ a : S, IsNormalizedCoefficientSequence l E (W a) (unit l E (W := W) a)
  tensor : ∀ (a : S) (A N : coefficientSequenceDerived l E (W a)),
    IsNormalizedCoefficientSequence l E (W a) A →
    IsNormalizedCoefficientSequence l E (W a) N →
      IsNormalizedCoefficientSequence l E (W a) ((tensor l E M a).obj (A, N))
  pullback : ∀ {a b : S} (f : W a ⟶ W b) (N : coefficientSequenceDerived l E (W b)),
    IsNormalizedCoefficientSequence l E (W b) N →
      IsNormalizedCoefficientSequence l E (W a)
        ((integralComparisonDerivedSequencePullback l E f).obj N)

omit [Fact l.Prime] in
private theorem primeUnit (X : Scheme.{t})
    (hl : ∀ x : X, IsUnit (l : X.residueField x)) : IsUnit (l : Γ(X, ⊤)) := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have h : IsUnit (l : X.presheaf.stalk x) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    simpa only [map_natCast] using (hl x).ne_zero
  simpa only [map_natCast] using h

private theorem modelCounit (a : S)
    (hl : ∀ x : W a, IsUnit (l : (W a).residueField x))
    (N : coefficientSequenceDerived l E (W a))
    (hN : IsNormalizedCoefficientSequence l E (W a) N) :
    IsIso ((M.calculus a).adjunction.counit.app N) :=
  ((purNormalizedReconstruction l E (W a) (primeUnit l (W a) hl)
    (M.calculus a)).1 N hN).2

private theorem normalizedIso {X : Scheme.{t}}
    {A B : coefficientSequenceDerived l E X} (e : A ≅ B)
    (hA : IsNormalizedCoefficientSequence l E X A) :
    IsNormalizedCoefficientSequence l E X B := by
  intro m n h P
  let Em := coefficientSequenceDerivedEvaluation l E X m
  let En := coefficientSequenceDerivedEvaluation l E X n
  let R := normalizedDVRRes l E X h
  let i := (En.mapIso e).hom
  let j := (Em.mapIso e).hom
  have hc : (fun f : En.obj B ⟶ P ↦
      (coefficientSequenceDerivedTransition l E X h).app A ≫ R.map (i ≫ f)) =
      (fun f : En.obj B ⟶ P ↦ j ≫
        ((coefficientSequenceDerivedTransition l E X h).app B ≫ R.map f)) := by
    funext f
    dsimp only [i, j, Functor.mapIso_hom, En, Em]
    rw [Functor.map_comp, ← Category.assoc]
    have hn := (coefficientSequenceDerivedTransition l E X h).naturality e.hom
    change (coefficientSequenceDerivedEvaluation l E X m).map e.hom ≫
      (coefficientSequenceDerivedTransition l E X h).app B =
        (coefficientSequenceDerivedTransition l E X h).app A ≫
          R.map ((coefficientSequenceDerivedEvaluation l E X n).map e.hom) at hn
    rw [← hn, Category.assoc]
  have hi : Function.Bijective (fun f : En.obj B ⟶ P ↦ i ≫ f) := by
    exact ⟨fun _ _ h ↦ (cancel_epi i).1 h,
      fun f ↦ ⟨(En.mapIso e).inv ≫ f, by simp [i]⟩⟩
  have hj : Function.Bijective
      (fun f : Em.obj B ⟶ R.obj P ↦ j ≫ f) := by
    exact ⟨fun _ _ h ↦ (cancel_epi j).1 h,
      fun f ↦ ⟨(Em.mapIso e).inv ≫ f, by simp [j]⟩⟩
  have hb := (hA h P).comp hi
  rw [show ((fun f : En.obj A ⟶ P ↦
      (coefficientSequenceDerivedTransition l E X h).app A ≫ R.map f) ∘
        (fun f : En.obj B ⟶ P ↦ i ≫ f)) = _ from hc] at hb
  exact ⟨fun f g he ↦ hb.1 (congrArg (fun k ↦ j ≫ k) he), fun f ↦ by
    obtain ⟨g, hg⟩ := hb.2 (j ≫ f)
    exact ⟨g, hj.1 hg⟩⟩

private theorem modelUnit (a : S)
    (hl : ∀ x : W a, IsUnit (l : (W a).residueField x)) :
    IsNormalizedCoefficientSequence l E (W a) (unit l E (W := W) a) := by
  let P : Fin 0 → CochainComplex (scalarReductionSource l E (W a)) ℤ := Fin.elim0
  obtain ⟨N, κ, _, _, h, _, _⟩ :=
    StrictQuotient.quotientExpressionKFlatNormalization l E (𝟙 (W a)) (𝟙 (W a))
      hl hl hl 0 P (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
  intro m n hmn Q
  have hu : IsNormalizedCoefficientSequence l E (W a)
      (DerivedCategory.Q.obj
        (MonoidalCategory.tensorUnit (StrictQuotient.Complex l E (W a)))) := by
    exact (h (W a) _ (StrictQuotient.Generated.unitY (N := N))).2.1
  exact hu hmn Q

private theorem modelTensor (a : S)
    (hl : ∀ x : W a, IsUnit (l : (W a).residueField x))
    (A N : coefficientSequenceDerived l E (W a))
    (hA : IsNormalizedCoefficientSequence l E (W a) A)
    (hN : IsNormalizedCoefficientSequence l E (W a) N) :
    IsNormalizedCoefficientSequence l E (W a) ((tensor l E M a).obj (A, N)) := by
  let C := M.calculus a
  let L := coefficientSequenceLimit l E (W a)
  let := modelCounit l E M a hl A hA
  let := modelCounit l E M a hl N hN
  let eA : C.reduction.obj (L.obj A) ≅ A := asIso (C.adjunction.counit.app A)
  let eN : C.reduction.obj (L.obj N) ≅ N := asIso (C.adjunction.counit.app N)
  let e := (C.reductionTensor).app (L.obj A, L.obj N)
  apply normalizedIso l E (e ≪≫ C.systemClosed.tensor.mapIso (Iso.prod eA eN) ≪≫
    (CoefficientClosedStructure.comparison C.systemClosed (M.system a).closed).app (A, N))
  exact C.reduction_normalized _

include M in
private theorem modelPullback {a b : S} (f : W a ⟶ W b)
    (ha : ∀ x : W a, IsUnit (l : (W a).residueField x))
    (hb : ∀ x : W b, IsUnit (l : (W b).residueField x))
    (N : coefficientSequenceDerived l E (W b))
    (hN : IsNormalizedCoefficientSequence l E (W b) N) :
    IsNormalizedCoefficientSequence l E (W a)
      ((integralComparisonDerivedSequencePullback l E f).obj N) := by
  let := modelCounit l E M b hb N hN
  let e := asIso ((M.calculus b).adjunction.counit.app N)
  apply normalizedIso l E ((integralComparisonDerivedSequencePullback l E f).mapIso e)
  exact ((effectiveQuotientModelDescent l E E (AlgHom.id _ _) f ha hb
    (M.calculus b) (M.calculus a) (M.calculus b) (M.roos a) (M.roos b)).1
      ((coefficientSequenceLimit l E (W b)).obj N)).2.1

/-- Simultaneous quotient and Roos models with primitive normalization.
This is the construction part of completed-operation substitution; it makes no
assertion about finite expressions, naturality of their recursive comparisons,
simultaneous substitution, or transport of structural maps.

Source: Bhatt--Scholze Definition 3.4.10 and Lemma 6.5.9(4), with the
representative-normalized refinement in the original substitution proof steps
1--6; Stacks 07A4, 07A6, 0941
(blueprint: lem-pur-normalized-completed-operation-models).

Proof: choose the canonical quotient/limit calculus and its ordinary and derived
completion models. Choose the sequence-site duality model and compare its closed
tensor with the calculus tensor by the unique comparison preserving their common
tensor-Hom adjunction. Do the same for the specified integral duality tensor.
The strict quotient/Roos presentation descends through good representatives to
identify completion with reduction followed by total limit. The strict quotient
augmentation agrees sectionwise with the prescribed completion augmentation;
uniqueness of its descent gives the displayed unit equation. Use the same Roos
model at each scheme in all primitive quotient pullback realizations.
The reconstruction theorem makes the actual counit invertible on normalized
systems. The unit is the empty-input unit expression in the strict quotient
normalization theorem. For tensor, identify the normalized inputs with reductions
of their total limits by this counit, apply the reduction tensor comparison, and
transport along the canonical closed-tensor comparison. Pullback of a reduction
is normalized by effective quotient model descent; pull back the same counit
isomorphism to handle any normalized input. Normalization is invariant under
isomorphism by naturality of transition and the induced Hom-set bijections.
Empty families require no choices, and none of these computations assumes
boundedness, constructibility, or flatness of a quotient map. -/
theorem normalizedCompletedOperationModels {S : Type s} (W : S → Scheme.{t})
    (_hl : ∀ (a : S) (x : W a), IsUnit (l : (W a).residueField x)) :
    ∃ M : Models l E W, PrimitiveLaws l E M := by
  classical
  have hm (a : S) : ∃ (C : CoefficientDerivedSystemCalculus l E (W a))
      (O : CompletionUnit.OrdinaryModel l E (W a)),
      Nonempty (CompletionUnit.DerivedModel l E (W a) C O) := by
    let : ∀ x : W a, Invertible (l : (W a).residueField x) :=
      fun x ↦ (_hl a x).invertible
    obtain ⟨C, _, O, hD⟩ := CompletionUnit.canonicalModels l E (W a)
    exact ⟨C, O, hD⟩
  choose C O hD using hm
  let D (a : S) := Classical.choice (hD a)
  have hc (a : S) := normalizedCompletionRealization l E (W a) (C a) (O a) (D a)
    (fun x ↦ by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
      simpa only [map_natCast] using (_hl a x).ne_zero)
  choose c hcu using hc
  let R (a : S) := roosModel l E (W a) (C a) (O a) (D a)
  let T (a : S) := Classical.choice (ringedSiteDualityMaps_exists.{t + 1, t, u, (max u (t + 1)) + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a)))
  let M : Models l E W :=
    { calculus := C
      system := T
      completion := c
      completion_unit := hcu
      roos := R
      pullback := fun {a b} f ↦ Classical.choice
        (primitiveQuotientRealizationComparisons l E E (AlgHom.id _ _) f (W b)
          (_hl a) (_hl b) (_hl b) (C b) (C b) (R a) (R b)).1 }
  exact ⟨M, ⟨fun a ↦ modelCounit l E M a (_hl a),
    fun a ↦ modelUnit l E a (_hl a), fun a ↦ modelTensor l E M a (_hl a),
    fun {a b} f ↦ modelPullback l E M f (_hl a) (_hl b)⟩⟩

end WeilConjectures.CompletedOperations
