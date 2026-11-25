/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationExpressions
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import Mathlib.CategoryTheory.Pi.Basic

/-! # Substitution into completed tensor and pullback

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9(4); blueprint
main-20261015, order 2232, coefficient twists; explicit coherent-counit refinement
in proof steps 1--12 of the node below
(blueprint: lem-pur-completed-operation-tower-substitution).

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

variable {S : Type s} {W : S → Scheme.{t}} (M : Models l E W)

variable {I : Type i} {location : I → S}

/-- Evaluate an expression on *whole* coefficient systems, functorially in all inputs.
Source: node proof step 7 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def systemValue {a : S} : Expression W location a →
    ((∀ k : I, coefficientSequenceDerived l E (W (location k))) ⥤
      coefficientSequenceDerived l E (W a))
  | .input k => Pi.eval _ k
  | .unit a => (Functor.const _).obj (unit l E (W := W) a)
  | .tensor P Q => (systemValue P).prod' (systemValue Q) ⋙ tensor l E M a
  | .pullback f P => systemValue P ⋙ integralComparisonDerivedSequencePullback l E f

/-- Evaluate with the same parentheses using the recorded completed operations.
Source: node proof step 7 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def completedValue {a : S} : Expression W location a →
    ((∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) ⥤
      DerivedCategory (scalarReductionSource l E (W a)))
  | .input k => Pi.eval _ k
  | .unit a => (Functor.const _).obj
      ((coefficientSequenceLimit l E (W a)).obj (unit l E (W := W) a))
  | .tensor P Q => (completedValue P).prod' (completedValue Q) ⋙
      IntegralOnSlice.completedTensor l E (W a) none
  | .pullback f P => completedValue P ⋙ integralDerivedPullback l E f

/-- The recursive comparison: identities at leaves, then the primitive counit formulas.
It is defined as a morphism, without choosing objectwise isomorphisms.
Source: node proof step 7 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def comparison {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    (completedValue l E P).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ⟶
      (coefficientSequenceLimit l E (W a)).obj ((systemValue l E M P).obj N) :=
  match P with
  | .input _ => 𝟙 _
  | .unit _ => 𝟙 _
  | .tensor P Q =>
      (IntegralOnSlice.completedTensor l E (W a) none).map
        (Prod.mkHom (comparison P N) (comparison Q N)) ≫
          tensorComparison l E M a ((systemValue l E M P).obj N) ((systemValue l E M Q).obj N)
  | .pullback f P => (integralDerivedPullback l E f).map (comparison P N) ≫
      pullbackComparison l E M f ((systemValue l E M P).obj N)

/-- Coherent reduction comparison e_(S_P) after R(beta_P).
Source: node proof step 8 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def reductionComparison {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :=
  (M.calculus a).reduction.map (comparison l E M P N) ≫
    (M.calculus a).adjunction.counit.app ((systemValue l E M P).obj N)

/-- Canonical comparison between substitution and system evaluation, recursively using
functoriality, with identity components at inputs and units.
Source: node proof step 12 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def systemSubstitution {J : Type j} {location' : J → S}
    (σ : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, coefficientSequenceDerived l E (W (location' k))) :
    (systemValue l E M (P.substitute σ)).obj N ≅
      (systemValue l E M P).obj (fun k ↦ (systemValue l E M (σ k)).obj N) :=
  match P with
  | .input _ => Iso.refl _
  | .unit _ => Iso.refl _
  | .tensor P Q => (tensor l E M a).mapIso
      (Iso.prod (systemSubstitution σ P N) (systemSubstitution σ Q N))
  | .pullback f P => (integralComparisonDerivedSequencePullback l E f).mapIso
      (systemSubstitution σ P N)

/-- The analogous parenthesis-preserving substitution comparison for completed evaluation.
Source: node proof step 12 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def completedSubstitution {J : Type j} {location' : J → S}
    (σ : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, DerivedCategory (scalarReductionSource l E (W (location' k)))) :
    (completedValue l E (P.substitute σ)).obj N ≅
      (completedValue l E P).obj (fun k ↦ (completedValue l E (σ k)).obj N) :=
  match P with
  | .input _ => Iso.refl _
  | .unit _ => Iso.refl _
  | .tensor P Q => (IntegralOnSlice.completedTensor l E (W a) none).mapIso
      (Iso.prod (completedSubstitution σ P N) (completedSubstitution σ Q N))
  | .pullback f P => (integralDerivedPullback l E f).mapIso
      (completedSubstitution σ P N)

/-- The named primitive constraints and their finite contexts. The composition
constraint has the direction (h >> f)* -> f* >> h* of the finite adjunction comparison.
Inverses and composites are included, so this also covers arrows inside a larger expression.
Source: node proof steps 9--12 (blueprint: lem-pur-completed-operation-tower-substitution). -/
inductive StructuralMap : {a : S} → Expression W location a →
    Expression W location a → Type (max t s i)
  | associator {a : S} (P Q R : Expression W location a) :
      StructuralMap (.tensor (.tensor P Q) R) (.tensor P (.tensor Q R))
  | leftUnitor {a : S} (P : Expression W location a) : StructuralMap (.tensor (.unit a) P) P
  | rightUnitor {a : S} (P : Expression W location a) : StructuralMap (.tensor P (.unit a)) P
  | symmetry {a : S} (P Q : Expression W location a) : StructuralMap (.tensor P Q) (.tensor Q P)
  | composition {a b c : S} (h : W c ⟶ W a) (f : W a ⟶ W b)
      (P : Expression W location b) :
      StructuralMap (.pullback (h ≫ f) P) (.pullback h (.pullback f P))
  | identity {a : S} (P : Expression W location a) : StructuralMap P P
  | inverse {a : S} {P Q : Expression W location a} : StructuralMap P Q → StructuralMap Q P
  | compose {a : S} {P Q R : Expression W location a} :
      StructuralMap P Q → StructuralMap Q R → StructuralMap P R
  | tensor {a : S} {P Q R V : Expression W location a} :
      StructuralMap P Q → StructuralMap R V → StructuralMap (.tensor P R) (.tensor Q V)
  | pullback {a b : S} (f : W a ⟶ W b) {P Q : Expression W location b} :
      StructuralMap P Q → StructuralMap (.pullback f P) (.pullback f Q)

/-- The actual system constraint: total-complex reassociation, action, Koszul sign,
or the localization of the finite adjunction-normalized composition map.
Source: node proof steps 9 and 11 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def structuralValue {a : S} {P Q : Expression W location a} (α : StructuralMap P Q)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    (systemValue l E M P).obj N ≅ (systemValue l E M Q).obj N :=
  match α with
  | .associator P Q R => (M.system a).closed.monoidal.associator
      ((systemValue l E M P).obj N) ((systemValue l E M Q).obj N)
        ((systemValue l E M R).obj N)
  | .leftUnitor P => (tensor l E M a).mapIso
      (Iso.prod (M.system a).unitIso.symm (Iso.refl _)) ≪≫
        (M.system a).closed.monoidal.leftUnitor ((systemValue l E M P).obj N)
  | .rightUnitor P => (tensor l E M a).mapIso
      (Iso.prod (Iso.refl _) (M.system a).unitIso.symm) ≪≫
        (M.system a).closed.monoidal.rightUnitor ((systemValue l E M P).obj N)
  | .symmetry P Q => (M.system a).symmetric.braiding
      ((systemValue l E M P).obj N) ((systemValue l E M Q).obj N)
  | .composition h f P => (integralComparisonSystemComposition l E h f).app
      ((systemValue l E M P).obj N)
  | .identity _ => Iso.refl _
  | .inverse α => (structuralValue α N).symm
  | .compose α β => structuralValue α N ≪≫ structuralValue β N
  | .tensor α β => (tensor l E M a).mapIso
      (Iso.prod (structuralValue α N) (structuralValue β N))
  | .pullback f α => (integralComparisonDerivedSequencePullback l E f).mapIso (structuralValue α N)

/-- The normalization and comparison assertions, with explicit whole-system naturality
and every quotient-transition square. No equality of derived maps is inferred from evaluations.
Source: node statement paragraphs 1--3, proof steps 2--10
(blueprint: lem-pur-completed-operation-tower-substitution). -/
structure ComparisonLaws : Prop where
  /-- The canonical coherent counit, not merely its independently evaluated components. -/
  counit : ∀ (a : S) (N : coefficientSequenceDerived l E (W a)),
    IsNormalizedCoefficientSequence l E (W a) N →
      IsIso ((M.calculus a).adjunction.counit.app N)
  /-- Unit, tensor and inverse image preserve normalization, hence so does every expression. -/
  normalized : ∀ {I : Type i} {location : I → S} {a : S}
    (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))),
    (∀ k, IsNormalizedCoefficientSequence l E _ (N k)) →
      IsNormalizedCoefficientSequence l E _ ((systemValue l E M P).obj N)
  /-- Both the recursive comparison and its specified coherent reduction are invertible. -/
  invertible : ∀ {I : Type i} {location : I → S} {a : S}
    (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))),
    (∀ k, IsNormalizedCoefficientSequence l E _ (N k)) →
      IsIso (comparison l E M P N) ∧ IsIso (reductionComparison l E M P N)
  /-- Naturality in morphisms of every normalized input system. -/
  naturality : ∀ {I : Type i} {location : I → S} {a : S}
    (P : Expression W location a)
    (N N' : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k))
    (_hN' : ∀ k, IsNormalizedCoefficientSequence l E _ (N' k))
    (v : ∀ k, N k ⟶ N' k),
    (completedValue l E P).map (fun k ↦ (coefficientSequenceLimit l E _).map (v k)) ≫
        comparison l E M P N' =
      comparison l E M P N ≫
        (coefficientSequenceLimit l E _).map ((systemValue l E M P).map v)
  /-- Every actual quotient transition is respected by gamma, including identity quotients. -/
  transitions : ∀ {I : Type i} {location : I → S} {a : S}
    (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k))
    {m n : ℕ} (h : n ≤ m),
    (coefficientSequenceDerivedTransition l E (W a) h).app _ ≫
        (normalizedDVRRes l E (W a) h).map
          ((coefficientSequenceDerivedEvaluation l E (W a) n).map
            (reductionComparison l E M P N)) =
      (coefficientSequenceDerivedEvaluation l E (W a) m).map
          (reductionComparison l E M P N) ≫
        (coefficientSequenceDerivedTransition l E (W a) h).app _

/-- Compatibility of the *recursive* comparisons with simultaneous substitution.
The two evaluation isomorphisms preserve parentheses; the middle arrow applies
completed operations to the comparisons for the substituted expressions.
Source: node proof step 12 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def SubstitutionLaw : Prop :=
  ∀ {I : Type i} {J : Type j} {location : I → S} {location' : J → S}
    (σ : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, coefficientSequenceDerived l E (W (location' k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)),
    (completedSubstitution l E σ P
        (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))).hom ≫
        (completedValue l E P).map (fun k ↦ comparison l E M (σ k) N) ≫
        comparison l E M P (fun k ↦ (systemValue l E M (σ k)).obj N) =
      comparison l E M (P.substitute σ) N ≫
        (coefficientSequenceLimit l E _).map (systemSubstitution l E M σ P N).hom

/-- The canonical completed constraints are characterized uniquely by their limit
and coherent reduction squares. In particular their forward map is exactly
beta_P >> L(alpha) >> beta_Q inverse. Uniqueness specifies the canonical map;
RingedSiteDualityModel fixes the system tensor maps on total-complex generators.
Source: node proof steps 9--11 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def StructuralLaw : Prop :=
  ∀ {I : Type i} {location : I → S} {a : S}
    {P Q : Expression W location a} (α : StructuralMap P Q)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)),
    ∃! c : (completedValue l E P).obj
          (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ≅
        (completedValue l E Q).obj
          (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)),
      c.hom ≫ comparison l E M Q N = comparison l E M P N ≫
          (coefficientSequenceLimit l E _).map (structuralValue l E M α N).hom ∧
        (M.calculus a).reduction.map c.hom ≫ reductionComparison l E M Q N =
          reductionComparison l E M P N ≫ (structuralValue l E M α N).hom

private theorem tensorComparison_naturality (a : S)
    {A A' N N' : coefficientSequenceDerived l E (W a)} (v : A ⟶ A') (w : N ⟶ N') :
    (IntegralOnSlice.completedTensor l E (W a) none).map
        (Prod.mkHom ((coefficientSequenceLimit l E _).map v)
          ((coefficientSequenceLimit l E _).map w)) ≫ tensorComparison l E M a A' N' =
      tensorComparison l E M a A N ≫
        (coefficientSequenceLimit l E _).map ((tensor l E M a).map (Prod.mkHom v w)) := by
  let L := coefficientSequenceLimit l E (W a)
  let R := (M.calculus a).reduction
  let T := tensor l E M a
  let e : (L ⋙ R).prod (L ⋙ R) ⟶ 𝟭 _ :=
    NatTrans.prod (M.calculus a).adjunction.counit (M.calculus a).adjunction.counit
  let β : L.prod L ⋙ IntegralOnSlice.completedTensor l E (W a) none ⟶ T ⋙ L :=
    whiskerLeft (L.prod L) (tensorRealization l E M a).hom ≫
      whiskerRight (whiskerRight e T) L
  exact β.naturality (Prod.mkHom v w)

private theorem pullbackComparison_naturality {a b : S} (f : W a ⟶ W b)
    {A B : coefficientSequenceDerived l E (W b)} (v : A ⟶ B) :
    (integralDerivedPullback l E f).map ((coefficientSequenceLimit l E _).map v) ≫
        pullbackComparison l E M f B =
      pullbackComparison l E M f A ≫ (coefficientSequenceLimit l E _).map
        ((integralComparisonDerivedSequencePullback l E f).map v) := by
  let F := integralComparisonDerivedSequencePullback l E f
  let L := coefficientSequenceLimit l E (W a)
  let β : coefficientSequenceLimit l E (W b) ⋙ integralDerivedPullback l E f ⟶ F ⋙ L :=
    whiskerLeft (coefficientSequenceLimit l E (W b)) (M.pullback f).realization.hom ≫
      whiskerRight (whiskerRight (M.calculus b).adjunction.counit F) L
  exact β.naturality v

private theorem comparison_naturality {a : S} (P : Expression W location a)
    (N N' : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (v : ∀ k, N k ⟶ N' k) :
    (completedValue l E P).map (fun k ↦ (coefficientSequenceLimit l E _).map (v k)) ≫
        comparison l E M P N' =
      comparison l E M P N ≫
        (coefficientSequenceLimit l E _).map ((systemValue l E M P).map v) := by
  induction P with
  | input k => simp [completedValue, systemValue, comparison]
  | unit a => simp [completedValue, systemValue, comparison]
  | @tensor a P Q hP hQ =>
      dsimp only [completedValue, systemValue, comparison, Functor.comp_map,
        Functor.prod'_map]
      rw [← Category.assoc, ← Functor.map_comp]
      have h : Prod.mkHom
          ((completedValue l E P).map (fun k ↦ (coefficientSequenceLimit l E _).map (v k)))
          ((completedValue l E Q).map (fun k ↦ (coefficientSequenceLimit l E _).map (v k))) ≫
          Prod.mkHom (comparison l E M P N') (comparison l E M Q N') =
          Prod.mkHom (comparison l E M P N) (comparison l E M Q N) ≫
          Prod.mkHom ((coefficientSequenceLimit l E _).map ((systemValue l E M P).map v))
            ((coefficientSequenceLimit l E _).map ((systemValue l E M Q).map v)) := by
        ext
        · simpa only [prod_comp, Prod.mkHom, Category.assoc] using hP
        · simpa only [prod_comp, Prod.mkHom, Category.assoc] using hQ
      rw [h, Functor.map_comp, Category.assoc, tensorComparison_naturality]
      simp only [Category.assoc]
  | @pullback a b f P hP =>
      dsimp only [completedValue, systemValue, comparison, Functor.comp_map]
      rw [← Category.assoc, ← Functor.map_comp, hP, Functor.map_comp, Category.assoc,
        pullbackComparison_naturality]
      simp only [Category.assoc]

private theorem comparison_substitution {J : Type j} {location' : J → S}
    (σ : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, coefficientSequenceDerived l E (W (location' k))) :
    (completedSubstitution l E σ P
        (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))).hom ≫
        (completedValue l E P).map (fun k ↦ comparison l E M (σ k) N) ≫
        comparison l E M P (fun k ↦ (systemValue l E M (σ k)).obj N) =
      comparison l E M (P.substitute σ) N ≫
        (coefficientSequenceLimit l E _).map (systemSubstitution l E M σ P N).hom := by
  induction P with
  | input k => simp [completedSubstitution, completedValue, comparison,
      systemSubstitution, Expression.substitute]
  | unit a => simp [completedSubstitution, completedValue, comparison,
      systemSubstitution, Expression.substitute]
  | @tensor a P Q hP hQ =>
      dsimp only [completedSubstitution, completedValue, comparison,
        systemSubstitution, Expression.substitute, Functor.comp_map, Functor.prod'_map,
        Functor.mapIso_hom, Iso.prod]
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      have h :
          (Prod.mkHom
              (completedSubstitution l E σ P
                (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))).hom
              (completedSubstitution l E σ Q
                (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))).hom ≫
            Prod.mkHom ((completedValue l E P).map (fun k ↦ comparison l E M (σ k) N))
              ((completedValue l E Q).map (fun k ↦ comparison l E M (σ k) N))) ≫
            Prod.mkHom
              (comparison l E M P (fun k ↦ (systemValue l E M (σ k)).obj N))
              (comparison l E M Q (fun k ↦ (systemValue l E M (σ k)).obj N)) =
          Prod.mkHom (comparison l E M (P.substitute σ) N)
              (comparison l E M (Q.substitute σ) N) ≫
            Prod.mkHom
              ((coefficientSequenceLimit l E _).map (systemSubstitution l E M σ P N).hom)
              ((coefficientSequenceLimit l E _).map
                (systemSubstitution l E M σ Q N).hom) := by
        ext
        · simpa only [prod_comp, Prod.mkHom, Category.assoc] using hP
        · simpa only [prod_comp, Prod.mkHom, Category.assoc] using hQ
      rw [h, Functor.map_comp, Category.assoc, tensorComparison_naturality]
      simp only [Category.assoc]
  | @pullback a b f P hP =>
      dsimp only [completedSubstitution, completedValue, comparison,
        systemSubstitution, Expression.substitute, Functor.comp_map, Functor.mapIso_hom]
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        Category.assoc, hP, Functor.map_comp, Category.assoc,
        pullbackComparison_naturality]
      simp only [Category.assoc]

private theorem comparisonLaws_of_primitive (h : PrimitiveLaws l E M) :
    ComparisonLaws.{t, u, s, i} l E M := by
  have hn : ∀ {I : Type i} {location : I → S} {a : S}
      (P : Expression W location a)
      (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))),
      (∀ k, IsNormalizedCoefficientSequence l E _ (N k)) →
        IsNormalizedCoefficientSequence l E _ ((systemValue l E M P).obj N) := by
    intro I location a P N hN
    induction P with
    | input k => exact hN k
    | unit a => exact h.unit a
    | tensor P Q hP hQ => exact h.tensor _ _ _ hP hQ
    | pullback f P hP => exact h.pullback f _ hP
  have hi : ∀ {I : Type i} {location : I → S} {a : S}
      (P : Expression W location a)
      (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))),
      (∀ k, IsNormalizedCoefficientSequence l E _ (N k)) →
        IsIso (comparison l E M P N) := by
    intro I location a P N hN
    induction P with
    | input k => dsimp only [comparison]; infer_instance
    | unit a => dsimp only [comparison]; infer_instance
    | @tensor a P Q hP hQ =>
        have := hP
        have := hQ
        have := h.counit a _ (hn P N hN)
        have := h.counit a _ (hn Q N hN)
        have : IsIso (Prod.mkHom (comparison l E M P N) (comparison l E M Q N)) :=
          (isIso_prod_iff _ _).2 ⟨hP, hQ⟩
        have : IsIso (Prod.mkHom
            ((M.calculus a).adjunction.counit.app ((systemValue l E M P).obj N))
            ((M.calculus a).adjunction.counit.app ((systemValue l E M Q).obj N))) :=
          (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
        dsimp only [comparison, tensorComparison]
        infer_instance
    | @pullback a b f P hP =>
        have := hP
        have := h.counit b _ (hn P N hN)
        dsimp only [comparison, pullbackComparison]
        infer_instance
  refine ⟨h.counit, hn, ?_, ?_, ?_⟩
  · intro I location a P N hN
    have := hi P N hN
    have := h.counit a _ (hn P N hN)
    exact ⟨inferInstance, by dsimp only [reductionComparison]; infer_instance⟩
  · intro I location a P N N' hN hN' v
    exact comparison_naturality l E M P N N' v
  · intro I location a P N hN m n hmn
    exact ((coefficientSequenceDerivedTransition l E (W a) hmn).naturality
      (reductionComparison l E M P N)).symm

private theorem structuralLaw_of_invertible
    (hβ : ∀ {I : Type i} {location : I → S} {a : S}
      (P : Expression W location a)
      (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))),
      (∀ k, IsNormalizedCoefficientSequence l E _ (N k)) →
        IsIso (comparison l E M P N)) : StructuralLaw.{t, u, s, i} l E M := by
  intro I location a P Q α N hN
  have := hβ P N hN
  have := hβ Q N hN
  let bP := asIso (comparison l E M P N)
  let bQ := asIso (comparison l E M Q N)
  let c := bP ≪≫ (coefficientSequenceLimit l E (W a)).mapIso
    (structuralValue l E M α N) ≪≫ bQ.symm
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · simp [c, bP, bQ, Category.assoc]
  · dsimp only [reductionComparison]
    have h : c.hom ≫ comparison l E M Q N = comparison l E M P N ≫
        (coefficientSequenceLimit l E _).map (structuralValue l E M α N).hom := by
      simp [c, bP, bQ, Category.assoc]
    rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc]
    simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
      congrArg ((M.calculus a).reduction.map (comparison l E M P N) ≫ ·)
        ((M.calculus a).adjunction.counit.naturality
          (structuralValue l E M α N).hom)
  · intro d hd
    apply Iso.ext
    apply (cancel_mono (comparison l E M Q N)).1
    rw [hd.1]
    simp [c, bP, bQ, Category.assoc]

end WeilConjectures.CompletedOperations
