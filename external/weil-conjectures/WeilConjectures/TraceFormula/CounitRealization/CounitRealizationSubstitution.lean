/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherence
public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.TraceFormula.Scalar.ScalarModelAssociativity
import WeilConjectures.TraceFormula.Scalar.ScalarModelUnit
import WeilConjectures.TraceFormula.Supporting.EffectiveComparisonRealizationModels

/-! # Whole-counit substitution in integral realization

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok; Bhatt--Scholze,
Definition 3.4.10, Proposition 3.5.1 and Lemma 3.5.7; blueprint main-20261015,
prop-trf-karoubi-independence, final common-stage transport sentence
(blueprint: lem-trf-counit-realization-substitution).

Words retain their parentheses, and all their maps are maps of entire derived
quotient systems. Inverses are supplied only by the asserted invertibility laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.CounitRealization

/-- Bundling the finite extensions already defined by the coefficient dependency.
Source: blueprint coefficient conventions; Stacks 0941
(blueprint: lem-trf-counit-realization-substitution). -/
structure Coefficient (l : ℕ) [Fact l.Prime] where
  /-- A finite extension of the specified p-adic field. -/
  carrier : Type u
  /-- Its field structure. -/
  field : Field carrier
  /-- Its specified p-adic algebra structure. -/
  algebra : Algebra ℚ_[l] carrier
  /-- Finiteness over the p-adic field. -/
  finite : FiniteDimensional ℚ_[l] carrier

attribute [instance] Coefficient.field Coefficient.algebra Coefficient.finite

variable (l : ℕ) [Fact l.Prime]

/-- A coefficient field and an allowed scheme, used only to index composable words.
Source: the standing scheme hypothesis in Stacks 0941 and the blueprint transport
(blueprint: lem-trf-counit-realization-substitution). -/
structure Location where
  /-- The coefficient extension. -/
  coefficient : Coefficient.{u} l
  /-- The small pro-etale site's scheme. -/
  scheme : Scheme.{u}
  /-- The standing invertibility condition. -/
  invertible : ∀ x : scheme, Invertible (l : scheme.residueField x)

attribute [instance] Location.invertible

/-- The two primitive operations, with their actual source and target.
Source: Stacks 0941, 06YY, 0D6D
(blueprint: lem-trf-counit-realization-substitution). -/
inductive Primitive : Location.{u} l → Location.{u} l → Type (u + 1)
  | pullback (E : Coefficient.{u} l) {X Y : Scheme.{u}}
      [hX : ∀ x : X, Invertible (l : X.residueField x)]
      [hY : ∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :
      Primitive ⟨E, Y, hY⟩ ⟨E, X, hX⟩
  | scalar (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
      (X : Scheme.{u}) [hX : ∀ x : X, Invertible (l : X.residueField x)] :
      Primitive ⟨E, X, hX⟩ ⟨L, X, hX⟩

/-- A finite composable word, including the empty word and arbitrary parentheses.
Source: Stacks 0941, substitution expansion
(blueprint: lem-trf-counit-realization-substitution). -/
inductive Word : Location.{u} l → Location.{u} l → Type (u + 1)
  | nil (a : Location.{u} l) : Word a a
  | atom {a b : Location.{u} l} : Primitive l a b → Word a b
  | comp {a b c : Location.{u} l} : Word a b → Word b c → Word a c

/-- The supplied normalized models, without any invertibility or coherence conclusions.
Source: Stacks 0941 and the prescribed realization-model dependency
(blueprint: lem-trf-counit-realization-substitution). -/
structure Models where
  /-- The whole-system adjunction, with its fixed reduction and realization. -/
  system : ∀ a : Location.{u} l,
    CoefficientDerivedSystemCalculus l a.coefficient.carrier a.scheme
  /-- The natural total-limit/Roos comparison with its K-injective normalization. -/
  roos : ∀ a : Location.{u} l,
    IntegralComparisonRoosModel l a.coefficient.carrier a.scheme
  /-- Each primitive pullback has its prescribed representative normalization. -/
  pullback : ∀ (E : Coefficient.{u} l) {X Y : Scheme.{u}}
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y),
    IntegralComparisonPullbackModel l E.carrier f (system ⟨E, Y, hY⟩) (roos ⟨E, X, hX⟩)
  /-- Each scalar primitive has its quotient/zero-shifted-product normalization. -/
  scalar : ∀ (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
    (X : Scheme.{u}) [hX : ∀ x : X, Invertible (l : X.residueField x)],
    IntegralComparisonScalarModel l E.carrier L.carrier ι X
      (system ⟨E, X, hX⟩) (roos ⟨L, X, hX⟩)

variable {l}

/-- Primitive evaluation in the category of entire derived quotient systems.
Source: Stacks 0941, 06YY (blueprint: lem-trf-counit-realization-substitution). -/
def Primitive.system {a b : Location.{u} l} (O : Primitive l a b) :
    coefficientSequenceDerived l a.coefficient.carrier a.scheme ⥤
      coefficientSequenceDerived l b.coefficient.carrier b.scheme :=
  match O with
  | @Primitive.pullback _ _ E X Y hX hY f => integralComparisonDerivedSequencePullback l E.carrier f
  | @Primitive.scalar _ _ E L ι X hX =>
      integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι X

/-- Primitive evaluation by the recorded completed operations.
Source: Stacks 0941, 06YY (blueprint: lem-trf-counit-realization-substitution). -/
def Primitive.completed {a b : Location.{u} l} (O : Primitive l a b) :
    DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme) ⥤
      DerivedCategory (scalarReductionSource l b.coefficient.carrier b.scheme) :=
  match O with
  | @Primitive.pullback _ _ E X Y hX hY f => integralDerivedPullback l E.carrier f
  | @Primitive.scalar _ _ E L ι X hX => integralScalarExtensionOfUniverses l E.carrier L.carrier ι X

/-- The prescribed primitive model isomorphism b, with no further choice.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Primitive.model (M : Models.{u} l) {a b : Location.{u} l} (O : Primitive l a b) :
    O.completed ≅ (M.system a).reduction ⋙ O.system ⋙
      coefficientSequenceLimit l b.coefficient.carrier b.scheme :=
  match O with
  | @Primitive.pullback _ _ E X Y hX hY f => (M.pullback E f).realization
  | @Primitive.scalar _ _ E L ι X hX => (M.scalar E L ι X).realization

/-- The primitive map r is exactly b followed by L(O(e_C)).
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Primitive.comparison (M : Models.{u} l) {a b : Location.{u} l} (O : Primitive l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme) :
    O.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ⟶
      (coefficientSequenceLimit l b.coefficient.carrier b.scheme).obj (O.system.obj C) :=
  (O.model M).hom.app _ ≫
    (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map
      (O.system.map ((M.system a).adjunction.counit.app C))

/-- Evaluation of a parenthesized word on entire systems.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Word.system {a b : Location.{u} l} (w : Word l a b) :
    coefficientSequenceDerived l a.coefficient.carrier a.scheme ⥤
      coefficientSequenceDerived l b.coefficient.carrier b.scheme :=
  match w with
  | .nil _ => 𝟭 _
  | .atom O => O.system
  | .comp w v => w.system ⋙ v.system

/-- The corresponding completed word with identical parentheses.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Word.completed {a b : Location.{u} l} (w : Word l a b) :
    DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme) ⥤
      DerivedCategory (scalarReductionSource l b.coefficient.carrier b.scheme) :=
  match w with
  | .nil _ => 𝟭 _
  | .atom O => O.completed
  | .comp w v => w.completed ⋙ v.completed

/-- Iterating precisely the primitive counit maps: r_vw = v-hat(r_w) followed by r_v.
Source: Stacks 0941, word substitution
(blueprint: lem-trf-counit-realization-substitution). -/
def Word.comparison (M : Models.{u} l) {a b : Location.{u} l} (w : Word l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme) :
    w.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ⟶
      (coefficientSequenceLimit l b.coefficient.carrier b.scheme).obj (w.system.obj C) :=
  match w with
  | .nil _ => 𝟙 _
  | .atom O => O.comparison M C
  | .comp w v => v.completed.map (w.comparison M C) ≫ v.comparison M (w.system.obj C)

/-- The domain restriction requires constructible-complete intermediate realizations.
Normalization of the intermediate systems is a conclusion, not an added assumption.
Source: Stacks 0941, effective-model domain
(blueprint: lem-trf-counit-realization-substitution). -/
def Word.Allowed {a b : Location.{u} l} (w : Word l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme) : Prop :=
  match w with
  | .nil a => sfIntegralConstructible l a.coefficient.carrier a.scheme
      ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C)
  | .atom O =>
      sfIntegralConstructible l a.coefficient.carrier a.scheme
          ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ∧
        sfIntegralConstructible l b.coefficient.carrier b.scheme
          ((coefficientSequenceLimit l b.coefficient.carrier b.scheme).obj (O.system.obj C))
  | .comp w v => w.Allowed C ∧ v.Allowed (w.system.obj C)

/-- Transport of an entire-system comparison by the iterated counit maps.
The explicit invertibility argument is the conclusion of the theorem below.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Word.transport (M : Models.{u} l) {a b : Location.{u} l} (w v : Word l a b)
    (t : w.system ⟶ v.system)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    [IsIso (v.comparison M C)] :
    w.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ⟶
      v.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) :=
  w.comparison M C ≫ (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map
    (t.app C) ≫ inv (v.comparison M C)

/-- All specified comparison generators, closed under inverse, composition, and both
whiskerings. The constraints are the recorded generator-normalized system maps.
Source: Stacks 0941, 06YY, 0D6D
(blueprint: lem-trf-counit-realization-substitution). -/
inductive Comparison : {a b : Location.{u} l} → Word l a b → Word l a b → Type (u + 1)
  | pullbackComp (E : Coefficient.{u} l) {X Y Z : Scheme.{u}}
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)]
      [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :
      Comparison (.atom (.pullback E (f ≫ g)))
        (.comp (.atom (.pullback E g)) (.atom (.pullback E f)))
  | pullbackUnit (E : Coefficient.{u} l) (X : Scheme.{u})
      [hX : ∀ x : X, Invertible (l : X.residueField x)] :
      Comparison (.atom (.pullback E (𝟙 X))) (.nil ⟨E, X, hX⟩)
  | scalarPullback (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
      {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :
      Comparison (.comp (.atom (.pullback E f)) (.atom (.scalar E L ι X)))
        (.comp (.atom (.scalar E L ι Y)) (.atom (.pullback L f)))
  | scalarComp (E L F : Coefficient.{u} l)
      (ι : E.carrier →ₐ[ℚ_[l]] L.carrier) (j : L.carrier →ₐ[ℚ_[l]] F.carrier)
      (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
      Comparison (.comp (.atom (.scalar E L ι X)) (.atom (.scalar L F j X)))
        (.atom (.scalar E F (j.comp ι) X))
  | scalarUnit (E : Coefficient.{u} l) (X : Scheme.{u})
      [hX : ∀ x : X, Invertible (l : X.residueField x)] :
      Comparison (.atom (.scalar E E (AlgHom.id ℚ_[l] E.carrier) X)) (.nil ⟨E, X, hX⟩)
  | associator {a b c d : Location.{u} l}
      (w : Word l a b) (v : Word l b c) (z : Word l c d) :
      Comparison (.comp (.comp w v) z) (.comp w (.comp v z))
  | unitSource {a b : Location.{u} l} (w : Word l a b) :
      Comparison (.comp (.nil a) w) w
  | unitTarget {a b : Location.{u} l} (w : Word l a b) :
      Comparison (.comp w (.nil b)) w
  | identity {a b : Location.{u} l} (w : Word l a b) : Comparison w w
  | inverse {a b : Location.{u} l} {w v : Word l a b} : Comparison w v → Comparison v w
  | compose {a b : Location.{u} l} {w v z : Word l a b} :
      Comparison w v → Comparison v z → Comparison w z
  | left {a b c : Location.{u} l} {w v : Word l a b} :
      Comparison w v → (z : Word l b c) → Comparison (.comp w z) (.comp v z)
  | right {a b c : Location.{u} l} (z : Word l a b) {w v : Word l b c} :
      Comparison w v → Comparison (.comp z w) (.comp z v)

/-- Evaluation of the named constraints as isomorphisms of whole-system functors.
Source: Stacks 0941, 06YY, 0D6D
(blueprint: lem-trf-counit-realization-substitution). -/
def Comparison.system {a b : Location.{u} l} {w v : Word l a b}
    (t : Comparison w v) : w.system ≅ v.system :=
  match t with
  | @Comparison.pullbackComp _ _ E X Y Z hX hY hZ f g =>
      integralComparisonSystemComposition l E.carrier f g
  | @Comparison.pullbackUnit _ _ E X hX => integralComparisonSystemUnit l E.carrier X
  | @Comparison.scalarPullback _ _ E L ι X Y hX hY f =>
      integralComparisonSystemScalarPullback l E.carrier L.carrier ι f
  | @Comparison.scalarComp _ _ E L F ι j X hX =>
      integralComparisonSystemScalarComposition l E.carrier L.carrier F.carrier ι j X
  | @Comparison.scalarUnit _ _ E X hX => integralComparisonSystemScalarUnit l E.carrier X
  | .associator w v z => Functor.associator w.system v.system z.system
  | .unitSource w => Functor.leftUnitor w.system
  | .unitTarget w => Functor.rightUnitor w.system
  | .identity _ => Iso.refl _
  | .inverse t => t.system.symm
  | .compose t s => t.system ≪≫ s.system
  | .left t z => Functor.isoWhiskerRight t.system z.system
  | .right z t => Functor.isoWhiskerLeft z.system t.system

/-- The coherent reduction of the recursive comparison, still an entire-system map.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Word.reductionComparison (M : Models.{u} l) {a b : Location.{u} l} (w : Word l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme) :=
  (M.system b).reduction.map (w.comparison M C) ≫
    (M.system b).adjunction.counit.app (w.system.obj C)

/-- Primitive whole-counit insertion at an arbitrary completed input.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Primitive.reductionComparison (M : Models.{u} l) {a b : Location.{u} l}
    (O : Primitive l a b)
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme)) :=
  (M.system b).reduction.map ((O.model M).hom.app K) ≫
    (M.system b).adjunction.counit.app (O.system.obj ((M.system a).reduction.obj K))

/-- The word assertions, separated from the scalar formulas only to keep elaboration small.
Every hypothesis is the stated normalized constructible-complete domain restriction.
Source: Stacks 0941, whole-counit substitution
(blueprint: lem-trf-counit-realization-substitution). -/
structure WordLaws (M : Models.{u} l) : Prop where
  /-- Effectivity concerns the actual canonical counit in the derived system category. -/
  counit : ∀ (a : Location.{u} l)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme),
    IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C →
      IsIso ((M.system a).adjunction.counit.app C)
  /-- All word maps are isomorphisms; normalization propagates to intermediate systems. -/
  invertible : ∀ {a b : Location.{u} l} (w : Word l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme),
    IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C → w.Allowed C →
      IsIso (w.comparison M C) ∧
        IsNormalizedCoefficientSequence l b.coefficient.carrier b.scheme (w.system.obj C)
  /-- Naturality is for arbitrary morphisms of entire derived systems. -/
  naturality : ∀ {a b : Location.{u} l} (w : Word l a b)
    (C D : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (_hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (_hD : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme D)
    (_hAC : w.Allowed C) (_hAD : w.Allowed D) (φ : C ⟶ D),
    w.completed.map ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).map φ) ≫
        w.comparison M D = w.comparison M C ≫
      (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map (w.system.map φ)
  /-- The displayed cut formula, including empty blocks. -/
  cut : ∀ {a b c : Location.{u} l} (w : Word l a b) (v : Word l b c)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme),
    (Word.comp w v).comparison M C =
      v.completed.map (w.comparison M C) ≫ v.comparison M (w.system.obj C)
  /-- No parentheses change the iterated whole-counit map. -/
  parenthesization : ∀ {a b c d : Location.{u} l}
    (w : Word l a b) (v : Word l b c) (z : Word l c d)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme),
    (Word.comp (Word.comp w v) z).comparison M C =
      (Word.comp w (Word.comp v z)).comparison M C
  /-- Inserting the entire counit before the next primitive gives the same map. -/
  wholeCounit : ∀ {a b : Location.{u} l} (O : Primitive l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme),
    (Word.atom O).reductionComparison M C =
      O.reductionComparison M
          ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ≫
        O.system.map ((M.system a).adjunction.counit.app C)
  /-- Transport is the unique completed arrow with the prescribed realization square. -/
  comparison : ∀ {a b : Location.{u} l} {w v : Word l a b} (t : Comparison w v)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (_hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (_hw : w.Allowed C) (_hv : v.Allowed C),
    ∃! q : w.completed.obj
        ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ≅
        v.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C),
      q.hom ≫ v.comparison M C = w.comparison M C ≫
        (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map (t.system.hom.app C)
  /-- Composing comparisons cancels the middle word identification. -/
  composition : ∀ {a b : Location.{u} l} (w v z : Word l a b)
    (t : Comparison w v) (s : Comparison v z)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    [IsIso (v.comparison M C)] [IsIso (z.comparison M C)],
    w.transport M v t.system.hom C ≫ v.transport M z s.system.hom C =
      w.transport M z (t.system.hom ≫ s.system.hom) C
  /-- Inverting a comparison gives the inverse completed arrow. -/
  inverse : ∀ {a b : Location.{u} l} (w v : Word l a b) (t : Comparison w v)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    [IsIso (w.comparison M C)] [IsIso (v.comparison M C)],
    w.transport M v t.system.hom C ≫ v.transport M w t.system.inv C = 𝟙 _
  /-- The formula persists after every further completed operation on the left. -/
  leftWhisker : ∀ {a b c : Location.{u} l} (w v : Word l a b)
    (t : Comparison w v) (z : Word l b c)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    [IsIso (v.comparison M C)] [IsIso ((Word.comp v z).comparison M C)],
    (Word.comp w z).transport M (Word.comp v z) (t.left z).system.hom C =
      z.completed.map (w.transport M v t.system.hom C)
  /-- Right whiskering uses the canonical comparison for the inserted input word. -/
  rightWhisker : ∀ {a b c : Location.{u} l} (z : Word l a b) (w v : Word l b c)
    (t : Comparison w v)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    [IsIso (v.comparison M (z.system.obj C))]
    [IsIso ((Word.comp z v).comparison M C)],
    (Word.comp z w).transport M (Word.comp z v) (t.right z).system.hom C ≫
        v.completed.map (z.comparison M C) =
      w.completed.map (z.comparison M C) ≫
        w.transport M v t.system.hom (z.system.obj C)

/-- The scalar letter, using the already defined whole-system and completed scalar changes.
Source: Stacks 06YY (blueprint: lem-trf-counit-realization-substitution). -/
def scalarWord (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
    (X : Scheme.{u}) [hX : ∀ x : X, Invertible (l : X.residueField x)] :
    Word l ⟨E, X, hX⟩ ⟨L, X, hX⟩ := .atom (.scalar E L ι X)

/-- Scalar normalization means the realized system associator is the ordinary tensor
associator conjugated by the actual quotient-normalized completion maps chi.
The published associator and unit definitions expand to exactly that formula.
Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1 and Lemma 3.5.7
(blueprint: lem-trf-counit-realization-substitution). -/
structure ScalarLaws (M : Models.{u} l) : Prop where
  /-- The entire-system associator is the chi-conjugated ordinary derived associator. -/
  associator : ∀ (E L F : Coefficient.{u} l)
    (ι : E.carrier →ₐ[ℚ_[l]] L.carrier) (j : L.carrier →ₐ[ℚ_[l]] F.carrier)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (C : coefficientSequenceDerived l E.carrier X)
    (_hN : IsNormalizedCoefficientSequence l E.carrier X C)
    (hC : sfIntegralConstructible l E.carrier X
      ((coefficientSequenceLimit l E.carrier X).obj C))
    (_hA : (Word.comp (scalarWord E L ι X) (scalarWord L F j X)).Allowed C)
    (_hDirect : (scalarWord E F (j.comp ι) X).Allowed C),
    (Word.comp (scalarWord E L ι X) (scalarWord L F j X)).comparison M C ≫
        (coefficientSequenceLimit l F.carrier X).map
          ((integralComparisonSystemScalarComposition l E.carrier L.carrier F.carrier
            ι j X).hom.app C) =
      (CompletedLineTensor.associator l E.carrier X L.carrier ι F.carrier j
        ((coefficientSequenceLimit l E.carrier X).obj C)
        (CompletedLineTensor.intrinsic_complete l E.carrier X ⟨_, hC⟩)).hom ≫
          (scalarWord E F (j.comp ι) X).comparison M C
  /-- Identity scalar change realizes to multiplication and completeness, including E=L. -/
  unit : ∀ (E : Coefficient.{u} l) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (C : coefficientSequenceDerived l E.carrier X)
    (_hN : IsNormalizedCoefficientSequence l E.carrier X C)
    (hC : sfIntegralConstructible l E.carrier X
      ((coefficientSequenceLimit l E.carrier X).obj C))
    (_hA : (scalarWord E E (AlgHom.id ℚ_[l] E.carrier) X).Allowed C),
    (scalarWord E E (AlgHom.id ℚ_[l] E.carrier) X).comparison M C ≫
        (coefficientSequenceLimit l E.carrier X).map
          ((integralComparisonSystemScalarUnit l E.carrier X).hom.app C) =
      (CompletedLineTensor.unit l E.carrier X
        ((coefficientSequenceLimit l E.carrier X).obj C)
        (CompletedLineTensor.intrinsic_complete l E.carrier X ⟨_, hC⟩)).hom

private theorem normalized_iso (a : Location.{u} l)
    {C D : coefficientSequenceDerived l a.coefficient.carrier a.scheme} (e : C ≅ D)
    (hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C) :
    IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme D := by
  intro m n h P
  let V := coefficientSequenceDerivedEvaluation l a.coefficient.carrier a.scheme
  let R := normalizedDVRRes l a.coefficient.carrier a.scheme h
  let t := coefficientSequenceDerivedTransition l a.coefficient.carrier a.scheme h
  have hn : (V m).map e.hom ≫ t.app D = t.app C ≫ R.map ((V n).map e.hom) :=
    t.naturality e.hom
  constructor
  · intro f g hfg
    apply (cancel_epi ((V n).map e.hom)).1
    apply (hC h P).1
    change t.app C ≫ R.map ((V n).map e.hom ≫ f) =
      t.app C ≫ R.map ((V n).map e.hom ≫ g)
    rw [R.map_comp, R.map_comp, ← Category.assoc, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using
      congrArg (fun k ↦ (V m).map e.hom ≫ k) hfg
  · intro k
    obtain ⟨f, hf⟩ := (hC h P).2 ((V m).map e.hom ≫ k)
    refine ⟨(V n).map e.inv ≫ f, ?_⟩
    apply (cancel_epi ((V m).map e.hom)).1
    change (V m).map e.hom ≫ t.app D ≫ R.map ((V n).map e.inv ≫ f) = _
    rw [← Category.assoc, hn, Category.assoc, ← R.map_comp]
    simpa using hf

private theorem counit_iso (M : Models.{u} l) (a : Location.{u} l)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C) :
    IsIso ((M.system a).adjunction.counit.app C) := by
  have hl : IsUnit (l : Γ(a.scheme, ⊤)) := by
    apply AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ a.scheme.toSheafedSpace ⊤
    intro x hx
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (isUnit_of_invertible (l : a.scheme.residueField x)).ne_zero
  exact ((purNormalizedReconstruction l a.coefficient.carrier a.scheme hl
    (M.system a)).1 C hC).2

private theorem primitive_normalized (M : Models.{u} l) {a b : Location.{u} l}
    (O : Primitive l a b) (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (hK : sfIntegralConstructible l a.coefficient.carrier a.scheme
      ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C)) :
    IsNormalizedCoefficientSequence l b.coefficient.carrier b.scheme (O.system.obj C) := by
  let := counit_iso M a C hC
  obtain ⟨T⟩ := effectiveComparisonRealizationModels.{u} l
  let K := (coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C
  cases O with
  | @pullback E X Y hX hY f =>
    let e := (T.system E.carrier Y).adjunction.leftAdjointUniq
      (M.system ⟨E, Y, hY⟩).adjunction
    apply normalized_iso ⟨E, X, hX⟩
      ((integralComparisonDerivedSequencePullback l E.carrier f).mapIso
        (e.app K ≪≫ asIso ((M.system ⟨E, Y, hY⟩).adjunction.counit.app C)))
    exact (T.pullback_effective E.carrier f ⟨K, hK⟩).1
  | @scalar E L ι X hX =>
    let e := (T.system E.carrier X).adjunction.leftAdjointUniq
      (M.system ⟨E, X, hX⟩).adjunction
    apply normalized_iso ⟨L, X, hX⟩
      ((integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι X).mapIso
        (e.app K ≪≫ asIso ((M.system ⟨E, X, hX⟩).adjunction.counit.app C)))
    exact (T.scalar_effective E.carrier L.carrier ι X ⟨K, hK⟩).1

private theorem word_invertible (M : Models.{u} l) {a b : Location.{u} l}
    (w : Word l a b) (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (hA : w.Allowed C) : IsIso (w.comparison M C) ∧
      IsNormalizedCoefficientSequence l b.coefficient.carrier b.scheme (w.system.obj C) := by
  induction w with
  | nil a => exact ⟨inferInstanceAs (IsIso (𝟙 _)), hC⟩
  | atom O =>
    let := counit_iso M _ C hC
    refine ⟨?_, primitive_normalized M O C hC hA.1⟩
    dsimp only [Word.comparison, Primitive.comparison]
    infer_instance
  | comp w v ihw ihv =>
    obtain ⟨hw, hn⟩ := ihw C hC hA.1
    obtain ⟨hv, hn'⟩ := ihv (w.system.obj C) hn hA.2
    let := hw
    let := hv
    exact ⟨inferInstanceAs
      (IsIso (v.completed.map (w.comparison M C) ≫ v.comparison M (w.system.obj C))), hn'⟩

private theorem word_naturality (M : Models.{u} l) {a b : Location.{u} l}
    (w : Word l a b) {C D : coefficientSequenceDerived l a.coefficient.carrier a.scheme}
    (φ : C ⟶ D) :
    w.completed.map ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).map φ) ≫
        w.comparison M D = w.comparison M C ≫
      (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map (w.system.map φ) := by
  induction w with
  | nil a => simp [Word.comparison, Word.completed, Word.system]
  | @atom a b O =>
    dsimp only [Word.completed, Word.system, Word.comparison, Primitive.comparison]
    rw [← Category.assoc, (O.model M).hom.naturality]
    dsimp only [Functor.comp_map]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 1
    exact congrArg
      (fun f ↦
        (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map (O.system.map f))
      ((M.system a).adjunction.counit.naturality φ)
  | comp w v ihw ihv =>
    dsimp only [Word.completed, Word.system, Word.comparison, Functor.comp_map]
    rw [← Category.assoc, ← v.completed.map_comp, ihw, v.completed.map_comp,
      Category.assoc, ihv]
    simp only [Category.assoc]

private theorem word_laws (M : Models.{u} l) : WordLaws M := by
  refine ⟨counit_iso M, word_invertible M, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b w C D hC hD hAC hAD φ
    exact word_naturality M w φ
  · intro a b c w v C
    rfl
  · intro a b c d w v z C
    simp only [Word.comparison, Word.completed, Word.system, Functor.map_comp,
      Functor.comp_map, Functor.comp_obj, Category.assoc]
  · intro a b O C
    dsimp only [Word.reductionComparison, Word.comparison, Primitive.comparison,
      Primitive.reductionComparison]
    have h := (M.system b).adjunction.counit.naturality
      (O.system.map ((M.system a).adjunction.counit.app C))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at h ⊢
    simpa only [Word.system, Word.completed, Functor.comp_obj, Functor.map_comp,
      Category.assoc] using congrArg
      (fun f ↦ (M.system b).reduction.map
        ((O.model M).hom.app
          ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C)) ≫ f) h
  · intro a b w v t C hC hw hv
    let := (word_invertible M w C hC hw).1
    let := (word_invertible M v C hC hv).1
    let q := asIso (w.comparison M C) ≪≫
      (coefficientSequenceLimit l b.coefficient.carrier b.scheme).mapIso (t.system.app C) ≪≫
        (asIso (v.comparison M C)).symm
    refine ⟨q, ?_, ?_⟩
    · simp [q, Category.assoc]
    · intro q' hq'
      apply Iso.ext
      apply (cancel_mono (v.comparison M C)).1
      exact hq'.trans (by simp [q, Category.assoc])
  · intro a b w v z t s C hv hz
    simp only [Word.transport, NatTrans.comp_app, Functor.map_comp, Category.assoc,
      IsIso.inv_hom_id_assoc]
  · intro a b w v t C hw hv
    simp only [Word.transport, Category.assoc, IsIso.inv_hom_id_assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, IsIso.hom_inv_id]
  · intro a b c w v t z C hv hvz
    apply (cancel_mono ((Word.comp v z).comparison M C)).1
    dsimp only [Word.transport]
    simp only [Category.assoc, IsIso.inv_hom_id]
    dsimp only [Comparison.system, Word.comparison, Word.system, Word.completed,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    have hn := word_naturality M z (t.system.hom.app C)
    simp only [Functor.map_comp, Functor.comp_obj, Category.assoc, Category.comp_id]
    rw [← hn]
    simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id, Category.comp_id]
  · intro a b c z w v t C hv hzv
    have hi : IsIso (v.completed.map (z.comparison M C) ≫
        v.comparison M (z.system.obj C)) := hzv
    apply (cancel_mono (v.comparison M (z.system.obj C))).1
    dsimp only [Word.transport]
    simp only [Category.assoc, IsIso.inv_hom_id]
    dsimp only [Word.comparison, Word.system, Word.completed, Comparison.system,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.comp_obj]
    have hc := IsIso.inv_hom_id
      (v.completed.map (z.comparison M C) ≫ v.comparison M (z.system.obj C))
    simpa only [Category.assoc, Category.comp_id] using congrArg
      (fun f ↦ w.completed.map (z.comparison M C) ≫
        w.comparison M (z.system.obj C) ≫
        (coefficientSequenceLimit l c.coefficient.carrier c.scheme).map
          (t.system.hom.app (z.system.obj C)) ≫ f) hc

private theorem scalar_laws (M : Models.{u} l) : ScalarLaws M := by
  constructor
  · intro E L F ι j X hX C hN hC hA hDirect
    let K := (coefficientSequenceLimit l E.carrier X).obj C
    let hK := CompletedLineTensor.intrinsic_complete l E.carrier X ⟨K, hC⟩
    let S := integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι X
    let T := integralComparisonDerivedSequenceScalar l L.carrier F.carrier j X
    let U := integralComparisonDerivedSequenceScalar l E.carrier F.carrier (j.comp ι) X
    let LE := coefficientSequenceLimit l E.carrier X
    let LL := coefficientSequenceLimit l L.carrier X
    let LF := coefficientSequenceLimit l F.carrier X
    let B := integralScalarExtensionOfUniverses l L.carrier F.carrier j X
    let D := completedDerivedScalarExtension l L.carrier F.carrier j X
    let b := M.scalar E L ι X
    let c := M.scalar L F j X
    let d := M.scalar E F (j.comp ι) X
    let e := (M.system ⟨E, X, inferInstance⟩).adjunction.counit.app C
    let a := integralComparisonSystemScalarComposition l E.carrier L.carrier F.carrier ι j X
    have hc := c.realization.hom.naturality (LL.map (S.map e))
    have he := (M.system ⟨L, X, inferInstance⟩).adjunction.counit.naturality (S.map e)
    have ha := a.hom.naturality e
    have hs := scalarModelAssociativity l E.carrier L.carrier F.carrier ι j X
      (M.system ⟨E, X, inferInstance⟩) (M.system ⟨L, X, inferInstance⟩)
      (M.roos ⟨L, X, inferInstance⟩) (M.roos ⟨F, X, inferInstance⟩) b c d K
    let χ := CompletedLineTensor.chi l E.carrier X L.carrier ι K hK
    let ψ := CompletedLineTensor.chi l L.carrier X F.carrier j
      ((integralScalarExtensionOfUniverses l E.carrier L.carrier ι X).obj K)
      (CompletedLineTensor.extension_complete l E.carrier X L.carrier ι K hK)
    change D.map χ.hom ≫ ψ.hom ≫ B.map (b.realization.hom.app K) ≫
      c.realization.hom.app (LL.obj (S.obj ((M.system ⟨E, X, hX⟩).reduction.obj K))) ≫
      LF.map (T.map ((M.system ⟨L, X, hX⟩).adjunction.counit.app
        (S.obj ((M.system ⟨E, X, hX⟩).reduction.obj K)))) ≫
      LF.map (a.hom.app ((M.system ⟨E, X, hX⟩).reduction.obj K)) = _ at hs
    apply (cancel_epi (D.map χ.hom ≫ ψ.hom)).1
    dsimp only [scalarWord, Word.comparison, Word.system, Word.completed,
      Primitive.comparison, Primitive.model, Primitive.system, Primitive.completed]
    change (D.map χ.hom ≫ ψ.hom) ≫
      (B.map (b.realization.hom.app K ≫ LL.map (S.map e)) ≫
        (c.realization.hom.app (LL.obj (S.obj C)) ≫
          LF.map (T.map ((M.system ⟨L, X, inferInstance⟩).adjunction.counit.app
            (S.obj C))))) ≫ LF.map (a.hom.app C) = _
    rw [B.map_comp]
    simp only [Category.assoc]
    dsimp only [Functor.comp_map, Functor.id_map] at hc he ha
    rw [reassoc_of% hc]
    have he' := congrArg (fun f ↦ LF.map (T.map f)) he
    simp only [CategoryTheory.Functor.map_comp] at he'
    rw [reassoc_of% he']
    change T.map (S.map e) ≫ a.hom.app C =
      a.hom.app ((M.system ⟨E, X, hX⟩).reduction.obj K) ≫ U.map e at ha
    rw [← LF.map_comp (T.map (S.map e)), ha]
    simp only [Functor.map_comp]
    have hs' := hs =≫ LF.map (U.map e)
    simp only [Category.assoc] at hs'
    rw [hs']
    dsimp only [CompletedLineTensor.associator, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom]
    simp only [Category.assoc]
    change _ = D.map χ.hom ≫ ψ.hom ≫ ψ.inv ≫ D.map χ.inv ≫
      (CompletedLineTensor.associatorData l E.carrier X L.carrier ι F.carrier j).derived.hom.app
        K ≫ (CompletedLineTensor.chi l E.carrier X F.carrier (j.comp ι) K hK).hom ≫
      d.realization.hom.app K ≫ LF.map (U.map e)
    rw [ψ.hom_inv_id_assoc, ← D.map_comp_assoc, χ.hom_inv_id, D.map_id,
      Category.id_comp]
    rfl
  · intro E X hX C hN hC hA
    let K := (coefficientSequenceLimit l E.carrier X).obj C
    let hK := CompletedLineTensor.intrinsic_complete l E.carrier X ⟨K, hC⟩
    let S := M.system ⟨E, X, inferInstance⟩
    let b := M.scalar E E (AlgHom.id ℚ_[l] E.carrier) X
    let L := coefficientSequenceLimit l E.carrier X
    let e := S.adjunction.counit.app C
    let a := integralComparisonSystemScalarUnit l E.carrier X
    have ha := a.hom.naturality e
    have hs := scalarModelUnit l E.carrier X S (M.roos ⟨E, X, inferInstance⟩) b K
    let χ := CompletedLineTensor.chi l E.carrier X E.carrier
      (AlgHom.id ℚ_[l] E.carrier) K hK
    change χ.hom ≫ b.realization.hom.app K ≫
      L.map (a.hom.app (S.reduction.obj K)) = _ at hs
    apply (cancel_epi χ.hom).1
    dsimp only [scalarWord, Word.comparison, Primitive.comparison, Primitive.model,
      Primitive.system]
    change χ.hom ≫ (b.realization.hom.app K ≫
      L.map ((integralComparisonDerivedSequenceScalar l E.carrier E.carrier
        (AlgHom.id ℚ_[l] E.carrier) X).map e)) ≫ L.map (a.hom.app C) = _
    simp only [Category.assoc]
    rw [← L.map_comp]
    rw [show (integralComparisonDerivedSequenceScalar l E.carrier E.carrier
      (AlgHom.id ℚ_[l] E.carrier) X).map e ≫ a.hom.app C =
      a.hom.app (S.reduction.obj K) ≫ e from ha]
    dsimp only [Functor.comp_map, Functor.id_map] at *
    rw [L.map_comp]
    have hs' := hs =≫ L.map e
    simp only [Category.assoc] at hs'
    rw [hs']
    have ht := S.adjunction.right_triangle_components C
    change S.adjunction.unit.app K ≫ L.map e = 𝟙 K at ht
    rw [ht]
    erw [Category.comp_id]
    dsimp only [CompletedLineTensor.unit, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
    change _ = χ.hom ≫ χ.inv ≫ (CompletedLineTensor.ordinaryUnit l E.carrier X).hom.app K
    rw [χ.hom_inv_id_assoc]

/-- Whole-counit substitution and scalar normalization for realized operations.
Source: Stacks 0941, lemma-derived-limit-is-ok; Bhatt--Scholze, Definition 3.4.10,
Proposition 3.5.1 and Lemma 3.5.7; blueprint main-20261015,
prop-trf-karoubi-independence, final common-stage transport sentence
(blueprint: lem-trf-counit-realization-substitution).

Proof, with the scalar representative calculations isolated in their own nodes:
1. purNormalizedReconstruction gives invertibility of the actual adjunction counit
on normalized systems, without bounds. The residue-field invertibility hypothesis
implies the required global invertibility of l by the stalk criterion.
2. A primitive comparison is its prescribed model followed by L(O(e_C)), hence is
invertible. effectiveComparisonRealizationModels makes O(R(K)) normalized on the
constructible-complete domain. Transport normalization along O(e_C); iterate.
3. Apply naturality of the primitive model and of the whole-system counit to an
arbitrary derived-system morphism. This proves primitive comparison naturality,
including inverse arrows, before any separate finite evaluation.
4. Induct on finite words. The empty comparison is identity. Composition is the
stated cut formula. Expanding three consecutive blocks proves parenthesization
independence by associativity and functoriality; repeat for every cut.
5. For two letters move the first model past the image of the second counit by
naturality. Counit naturality then identifies insertion at the intermediate object
with substitution before the next primitive. The triangle identities cancel an
inserted unit. This gives the coherent reductionComparison equation.
6. For each named entire-system comparison, conjugate its realization by the two
word comparisons. Invertibility gives uniqueness. Composition cancels the middle
comparison and its inverse; inversion reverses all factors.
7. Naturality applied to t_C gives left whiskering; evaluating at zC and using the
word cut formula gives right whiskering. Induct to arbitrary further words.
8. scalarModelAssociativity supplies the ambient scalar normalization square,
including the original middle whole-system counit. Naturality of the second scalar
model and the middle counit, then naturality of the system associator, transport
this square through e_C. Cancel the two invertible chi factors. Their conjugation
is exactly the published CompletedLineTensor.associator.
9. scalarModelUnit supplies the ambient identity square with the actual adjunction
unit. Naturality of the system unitor transports it through e_C. The adjunction
triangle cancels the unit and realized counit. Cancel chi and expand the published
CompletedLineTensor.unit. The two scalar nodes carry the strict quotient arguments;
no faithfulness of separate finite reductions, finite Tor-amplitude, or additional
boundedness is used. -/
theorem counitRealizationSubstitution (l : ℕ) [Fact l.Prime] (M : Models.{u} l) :
    WordLaws M ∧ ScalarLaws M := by
  exact ⟨word_laws M, scalar_laws M⟩

end WeilConjectures.CounitRealization
