/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import Mathlib.CategoryTheory.Pi.Basic

/-! # IntegralSystemExpressionDomain

Source: Stacks 0941, 03DI, 07A7 and blueprint fix-prop-coherence,
strict-system operations and bounded finite expressions
(blueprint: def-sf-integral-system-expression-domain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Equality of the two definitions of the adjacent quotient restriction. The
sequence functor maps a successor arrow to its specified transition; scalar
restriction then applies to that same ring-sheaf map.
Source: Stacks 0941 (blueprint: def-sf-integral-system-expression-domain). -/
abbrev originRestrictionEquality (W : Scheme.{u}) (n : ℕ) :
    proEtaleCoefficientRestrictScalars W (Padic.coefficientExtensionTransition l E (n + 1)) =
      normalizedDVRModuleRes l E W (Nat.le_succ n) :=
  congrArg (fun f : integralCoefficientSheaf l E W (n + 1) ⟶
      integralCoefficientSheaf l E W n ↦ SheafOfModules.restrictScalars.{u + 1} f)
    (Functor.ofOpSequence_map_homOfLE_succ (integralCoefficientSheafTransition l E W) n).symm

/-- Compatible etale-origin witnesses at all positive coefficient levels.
Source: Stacks 099R; blueprint: def-sf-integral-system-expression-domain. -/
structure Origins (W : Scheme.{u}) (M : System l E W) where
  /-- The retained etale-origin witness at every positive coefficient level. -/
  level : ∀ n : ℕ, DerivedCategory.Plus
    (Sheaf (ProEt.topology W)
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))))
  origin : ∀ n : ℕ, Nonempty (FixedEtaleOriginWitness W
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (level n))
  /-- The witness levels are the compatible coefficientSequenceDerivedEvaluation levels
      of `M`; the compatibility equations are retained as data at each transition. -/
  evaluation : ∀ n : ℕ,
    (sfIntrinsicModuleEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapDerivedCategory.obj
        (level n).obj ≅
        (coefficientSequenceDerivedEvaluation l E W n).obj M
  /-- The transition on the etale antecedents, before applying the site comparison. -/
  etaleTransition : ∀ n : ℕ,
    (Classical.choice (origin (n + 1))).complex.obj ⟶
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (Padic.coefficientExtensionTransition l E (n + 1)).ulift).obj
          (Classical.choice (origin n)).complex.obj
  /-- The actual fixed-scalar transition on the pro-etale origin levels. -/
  fixedTransition : ∀ n : ℕ, (level (n + 1)).obj ⟶
    (Sheaf.derivedRestrictScalars (ProEt.topology W)
      (Padic.coefficientExtensionTransition l E (n + 1)).ulift).obj (level n).obj
  originSquare : ∀ n : ℕ,
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 2)))) W).mapDerivedCategory.map
          (etaleTransition n) ≫
      (ProEtale.pbcDerivedComparisonRestrict W
        (Padic.coefficientExtensionTransition l E (n + 1)).ulift).inv.app
          (Classical.choice (origin n)).complex.obj ≫
      (Sheaf.derivedRestrictScalars (ProEt.topology W)
        (Padic.coefficientExtensionTransition l E (n + 1)).ulift).map
          (Classical.choice (origin n)).iso.hom =
    (Classical.choice (origin (n + 1))).iso.hom ≫ fixedTransition n
  /-- The fixed-scalar transition is precisely the system's actual quotient map,
      transported by the published realization comparison and equality transport of
      the actual quotient restriction functors. -/
  transitionSquare : ∀ n : ℕ,
    letI := normalizedDVRModuleRes_limits l E W (Nat.le_succ n)
    letI := normalizedDVRModuleRes_colimits l E W (Nat.le_succ n)
    ((sfIntrinsicModuleEquivalence W
        (Padic.coefficientExtensionRing l E (n + 2))).functor.mapDerivedCategory.map
          (fixedTransition n) ≫
      (Functor.mapDerivedCategorySquareIso (sfRealizationRestriction W
        (Padic.coefficientExtensionTransition l E (n + 1)))).inv.app (level n).obj ≫
      (Functor.mapDerivedCategoryNatIso (eqToIso (originRestrictionEquality l E W n))).hom.app
        ((sfIntrinsicModuleEquivalence W
          (Padic.coefficientExtensionRing l E (n + 1))).functor.mapDerivedCategory.obj
            (level n).obj)) =
    ((evaluation (n + 1)).hom ≫
      (coefficientSequenceDerivedTransition l E W (Nat.le_succ n)).app M ≫
        (normalizedDVRRes l E W (Nat.le_succ n)).map (evaluation n).inv)

/-- One common finite cohomological interval and one common finite Tor interval for
all positive levels. Source: blueprint finite-Tor and constructible definitions
(blueprint: def-sf-integral-system-expression-domain). -/
def LevelBounds (W : Scheme.{u}) (M : System l E W) : Prop :=
  ∃ a b c d : ℤ, a ≤ b ∧ c ≤ d ∧ ∀ n : ℕ,
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) W
        ((coefficientSequenceDerivedEvaluation l E W n).obj M) ∧
      proEtaleCohomologicalSupport
        ((coefficientSequenceDerivedEvaluation l E W n).obj M) ⊆ Set.Icc a b ∧
      HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1))
        ((coefficientSequenceDerivedEvaluation l E W n).obj M) c d

/-- The normalized bounded constructible domain. Each actual positive
level has constructible cohomology in one common interval and finite Tor amplitude
in one common interval. Retained
compatible origins are additional data, rather than an unspecified finite-arrow lift.
Source: Stacks 0941; blueprint derived-complete and finite-Tor definitions
(blueprint: def-sf-integral-system-expression-domain). -/
def Good (W : Scheme.{u}) : ObjectProperty (System l E W) := fun M ↦
  IsNormalizedCoefficientSequence l E W M ∧
    LevelBounds l E W M ∧ Nonempty (Origins l E W M)

/-- Operation symbols interpreted in specified categories; this helper stores functors
only. The two interpretations below use actual sequence-site and integral functors.
Source: blueprint fix-prop-coherence, finite expressions
(blueprint: def-sf-integral-system-expression-domain). -/
structure Interpretation (C : Scheme.{u} → Type v) [∀ X, Category.{w} (C X)] where
  pull : ∀ {X Y : Scheme.{u}} (_f : X ⟶ Y), C Y ⥤ C X
  push : ∀ {X Y : Scheme.{u}} (_f : X ⟶ Y), C X ⥤ C Y
  shriek : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], C U ⥤ C X
  tensor : ∀ X : Scheme.{u}, C X × C X ⥤ C X
  /-- Compact support is the chosen compactification composite `S_p J_j`. -/
  compactSupport : ∀ {X Y : Scheme.{u}} (_f : X ⟶ Y) (_c : Compactification _f),
    C X ⥤ C Y

/-- The sequence-site interpretation uses exact pullback, total right-derived image,
exact termwise open extension and the recorded K-flat derived tensor.
Source: Stacks 0941 (blueprint: def-sf-integral-system-expression-domain). -/
def systemInterpretation (o : Operations l E) : Interpretation (System l E) where
  pull := pull l E
  push := Operations.push l E o
  shriek := Operations.shriek l E o
  tensor X := (calculus l E X).systemClosed.tensor
  compactSupport _f c := Operations.shriek l E o c.i ⋙ Operations.push l E o c.g

/-- The integral interpretation uses precisely completed pullback and completed tensor,
ordinary integral proper direct image and localized completed-ring open extension.
Source: Bhatt--Scholze 6.7.6; Stacks 0941
(blueprint: def-sf-integral-system-expression-domain). -/
def integralInterpretation : Interpretation (Integral l E) where
  pull := integralDerivedPullback l E
  push := PurCompactSupport.push (PurCompactSupport.completed l E)
  shriek j := (PurCompactSupport.openExtension (PurCompactSupport.completed l E)
    j).mapDerivedCategory
  tensor := integralCompletedTensor l E
  compactSupport _f c := PurCompactSupport.image (PurCompactSupport.completed l E) c

/-- Finite well-typed expressions, with a finite family of variables at possibly different
schemes. Push symbols are proper; open symbols are quasi-compact. The scheme indices
are objects over the fixed base, so every arrow is a morphism over that base. Tensor
has two inputs at the same scheme. No compact-support symbol changes the prescribed
meaning of the subexpression `S_p J_j`.
Source: blueprint fix-prop-coherence, compactification expressions
(blueprint: def-sf-integral-system-expression-domain). -/
inductive Expression (B : Scheme.{u}) (I : Type u) (X : I → Over B) : Over B →
    Type (u + 1) where
  | var (i : I) : Expression B I X (X i)
  | pull {U V : Over B} (f : U ⟶ V) (e : Expression B I X V) : Expression B I X U
  | push {U V : Over B} (f : U ⟶ V) (hp : IsProper f.left)
      (e : Expression B I X U) : Expression B I X V
  | shriek {U V : Over B} (j : U ⟶ V) (hj : IsOpenImmersion j.left)
      (hqc : QuasiCompact j.left) (e : Expression B I X U) : Expression B I X V
  | compactSupport {U V : Over B} (f : U ⟶ V) (c : Compactification f.left)
      (e : Expression B I X U) : Expression B I X V
  | tensor {W : Over B} (e f : Expression B I X W) : Expression B I X W

/-- Recursive interpretation as a functor of all inputs, retaining all input morphisms.
Source: blueprint fix-prop-coherence, expression induction
(blueprint: def-sf-integral-system-expression-domain). -/
def Expression.evaluate {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] (d : Interpretation C) :
    {W : Over B} → Expression B I X W → (∀ i, C (X i).left) ⥤ C W.left
  | _, .var i => Pi.eval _ i
  | _, .pull f e => e.evaluate d ⋙ d.pull f.left
  | _, .push f _ e => e.evaluate d ⋙ d.push f.left
  | _, .shriek j hj _ e =>
    letI := hj
    e.evaluate d ⋙ d.shriek j.left
  | _, .compactSupport f c e => e.evaluate d ⋙ d.compactSupport f.left c
  | _, .tensor e f => (e.evaluate d).prod' (f.evaluate d) ⋙ d.tensor _

/-- All intermediate schemes are finite type over k and every inverse-image arrow is
separated and finite type. Proper and quasi-compact open constructors already impose
the corresponding arrow properties. These conditions are imposed throughout the tree.
Source: blueprint fix-prop-coherence, geometric domain
(blueprint: def-sf-integral-system-expression-domain). -/
def Expression.geometric {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {W : Over B} (e : Expression B I X W) : Prop :=
  LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom ∧
    match e with
    | .var _ => True
    | .pull f e => IsSeparated f.left ∧ LocallyOfFiniteType f.left ∧
        QuasiCompact f.left ∧ e.geometric
    | .push _ _ e => e.geometric
    | .shriek _ _ _ e => e.geometric
    | .compactSupport f _ e => IsSeparated f.left ∧ LocallyOfFiniteType f.left ∧
        QuasiCompact f.left ∧ e.geometric
    | .tensor e f => e.geometric ∧ f.geometric

/-- Apply the actual reduction functor separately to every integral input.
Source: Stacks 0941 (blueprint: def-sf-integral-system-expression-domain). -/
def inputReduction {B : Scheme.{u}} {I : Type u} (X : I → Over B) :
    (∀ i, Integral l E (X i).left) ⥤ ∀ i, System l E (X i).left :=
  Functor.pi (fun i ↦ (calculus l E (X i).left).reduction)

/-- Every intermediate system in the expression tree belongs to the stated domain.
Source: blueprint fix-prop-coherence, common-bounds proviso
(blueprint: def-sf-integral-system-expression-domain). -/
def Expression.admissible (o : Operations l E) {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : Expression B I X W)
    (M : ∀ i, System l E (X i).left) : Prop :=
  Good l E W.left ((e.evaluate (systemInterpretation l E o)).obj M) ∧
    match e with
    | .var _ => True
    | .pull _ e => e.admissible o M
    | .push _ _ e => e.admissible o M
    | .shriek _ _ _ e => e.admissible o M
    | .compactSupport _ c e => e.admissible o M ∧
        Good l E c.Z ((Operations.shriek l E o c.i).obj
          ((e.evaluate (systemInterpretation l E o)).obj M))
    | .tensor e f => e.admissible o M ∧ f.admissible o M

/-- Extract the root bound from the recursive intermediate-object domain. The case
split only exposes the defining conjunction; no additional boundedness is assumed.
Source: blueprint fix-prop-coherence, common-bounds proviso
(blueprint: def-sf-integral-system-expression-domain). -/
abbrev Expression.admissibleGood (o : Operations l E) {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : Expression B I X W)
    (M : ∀ i, System l E (X i).left) (h : e.admissible l E o M) :
    Good l E W.left ((e.evaluate (systemInterpretation l E o)).obj M) :=
  match e, h with
  | .var _, h => h.1
  | .pull _ _, h => h.1
  | .push _ _ _, h => h.1
  | .shriek _ _ _ _, h => h.1
  | .compactSupport _ _ _, h => h.1
  | .tensor _ _, h => h.1

/-- The full domain of integral input families for a particular expression. All input
and intermediate system bounds, and every retained origin witness, are present.
Source: blueprint fix-prop-coherence, realization domain
(blueprint: def-sf-integral-system-expression-domain). -/
def Expression.domain (o : Operations l E) {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : Expression B I X W) :
    ObjectProperty (∀ i, Integral l E (X i).left) := fun K ↦
  (∀ i, sfIntegralConstructible l E (X i).left (K i) ∧
    Good l E (X i).left ((calculus l E (X i).left).reduction.obj (K i))) ∧
    e.admissible l E o ((inputReduction l E X).obj K)

/-- The actual total limit of a system expression on reduced integral inputs.
Source: Stacks 0941; blueprint fix-prop-coherence
(blueprint: def-sf-integral-system-expression-domain). -/
def Expression.realizationSource (o : Operations l E) {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : Expression B I X W) :=
  (e.domain l E o).ι ⋙ inputReduction l E X ⋙
    e.evaluate (systemInterpretation l E o) ⋙ coefficientSequenceLimit l E W.left

/-- The integral interpretation on exactly the same full input domain.
Source: blueprint fix-prop-coherence
(blueprint: def-sf-integral-system-expression-domain). -/
def Expression.realizationTarget (o : Operations l E) {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : Expression B I X W) :=
  (e.domain l E o).ι ⋙ e.evaluate (integralInterpretation l E)

end IntegralSystemRealization
end WeilConjectures
