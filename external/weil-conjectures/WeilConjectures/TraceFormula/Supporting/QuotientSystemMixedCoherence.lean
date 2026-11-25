/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherenceData
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import Mathlib.CategoryTheory.PathCategory.Basic
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import WeilConjectures.TraceFormula.Sequence.SequenceScalarGeneratorInterchange
import WeilConjectures.TraceFormula.Sequence.SequenceDerivedAssociativity
import WeilConjectures.TraceFormula.Sequence.SequenceFiniteBracketingCoherence
import WeilConjectures.TraceFormula.Sequence.SequenceDerivedMixedSquare
import WeilConjectures.TraceFormula.Sequence.SequenceDerivedScalarUnit
import WeilConjectures.TraceFormula.Sequence.SequenceDerivedScalarTower

/-! # Mixed geometric and scalar coherence on strict quotient systems

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe t u a v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  integralComparisonSequenceScalarModel
attribute [local instance 5000] coefficientSequenceEssentiallySmall
attribute [local instance 6000] HasDerivedCategory.standard
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  finiteSystemSequenceSmall finiteSystemSiteSmall
attribute [local irreducible] HasDerivedCategory.standard

attribute [local irreducible] integralComparisonSequenceComposition integralComparisonSequenceUnit
  integralComparisonSequenceScalarPullback integralComparisonSequenceScalarComposition
  integralComparisonSequenceScalarUnit integralComparisonSystemComposition
  integralComparisonSystemUnit integralComparisonSystemScalarPullback

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The geometric/scalar square, as transformations of whole diagrams.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseOrdinaryMixed (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  {V W Z : Scheme.{t}}
  [∀ x : V, Invertible (l : V.residueField x)]
  [∀ x : W, Invertible (l : W.residueField x)]
  [∀ x : Z, Invertible (l : Z.residueField x)]
  (h : Z ⟶ W) (k : W ⟶ V),
  Functor.whiskerRight (integralComparisonSequenceComposition l E h k).hom
    ((integralComparisonSequenceScalarModel l E L ι Z).E) ≫
      Functor.whiskerLeft (integralComparisonSequencePullback l E k)
        (integralComparisonSequenceScalarPullback l E L ι h).hom ≫
      Functor.whiskerRight (integralComparisonSequenceScalarPullback l E L ι k).hom
        (integralComparisonSequencePullback l L h) =
    (integralComparisonSequenceScalarPullback l E L ι (h ≫ k)).hom ≫
      Functor.whiskerLeft ((integralComparisonSequenceScalarModel l E L ι V).E)
        (integralComparisonSequenceComposition l L h k).hom

/-- Multiplication is compatible with the scalar/pullback comparison.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseOrdinaryScalarUnit (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
  (integralComparisonSequenceScalarPullback l E E (AlgHom.id ℚ_[l] E) f).hom ≫
      Functor.whiskerRight (integralComparisonSequenceScalarUnit l E Y).hom
        (integralComparisonSequencePullback l E f) =
    Functor.whiskerLeft (integralComparisonSequencePullback l E f)
      (integralComparisonSequenceScalarUnit l E X).hom

/-- The associator multiplies successive coefficient factors, including equal fields.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseOrdinaryScalarTower (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{t}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
  Functor.whiskerRight (integralComparisonSequenceScalarPullback l E L ι f).hom
    ((integralComparisonSequenceScalarModel l L M j X).E) ≫
      Functor.whiskerLeft ((integralComparisonSequenceScalarModel l E L ι Y).E)
        (integralComparisonSequenceScalarPullback l L M j f).hom ≫
      Functor.whiskerRight (integralComparisonSequenceScalarComposition l E L ι M j Y).hom
        (integralComparisonSequencePullback l M f) =
    Functor.whiskerLeft (integralComparisonSequencePullback l E f)
        (integralComparisonSequenceScalarComposition l E L ι M j X).hom ≫
      (integralComparisonSequenceScalarPullback l E M (j.comp ι) f).hom

/-- Three-arrow associativity, with the canonical identification of equal composites.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseOrdinaryAssociative (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {T V W Z : Scheme.{t}}
  [∀ x : T, Invertible (l : T.residueField x)]
  [∀ x : V, Invertible (l : V.residueField x)]
  [∀ x : W, Invertible (l : W.residueField x)]
  [∀ x : Z, Invertible (l : Z.residueField x)]
  (f : Z ⟶ W) (g : W ⟶ V) (h : V ⟶ T),
  (integralComparisonSequenceComposition l E (f ≫ g) h).hom ≫
      Functor.whiskerLeft (integralComparisonSequencePullback l E h)
        (integralComparisonSequenceComposition l E f g).hom =
    eqToHom (congrArg (fun k ↦ integralComparisonSequencePullback l E k) (Category.assoc f g h)) ≫
      (integralComparisonSequenceComposition l E f (g ≫ h)).hom ≫
      Functor.whiskerRight (integralComparisonSequenceComposition l E g h).hom
        (integralComparisonSequencePullback l E f)

/-- Both geometric unit laws, with their scheme-morphism equality identifications.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseOrdinaryUnital (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
  ((integralComparisonSequenceComposition l E (𝟙 X) f).hom ≫
      Functor.whiskerLeft (integralComparisonSequencePullback l E f)
        (integralComparisonSequenceUnit l E X).hom =
    eqToHom (congrArg (fun k ↦ integralComparisonSequencePullback l E k) (Category.id_comp f))) ∧
  ((integralComparisonSequenceComposition l E f (𝟙 Y)).hom ≫
      Functor.whiskerRight (integralComparisonSequenceUnit l E Y).hom
        (integralComparisonSequencePullback l E f) =
    eqToHom (congrArg (fun k ↦ integralComparisonSequencePullback l E k) (Category.comp_id f)))

/-- All parenthesizations of every finite string give the same comparison.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseOrdinaryFinite (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (p : Quiver.Path X Y) (_hp : IntegralQuotientPathInvertible l p)
  (a b : IntegralQuotientBracketing p),
  ∃ h : integralQuotientBracketFunctor (fun W ↦ coefficientSequenceModules.{t, u} l E W)
      (integralComparisonSequencePullback.{t, u} l E) a =
    integralQuotientBracketFunctor (fun W ↦ coefficientSequenceModules.{t, u} l E W)
      (integralComparisonSequencePullback.{t, u} l E) b,
  integralQuotientBracketComparison (fun W ↦ coefficientSequenceModules.{t, u} l E W)
      (integralComparisonSequencePullback.{t, u} l E)
      (integralComparisonSequenceComposition.{t, u} l E)
      (integralComparisonSequenceUnit.{t, u} l E) a ≪≫ eqToIso h =
    integralQuotientBracketComparison (fun W ↦ coefficientSequenceModules.{t, u} l E W)
      (integralComparisonSequencePullback.{t, u} l E)
      (integralComparisonSequenceComposition.{t, u} l E)
      (integralComparisonSequenceUnit.{t, u} l E) b

/-- The geometric/scalar square, as transformations of whole diagrams.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseDerivedMixed (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  {V W Z : Scheme.{t}}
  [∀ x : V, Invertible (l : V.residueField x)]
  [∀ x : W, Invertible (l : W.residueField x)]
  [∀ x : Z, Invertible (l : Z.residueField x)]
  (h : Z ⟶ W) (k : W ⟶ V),
  Functor.whiskerRight (integralComparisonSystemComposition l E h k).hom
    (integralComparisonDerivedSequenceScalar l E L ι Z) ≫
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E k)
        (integralComparisonSystemScalarPullback l E L ι h).hom ≫
      Functor.whiskerRight (integralComparisonSystemScalarPullback l E L ι k).hom
        (integralComparisonDerivedSequencePullback l L h) =
    (integralComparisonSystemScalarPullback l E L ι (h ≫ k)).hom ≫
      Functor.whiskerLeft (integralComparisonDerivedSequenceScalar l E L ι V)
        (integralComparisonSystemComposition l L h k).hom

/-- Multiplication is compatible with the scalar/pullback comparison.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseDerivedScalarUnit (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
  (integralComparisonSystemScalarPullback l E E (AlgHom.id ℚ_[l] E) f).hom ≫
      Functor.whiskerRight (integralComparisonSystemScalarUnit l E Y).hom
        (integralComparisonDerivedSequencePullback l E f) =
    Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
      (integralComparisonSystemScalarUnit l E X).hom

/-- The associator multiplies successive coefficient factors, including equal fields.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseDerivedScalarTower (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{t}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
  Functor.whiskerRight (integralComparisonSystemScalarPullback l E L ι f).hom
    (integralComparisonDerivedSequenceScalar l L M j X) ≫
      Functor.whiskerLeft (integralComparisonDerivedSequenceScalar l E L ι Y)
        (integralComparisonSystemScalarPullback l L M j f).hom ≫
      Functor.whiskerRight (integralComparisonSystemScalarComposition l E L M ι j Y).hom
        (integralComparisonDerivedSequencePullback l M f) =
    Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
        (integralComparisonSystemScalarComposition l E L M ι j X).hom ≫
      (integralComparisonSystemScalarPullback l E M (j.comp ι) f).hom

/-- Three-arrow associativity, with the canonical identification of equal composites.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseDerivedAssociative (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {T V W Z : Scheme.{t}}
  [∀ x : T, Invertible (l : T.residueField x)]
  [∀ x : V, Invertible (l : V.residueField x)]
  [∀ x : W, Invertible (l : W.residueField x)]
  [∀ x : Z, Invertible (l : Z.residueField x)]
  (f : Z ⟶ W) (g : W ⟶ V) (h : V ⟶ T),
  (integralComparisonSystemComposition l E (f ≫ g) h).hom ≫
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E h)
        (integralComparisonSystemComposition l E f g).hom =
    eqToHom (congrArg (fun k ↦ integralComparisonDerivedSequencePullback l E k) (Category.assoc f
      g h)) ≫
      (integralComparisonSystemComposition l E f (g ≫ h)).hom ≫
      Functor.whiskerRight (integralComparisonSystemComposition l E g h).hom
        (integralComparisonDerivedSequencePullback l E f)

/-- Both geometric unit laws, with their scheme-morphism equality identifications.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseDerivedUnital (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y),
  ((integralComparisonSystemComposition l E (𝟙 X) f).hom ≫
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
        (integralComparisonSystemUnit l E X).hom =
    eqToHom (congrArg (fun k ↦ integralComparisonDerivedSequencePullback l E k) (Category.id_comp
      f))) ∧
  ((integralComparisonSystemComposition l E f (𝟙 Y)).hom ≫
      Functor.whiskerRight (integralComparisonSystemUnit l E Y).hom
        (integralComparisonDerivedSequencePullback l E f) =
    eqToHom (congrArg (fun k ↦ integralComparisonDerivedSequencePullback l E k) (Category.comp_id
      f)))

/-- All parenthesizations of every finite string give the same comparison.
Source: Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralQuotientClauseDerivedFinite (l : ℕ) [Fact l.Prime] : Prop :=
  ∀
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (p : Quiver.Path X Y) (_hp : IntegralQuotientPathInvertible l p)
  (a b : IntegralQuotientBracketing p),
  ∃ h : integralQuotientBracketFunctor (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
      (integralComparisonDerivedSequencePullback.{t, u} l E) a =
    integralQuotientBracketFunctor (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
      (integralComparisonDerivedSequencePullback.{t, u} l E) b,
  integralQuotientBracketComparison (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
      (integralComparisonDerivedSequencePullback.{t, u} l E)
        (integralComparisonSystemComposition.{t, u} l E) (integralComparisonSystemUnit.{t, u} l E)
        a ≪≫ eqToIso h =
    integralQuotientBracketComparison (fun W ↦ coefficientSequenceDerived.{t, u} l E W)
      (integralComparisonDerivedSequencePullback.{t, u} l E)
        (integralComparisonSystemComposition.{t, u} l E) (integralComparisonSystemUnit.{t, u} l E)
        b

/-- Clause-by-clause packaging with shared clause types.
Source: Stacks 0D6D (blueprint: lem-trf-quotient-system-mixed-coherence). -/
structure IntegralQuotientMixedCoherence (l : ℕ) [Fact l.Prime] : Prop where
  /-- The geometric/scalar square, as transformations of whole diagrams. -/
  ordinary_mixed : integralQuotientClauseOrdinaryMixed.{t, u} l
  /-- Multiplication is compatible with the scalar/pullback comparison. -/
  ordinary_scalar_unit : integralQuotientClauseOrdinaryScalarUnit.{t, u} l
  /-- The associator multiplies successive coefficient factors, including equal fields. -/
  ordinary_scalar_tower : integralQuotientClauseOrdinaryScalarTower.{t, u} l
  /-- Three-arrow associativity, with the canonical identification of equal composites. -/
  ordinary_associative : integralQuotientClauseOrdinaryAssociative.{t, u} l
  /-- Both geometric unit laws, with their scheme-morphism equality identifications. -/
  ordinary_unital : integralQuotientClauseOrdinaryUnital.{t, u} l
  /-- All parenthesizations of every finite string give the same comparison. -/
  ordinary_finite : integralQuotientClauseOrdinaryFinite.{t, u} l
  /-- The geometric/scalar square, as transformations of whole diagrams. -/
  derived_mixed : integralQuotientClauseDerivedMixed.{t, u} l
  /-- Multiplication is compatible with the scalar/pullback comparison. -/
  derived_scalar_unit : integralQuotientClauseDerivedScalarUnit.{t, u} l
  /-- The associator multiplies successive coefficient factors, including equal fields. -/
  derived_scalar_tower : integralQuotientClauseDerivedScalarTower.{t, u} l
  /-- Three-arrow associativity, with the canonical identification of equal composites. -/
  derived_associative : integralQuotientClauseDerivedAssociative.{t, u} l
  /-- Both geometric unit laws, with their scheme-morphism equality identifications. -/
  derived_unital : integralQuotientClauseDerivedUnital.{t, u} l
  /-- All parenthesizations of every finite string give the same comparison. -/
  derived_finite : integralQuotientClauseDerivedFinite.{t, u} l

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] sequenceDirectComp sequenceDirectId

private theorem sequenceComp_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V) :
    integralComparisonSequenceComposition l E h k =
      (Adjunction.leftAdjointCompIso
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k))
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h))
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k)))
        (sequenceDirectComp l E h k)).symm := by
  unfold integralComparisonSequenceComposition
  obtain ⟨d, he, hd⟩ :=
    (integralComparisonSequenceComposition_existsUnique l E h k).exists.choose_spec
  have hde : d = sequenceDirectComp l E h k := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (hd M U.unop.1 U.unop.2 x).trans
      (sequenceDirectComp_apply l E h k M U x).symm
  apply (conjugateIsoEquiv
    ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k)).comp
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)))
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k)))).injective
  rw [he, hde]
  apply Iso.ext
  exact (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _).symm

private abbrev sequenceAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sequenceDirectTransport (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{t}} {f g : X ⟶ Y} (e : f = g)
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : Y.ProEt)
    (m : ((integralComparisonSequenceDirectImage l E f).obj N).val.obj (op (n, U))) :
    ((eqToIso (congrArg (integralComparisonSequenceDirectImage l E) e)).hom.app N).val.app
        (op (n, U)) m =
      N.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
        (eqToHom (congrArg (fun t ↦ (Scheme.proEtaleBaseChange t).obj U) e.symm))).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sequenceDirectMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{t}} (f : X ⟶ Y)
    {N N' : coefficientSequenceModules l E X} (a : N ⟶ N') (n : ℕ) (U : Y.ProEt)
    (m : ((integralComparisonSequenceDirectImage l E f).obj N).val.obj (op (n, U))) :
    (((integralComparisonSequenceDirectImage l E f).map a).val.app (op (n, U))) m =
      a.val.app (op (n, (Scheme.proEtaleBaseChange f).obj U)) m := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sequenceDirectRestriction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{t}} (f : X ⟶ Y)
    (N : coefficientSequenceModules l E X) (n : ℕ) {U V : Y.ProEt} (a : U ⟶ V)
    (m : ((integralComparisonSequenceDirectImage l E f).obj N).val.obj (op (n, V))) :
    (((integralComparisonSequenceDirectImage l E f).obj N).val.map
      (CategoryTheory.Prod.mkHom (𝟙 n) a).op) m =
      N.val.map (CategoryTheory.Prod.mkHom (𝟙 n) ((Scheme.proEtaleBaseChange f).map a)).op m := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sequenceDirectCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y Z W : Scheme.{t}}
    (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X) :
    Functor.isoWhiskerLeft (integralComparisonSequenceDirectImage l E j)
        (sequenceDirectComp l E h k) ≪≫ sequenceDirectComp l E j (h ≫ k) =
      (Functor.associator (integralComparisonSequenceDirectImage l E j)
        (integralComparisonSequenceDirectImage l E h)
        (integralComparisonSequenceDirectImage l E k)).symm ≪≫
        Functor.isoWhiskerRight (sequenceDirectComp l E j h)
          (integralComparisonSequenceDirectImage l E k) ≪≫ sequenceDirectComp l E (j ≫ h) k ≪≫
        eqToIso (congrArg (integralComparisonSequenceDirectImage l E) (Category.assoc j h k)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨⟨n, U⟩⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  erw [sequenceDirectMap l E k ((sequenceDirectComp l E j h).hom.app N) n U]
  erw [sequenceDirectComp_apply l E j h N (op (n, (Scheme.proEtaleBaseChange k).obj U))]
  erw [sequenceDirectComp_apply l E (j ≫ h) k N (op (n, U))]
  conv_rhs => erw [sequenceDirectTransport l E (Category.assoc j h k) N n U]
  conv_lhs => erw [sequenceDirectComp_apply l E h k
    ((integralComparisonSequenceDirectImage l E j).obj N) (op (n, U)) m]
  conv_lhs => erw [sequenceDirectComp_apply l E j (h ≫ k) N (op (n, U))]
  conv_lhs => erw [sequenceDirectRestriction l E j N n
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U)]
  apply restriction_pasting N.val
  apply CategoryTheory.Prod.hom_ext
  · simp
  · exact site_pasting (P := @WeaklyEtale) (Q := ⊤) j h k U

private theorem sequenceOrdinaryCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Z W : Scheme.{t}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (M : coefficientSequenceModules l E X) :
    (integralComparisonSequenceComposition l E j (h ≫ k)).hom.app M ≫
        (integralComparisonSequencePullback l E j).map
          ((integralComparisonSequenceComposition l E h k).hom.app M) =
      (eqToIso (congrArg (integralComparisonSequencePullback l E)
        (Category.assoc j h k).symm)).hom.app M ≫
        (integralComparisonSequenceComposition l E (j ≫ h) k).hom.app M ≫
        (integralComparisonSequenceComposition l E j h).hom.app
          ((integralComparisonSequencePullback l E k).obj M) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (sequenceAdjunction l E k) (sequenceAdjunction l E h)
    (sequenceAdjunction l E j)
    (sequenceAdjunction l E (h ≫ k)) (sequenceAdjunction l E (j ≫ h))
    (sequenceAdjunction l E (j ≫ h ≫ k))
    (sequenceDirectComp l E h k) (sequenceDirectComp l E j h)
    ((sequenceDirectComp l E (j ≫ h) k) ≪≫
      eqToIso (congrArg (integralComparisonSequenceDirectImage l E) (Category.assoc j h k)))
    (sequenceDirectComp l E j (h ≫ k)) (sequenceDirectCoherence l E j h k)
  have ht := mate_transport (fun f ↦ (integralComparisonSequenceDirectImage l E f).leftAdjoint)
    (integralComparisonSequenceDirectImage l E) (fun f ↦ sequenceAdjunction l E f)
    (sequenceAdjunction l E k) (sequenceAdjunction l E (j ≫ h))
    (Category.assoc j h k)
    (sequenceDirectComp l E (j ≫ h) k)
  rw [ht] at hh
  have hi := NatTrans.congr_app (congrArg Iso.inv hh) M
  dsimp only [sequenceAdjunction] at hi
  dsimp only [integralComparisonSequencePullback]
  simp only [sequenceComp_eq,
    Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.comp_id, Category.assoc, eqToIso.inv,
    Functor.comp_obj, eqToHom_app] at hi ⊢
  exact hi.symm

private theorem sequenceOrdinaryAssocForward
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T X Y Z : Scheme.{t}} (f : Z ⟶ Y) (g : Y ⟶ X) (h : X ⟶ T) :
    (integralComparisonSequenceComposition l E (f ≫ g) h).hom ≫
      Functor.whiskerLeft (integralComparisonSequencePullback l E h)
        (integralComparisonSequenceComposition l E f g).hom =
      eqToHom (congrArg (integralComparisonSequencePullback l E) (Category.assoc f g h)) ≫
        (integralComparisonSequenceComposition l E f (g ≫ h)).hom ≫
        Functor.whiskerRight (integralComparisonSequenceComposition l E g h).hom
          (integralComparisonSequencePullback l E f) := by
  apply NatTrans.ext
  funext P
  let e := eqToIso (congrArg (integralComparisonSequencePullback l E)
    (Category.assoc f g h))
  have he : (integralComparisonSequenceComposition l E f (g ≫ h)).hom.app P ≫
      (integralComparisonSequencePullback l E f).map
        ((integralComparisonSequenceComposition l E g h).hom.app P) =
      e.inv.app P ≫ (integralComparisonSequenceComposition l E (f ≫ g) h).hom.app P ≫
        (integralComparisonSequenceComposition l E f g).hom.app
          ((integralComparisonSequencePullback l E h).obj P) :=
    sequenceOrdinaryCoherence l E f g h P
  have hh := congrArg (fun a ↦ e.hom.app P ≫ a) he
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at hh
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    e, eqToIso.hom, Category.assoc] using hh.symm

private theorem site_congr
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange] {X Y : C} {f g : X ⟶ Y} (e : f = g) :
    MorphismProperty.Over.pullbackCongr (P := P) (Q := Q) e =
      eqToIso (congrArg (fun f : X ⟶ Y ↦ MorphismProperty.Over.pullback P Q f) e) := by
  cases e
  exact MorphismProperty.Over.pullbackCongr_refl f rfl

private theorem sequenceUnit_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t}) :
    integralComparisonSequenceUnit l E X =
      Adjunction.leftAdjointIdIso (sequenceAdjunction l E (𝟙 X))
        (sequenceDirectId l E X).symm := by
  unfold integralComparisonSequenceUnit
  apply (integralComparisonSequenceUnit_existsUnique l E X).unique
    (integralComparisonSequenceUnit_existsUnique l E X).exists.choose_spec
  intro M n U x
  have hh := unit_conjugateEquiv_symm Adjunction.id
    (sequenceAdjunction l E (𝟙 X)) (sequenceDirectId l E X).hom M
  have hu := congrArg (fun q ↦ q.val.app (op (n, U)) x) hh.symm
  exact hu.trans (sequenceDirectId_apply l E X M U n x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sequenceDirectLeftUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) :
    Functor.isoWhiskerRight (sequenceDirectId l E X)
        (integralComparisonSequenceDirectImage l E f) ≪≫
      sequenceDirectComp l E (𝟙 X) f ≪≫
      eqToIso (congrArg (integralComparisonSequenceDirectImage l E) (Category.id_comp f)) =
      Functor.leftUnitor (integralComparisonSequenceDirectImage l E f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨⟨n, U⟩⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [sequenceDirectMap l E f ((sequenceDirectId l E X).hom.app N) n U]
  erw [sequenceDirectId_apply l E X N ((Scheme.proEtaleBaseChange f).obj U) n]
  erw [sequenceDirectComp_apply l E (𝟙 X) f N (op (n, U))]
  erw [sequenceDirectTransport l E (Category.id_comp f) N n U]
  erw [← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp]
  change _ = m
  have hb := congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_id_left (P := @WeaklyEtale) (Q := ⊤)
      f (𝟙 X ≫ f) rfl)) U
  have hc :
      eqToHom (congrArg (fun g ↦ (Scheme.proEtaleBaseChange g).obj U)
          (Category.id_comp f).symm) ≫
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          (𝟙 X) f).hom.app U ≫
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app
          ((Scheme.proEtaleBaseChange f).obj U) = 𝟙 _ := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app] at hb
    rw [hb]
    simp only [Iso.symm_hom, Functor.rightUnitor_inv_app, Category.id_comp]
    rw [site_congr]
    simp only [Functor.id_obj, eqToIso.hom, NatTrans.id_app, Category.id_comp,
      Iso.inv_hom_id_app, eqToHom_refl]
  have hd := congrArg (fun a ↦ (Prod.sectR n X.ProEt).map a) hc
  simp only [Functor.map_comp] at hd
  change Prod.mkHom (𝟙 n) _ ≫ Prod.mkHom (𝟙 n) _ ≫ Prod.mkHom (𝟙 n) _ = 𝟙 _ at hd
  erw [Category.assoc, hd, op_id, PresheafOfModules.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sequenceDirectRightUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) :
    Functor.isoWhiskerLeft (integralComparisonSequenceDirectImage l E f)
        (sequenceDirectId l E Y) ≪≫
      sequenceDirectComp l E f (𝟙 Y) ≪≫
      eqToIso (congrArg (integralComparisonSequenceDirectImage l E) (Category.comp_id f)) =
      Functor.rightUnitor (integralComparisonSequenceDirectImage l E f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨⟨n, U⟩⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [sequenceDirectId_apply l E Y
    ((integralComparisonSequenceDirectImage l E f).obj N) U n]
  erw [sequenceDirectComp_apply l E f (𝟙 Y) N (op (n, U))]
  erw [sequenceDirectTransport l E (Category.comp_id f) N n U]
  erw [sequenceDirectRestriction l E f N n
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U)]
  erw [← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp]
  change _ = m
  have hb := congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_id_right (P := @WeaklyEtale) (Q := ⊤)
      f (f ≫ 𝟙 Y) rfl)) U
  have hc :
      eqToHom (congrArg (fun g ↦ (Scheme.proEtaleBaseChange g).obj U)
          (Category.comp_id f).symm) ≫
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          f (𝟙 Y)).hom.app U ≫
        (Scheme.proEtaleBaseChange f).map
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U) = 𝟙 _ := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app] at hb
    rw [hb]
    simp only [Iso.symm_hom, Functor.leftUnitor_inv_app, Category.id_comp]
    rw [site_congr]
    simp only [Functor.id_obj, eqToIso.hom, NatTrans.id_app, Category.id_comp,
      ← Functor.map_comp, Iso.inv_hom_id_app, eqToHom_refl]
    exact CategoryTheory.Functor.map_id _ _
  have hd := congrArg (fun a ↦ (Prod.sectR n X.ProEt).map a) hc
  simp only [Functor.map_comp] at hd
  change Prod.mkHom (𝟙 n) _ ≫ Prod.mkHom (𝟙 n) _ ≫ Prod.mkHom (𝟙 n) _ = 𝟙 _ at hd
  erw [Category.assoc, hd, op_id, PresheafOfModules.map_id]
  rfl

attribute [local irreducible] Adjunction.leftAdjointCompIso Adjunction.leftAdjointIdIso
  Adjunction.ofIsRightAdjoint
private theorem sequenceOrdinaryLeftUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequenceComposition l E (𝟙 X) f).hom ≫
      Functor.whiskerLeft (integralComparisonSequencePullback l E f)
        (integralComparisonSequenceUnit l E X).hom =
      eqToHom (congrArg (integralComparisonSequencePullback l E) (Category.id_comp f)) := by
  have hd := sequenceDirectLeftUnit l E f
  have hc : sequenceDirectComp l E (𝟙 X) f ≪≫
      eqToIso (congrArg (integralComparisonSequenceDirectImage l E) (Category.id_comp f)) =
      Functor.isoWhiskerRight (sequenceDirectId l E X).symm
        (integralComparisonSequenceDirectImage l E f) ≪≫
      Functor.leftUnitor (integralComparisonSequenceDirectImage l E f) := by
    simpa only [← Functor.isoWhiskerRight_symm, ← Functor.isoWhiskerLeft_symm,
      Iso.trans_assoc, Iso.symm_self_id_assoc] using
      congrArg (fun a ↦ Functor.isoWhiskerRight (sequenceDirectId l E X).symm
        (integralComparisonSequenceDirectImage l E f) ≪≫ a) hd
  have hm := Adjunction.leftAdjointCompIso_comp_id (sequenceAdjunction l E f)
    (sequenceAdjunction l E (𝟙 X)) _ (sequenceDirectId l E X).symm hc
  rw [mate_transport (fun f ↦ (integralComparisonSequenceDirectImage l E f).leftAdjoint)
    (integralComparisonSequenceDirectImage l E) (fun g ↦ sequenceAdjunction l E g)
    (sequenceAdjunction l E f) (sequenceAdjunction l E (𝟙 X))
    (Category.id_comp f) (sequenceDirectComp l E (𝟙 X) f)] at hm
  have ho := congrArg
    (fun a ↦ (Adjunction.leftAdjointCompIso (sequenceAdjunction l E f)
      (sequenceAdjunction l E (𝟙 X)) (sequenceAdjunction l E (𝟙 X ≫ f))
      (sequenceDirectComp l E (𝟙 X) f)).symm ≪≫ a) hm
  apply NatTrans.ext
  funext P
  have hp := congr_app (congrArg Iso.hom ho) P
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.comp_id, Category.assoc,
    Iso.inv_hom_id_app_assoc, sequenceComp_eq, sequenceUnit_eq, sequenceAdjunction,
    integralComparisonSequencePullback, eqToIso.hom] using hp.symm

private theorem sequenceOrdinaryRightUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequenceComposition l E f (𝟙 Y)).hom ≫
      Functor.whiskerRight (integralComparisonSequenceUnit l E Y).hom
        (integralComparisonSequencePullback l E f) =
      eqToHom (congrArg (integralComparisonSequencePullback l E) (Category.comp_id f)) := by
  have hd := sequenceDirectRightUnit l E f
  have hc : sequenceDirectComp l E f (𝟙 Y) ≪≫
      eqToIso (congrArg (integralComparisonSequenceDirectImage l E) (Category.comp_id f)) =
      Functor.isoWhiskerLeft (integralComparisonSequenceDirectImage l E f)
        (sequenceDirectId l E Y).symm ≪≫
      Functor.rightUnitor (integralComparisonSequenceDirectImage l E f) := by
    simpa only [← Functor.isoWhiskerRight_symm, ← Functor.isoWhiskerLeft_symm,
      Iso.trans_assoc, Iso.symm_self_id_assoc] using
      congrArg (fun a ↦ Functor.isoWhiskerLeft (integralComparisonSequenceDirectImage l E f)
        (sequenceDirectId l E Y).symm ≪≫ a) hd
  have hm := Adjunction.leftAdjointCompIso_id_comp (sequenceAdjunction l E (𝟙 Y))
    (sequenceAdjunction l E f) _ (sequenceDirectId l E Y).symm hc
  rw [mate_transport (fun f ↦ (integralComparisonSequenceDirectImage l E f).leftAdjoint)
    (integralComparisonSequenceDirectImage l E) (fun g ↦ sequenceAdjunction l E g)
    (sequenceAdjunction l E (𝟙 Y)) (sequenceAdjunction l E f)
    (Category.comp_id f) (sequenceDirectComp l E f (𝟙 Y))] at hm
  have ho := congrArg
    (fun a ↦ (Adjunction.leftAdjointCompIso (sequenceAdjunction l E (𝟙 Y))
      (sequenceAdjunction l E f) (sequenceAdjunction l E (f ≫ 𝟙 Y))
      (sequenceDirectComp l E f (𝟙 Y))).symm ≪≫ a) hm
  apply NatTrans.ext
  funext P
  have hp := congr_app (congrArg Iso.hom ho) P
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.comp_id, Category.assoc,
    Iso.inv_hom_id_app_assoc, sequenceComp_eq, sequenceUnit_eq, sequenceAdjunction,
    integralComparisonSequencePullback, eqToIso.hom] using hp.symm

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem sequenceExactLeftUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ D) (H : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : H ≅ F ⋙ G) (e : G ≅ 𝟭 D) (d : H ≅ F)
    (h : c ≪≫ Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F = d) :
    (Functor.mapDerivedCategoryNatIso c).hom ≫
      (Functor.mapDerivedCategoryCompIso F G).inv ≫
      Functor.whiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D).hom =
      (Functor.mapDerivedCategoryNatIso d).hom := by
  have ho := congrArg (fun a ↦ (Functor.mapDerivedCategoryNatIso a).hom) h
  have hn := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e
  simp only [Functor.mapDerivedCategoryNatIso_trans] at ho
  simp only [Iso.trans_hom, Functor.whiskerLeft_comp]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F G).inv, ← hn, Category.assoc,
    Functor.mapDerivedCategoryCompIso_comp_id]
  have hu : Functor.rightUnitor F = Iso.refl F := rfl
  simp only [hu] at ho
  erw [Functor.mapDerivedCategoryNatIso_refl] at ho
  exact ho

private theorem sequenceExactRightUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : C ⥤ C) (H : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : H ≅ G ⋙ F) (e : G ≅ 𝟭 C) (d : H ≅ F)
    (h : c ≪≫ Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F = d) :
    (Functor.mapDerivedCategoryNatIso c).hom ≫
      (Functor.mapDerivedCategoryCompIso G F).inv ≫
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom
        F.mapDerivedCategory = (Functor.mapDerivedCategoryNatIso d).hom := by
  have ho := congrArg (fun a ↦ (Functor.mapDerivedCategoryNatIso a).hom) h
  have hn := Functor.mapDerivedCategoryNatIso_isoWhiskerRight e F
  simp only [Functor.mapDerivedCategoryNatIso_trans] at ho
  simp only [Iso.trans_hom, Functor.whiskerRight_comp]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso G F).inv, ← hn, Category.assoc,
    Functor.mapDerivedCategoryCompIso_id_comp]
  have hu : Functor.leftUnitor F = Iso.refl F := rfl
  simp only [hu] at ho
  erw [Functor.mapDerivedCategoryNatIso_refl] at ho
  exact ho

private theorem sequenceDerivedTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} {f g : X ⟶ Y} (e : f = g) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (integralComparisonSequencePullback l E) e))).hom =
      (eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem sequenceDerivedLeftUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSystemComposition l E (𝟙 X) f).hom ≫
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
        (integralComparisonSystemUnit l E X).hom =
      eqToHom (congrArg (integralComparisonDerivedSequencePullback l E) (Category.id_comp f)) := by
  have ho : integralComparisonSequenceComposition l E (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (integralComparisonSequencePullback l E f)
        (integralComparisonSequenceUnit l E X) ≪≫
      Functor.rightUnitor (integralComparisonSequencePullback l E f) =
      eqToIso (congrArg (integralComparisonSequencePullback l E) (Category.id_comp f)) := by
    apply Iso.ext
    apply NatTrans.ext
    funext P
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    exact (Category.comp_id _).trans (congr_app (sequenceOrdinaryLeftUnit l E f) P)
  have hd := sequenceExactLeftUnit (integralComparisonSequencePullback l E f)
    (integralComparisonSequencePullback l E (𝟙 X))
    (integralComparisonSequencePullback l E (𝟙 X ≫ f)) _ _ _ ho
  rw [sequenceDerivedTransport l E (Category.id_comp f)] at hd
  dsimp only [integralComparisonSystemComposition, integralComparisonSystemUnit,
    integralComparisonDerivedSequencePullback, Iso.trans_hom]
  simp only [integralComparisonSystemComposition, integralComparisonSystemUnit,
    integralComparisonSequenceUnit, integralComparisonDerivedSequencePullback,
    Iso.trans_hom, Category.assoc] at hd ⊢
  exact hd

private theorem sequenceDerivedRightUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSystemComposition l E f (𝟙 Y)).hom ≫
      Functor.whiskerRight (integralComparisonSystemUnit l E Y).hom
        (integralComparisonDerivedSequencePullback l E f) =
      eqToHom (congrArg (integralComparisonDerivedSequencePullback l E) (Category.comp_id f)) := by
  have ho : integralComparisonSequenceComposition l E f (𝟙 Y) ≪≫
      Functor.isoWhiskerRight (integralComparisonSequenceUnit l E Y)
        (integralComparisonSequencePullback l E f) ≪≫
      Functor.leftUnitor (integralComparisonSequencePullback l E f) =
      eqToIso (congrArg (integralComparisonSequencePullback l E) (Category.comp_id f)) := by
    apply Iso.ext
    apply NatTrans.ext
    funext P
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
    exact (congrArg (fun a ↦ (integralComparisonSequenceComposition l E f (𝟙 Y)).hom.app P ≫ a)
      (Category.comp_id _)).trans (congr_app (sequenceOrdinaryRightUnit l E f) P)
  have hd := sequenceExactRightUnit (integralComparisonSequencePullback l E f)
    (integralComparisonSequencePullback l E (𝟙 Y))
    (integralComparisonSequencePullback l E (f ≫ 𝟙 Y)) _ _ _ ho
  rw [sequenceDerivedTransport l E (Category.comp_id f)] at hd
  dsimp only [integralComparisonSystemComposition, integralComparisonSystemUnit,
    integralComparisonDerivedSequencePullback, Iso.trans_hom]
  simp only [integralComparisonSystemComposition, integralComparisonSystemUnit,
    integralComparisonSequenceUnit, integralComparisonDerivedSequencePullback,
    Iso.trans_hom, Category.assoc] at hd ⊢
  exact hd

private theorem sequencePrimeStalkUnit (l : ℕ) (X : Scheme.{t})
    [∀ x : X, Invertible (l : X.residueField x)] (x : X) :
    IsUnit (l : X.presheaf.stalk x) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change (X.residue x).hom (l : X.presheaf.stalk x) ≠ 0
  simpa only [map_natCast] using (isUnit_of_invertible (l : X.residueField x)).ne_zero

/-- Mixed geometric/scalar coherence of the canonical operations on strict quotient systems.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6D, and the node's eight proof steps
(blueprint: lem-trf-quotient-system-mixed-coherence).

Proof: (1) Work on the ringed sequence site, not in towers in a derived category.
The adjunction determines inverse-image maps on unit sections; the tensor adjunction
then determines scalar-linear maps on unit tensors. (2) The two three-arrow compositors
send a unit to the same successive units. Identity units insert the identity map.
Induction on a binary assembly proves finite-string coherence, including the empty
and singleton paths. Transport along an equality of scheme arrows uses that same mate.
(3) In the mixed square both routes send 1 tensor gamma_hk(x) to
 gamma_h gamma_k(1 tensor x). (4) For the scalar unit both routes send
1 tensor gamma_f(x) to gamma_f(x), and scalar linearity handles general coefficients.
(5) In a coefficient tower both routes send c tensor (b tensor gamma_f(x)) to
 gamma_f(c*j(b) tensor x). This includes identity and equal coefficient extensions.
(6) Unit naturality and tensor functoriality commute with every vertical restriction
and horizontal quotient transition; quotient ring homomorphisms preserve products.
The resulting equalities are equalities of module-system transformations, so applying
mapHomologicalComplex gives equal cochain maps in all degrees, commuting with the
differential and without signs. (7) Choose one flat-term K-flat resolution of the
entire system, using lem-pc-kflat-resolution. Ringed-topos pullback preserves K-flat
complexes with flat terms (lem-weil-pbc-ringed-topos-kflat-pullback), as does scalar
extension, including for nonflat coefficient maps. Iterate this for the finite diagram.
The universal cochain counits of lem-pur-derived-change-of-rings identify the specified
derived maps with the localized ordinary maps on this simultaneous model.
(8) Localization preserves the equalities. Naturality and cancellation of the
resolution isomorphism prove them on every input. No normalization, boundedness,
finite Tor-amplitude or flatness of a quotient coefficient map was used. -/
theorem integralQuotientMixedCoherence (l : ℕ) [Fact l.Prime] :
    IntegralQuotientMixedCoherence.{t, u} l := by
  refine {
    ordinary_mixed := ?_
    ordinary_scalar_unit := ?_
    ordinary_scalar_tower := ?_
    ordinary_associative := ?_
    ordinary_unital := ?_
    ordinary_finite := ?_
    derived_mixed := ?_
    derived_scalar_unit := ?_
    derived_scalar_tower := ?_
    derived_associative := ?_
    derived_unital := ?_
    derived_finite := ?_ }
  · intro E L _ _ _ _ _ _ ι V W Z _ _ _ h k
    have h := sequenceScalarGeometric_interchange l E L ι h k
      (sequencePrimeStalkUnit l V) (sequencePrimeStalkUnit l W) (sequencePrimeStalkUnit l Z)
    apply NatTrans.ext
    funext P
    simpa [sequenceScalarGeometricLeft, sequenceScalarGeometricRight] using congr_app h P
  · intro E _ _ _ X Y _ _ f
    have h := sequenceScalarUnit_interchange l E f
      (sequencePrimeStalkUnit l X) (sequencePrimeStalkUnit l Y)
    apply NatTrans.ext
    funext P
    simpa [sequenceScalarUnitLeft, sequenceScalarUnitRight] using congr_app h P
  · intro E L _ _ _ _ _ _ ι M _ _ _ j X Y _ _ f
    have h := sequenceScalarTower_interchange l E L ι M j f
      (sequencePrimeStalkUnit l X) (sequencePrimeStalkUnit l Y)
    apply NatTrans.ext
    funext P
    simpa [sequenceScalarTowerLeft, sequenceScalarTowerRight] using congr_app h P
  · intro E _ _ _ T V W Z _ _ _ _ f g h
    exact sequenceOrdinaryAssocForward l E f g h
  · intro E _ _ _ X Y _ _ f
    exact ⟨sequenceOrdinaryLeftUnit l E f, sequenceOrdinaryRightUnit l E f⟩
  · intro E _ _ _ X Y p hp a b
    exact sequenceFiniteCoherence _ (integralComparisonSequencePullback l E)
      (integralComparisonSequenceComposition l E) (integralComparisonSequenceUnit l E)
      (sequenceOrdinaryAssocForward l E)
      (sequenceOrdinaryLeftUnit l E) (sequenceOrdinaryRightUnit l E) a b
  · exact sequenceDerivedMixed l
  · exact sequenceDerivedScalarUnit l
  · exact sequenceDerivedScalarTower l
  · intro E _ _ _ T V W Z _ _ _ _ f g h
    apply NatTrans.ext
    funext P
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc] using (sequenceDerivedCoherence l E f g h P).symm
  · intro E _ _ _ X Y _ _ f
    exact ⟨sequenceDerivedLeftUnit l E f, sequenceDerivedRightUnit l E f⟩
  · intro E _ _ _ X Y p hp a b
    exact sequenceFiniteCoherence _ (integralComparisonDerivedSequencePullback l E)
      (integralComparisonSystemComposition l E) (integralComparisonSystemUnit l E)
      (fun f g h ↦ by
        apply NatTrans.ext
        funext P
        simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Category.assoc] using (sequenceDerivedCoherence l E f g h P).symm)
      (sequenceDerivedLeftUnit l E) (sequenceDerivedRightUnit l E) a b

end WeilConjectures
