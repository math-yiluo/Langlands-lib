/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
import WeilConjectures.TraceFormula.Supporting.EffectiveQuotientModelDescent
import WeilConjectures.TraceFormula.Supporting.EffectiveCompletionPresentationModels
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-!
# Effective normalized integral realization models

Source: Stacks Project, Tags 099N(2),(5) and 0941; blueprint
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`,
final common-stage transport paragraph
(blueprint: lem-trf-effective-comparison-realization-models).

The assertion retains the actual system adjunction, the representative-normalized
primitive models, and the strict quotient augmentation. Effectivity is stated in
the derived category of the entire quotient diagram.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual completion unit is the strict quotient augmentation, on every
whole-system coherent quotient presentation of every flat-term K-flat representative.
The unshifted projections are quotient-unit sections; every shifted coordinate
is zero. The final equation is an equality of entire derived morphisms.
Source: Stacks 0941; blueprint common-stage transport, completion-unit normalization
(blueprint: lem-trf-effective-comparison-realization-models). -/
def IsEffectiveComparisonCompletionNormalized (X : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l E X) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    IsIntegralComparisonPresentationCoherent l E X S P.obj C e κ →
    ∃ v : P.obj ⟶ integralOperationsRoos
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.obj.X i).val.obj U),
        (((v ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor) ≫ Pi.π (fun m ↦
              ((((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
                C).asFunctor.obj (op m))) n).f i).val.app U) x =
          integralComparisonRestrictedSection l E X (C.X i) n U
            (integralComparisonSequenceSection l E X (C.X i) n U
              (((κ n).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x)))) ∧
      (∀ (i j : ℤ) (h : i + -1 = j), v.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary
          (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor)).v i j h = 0) ∧
      S.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E X).map e.hom ≫
        (integralComparisonRoosBridge l E X ρ C).hom = DerivedCategory.Q.map v

/-- Simultaneous primitive models and effectivity, for all finite coefficient
fields and embeddings (in particular identities and composite embeddings).
All model types are the published representative-normalized interfaces.
Source: Stacks 099N(2),(5), 0941; blueprint common-stage transport
(blueprint: lem-trf-effective-comparison-realization-models). -/
structure EffectiveComparisonRealizationModels (l : ℕ) [Fact l.Prime] where
  /-- The specified whole-system reduction/realization calculus. -/
  system : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)], CoefficientDerivedSystemCalculus l E X
  /-- One normalized natural Roos comparison for each field and site. -/
  roos : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)], IntegralComparisonRoosModel l E X
  /-- Primitive pullback isomorphisms, with every K-flat presentation normalized. -/
  pullback : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y),
    IntegralComparisonPullbackModel l E f (system E Y) (roos E X)
  /-- Primitive scalar isomorphisms for every inclusion, with the same Roos models. -/
  scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)],
    IntegralComparisonScalarModel l E L ι X (system E X) (roos L X)
  /-- The initial map has its quotient coordinate and zero shifted coordinate. -/
  completion_normalization : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)],
    IsEffectiveComparisonCompletionNormalized l E X (system E X) (roos E X)
  /-- Both normalization and effectivity concern the actual whole pullback system. -/
  pullback_effective : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory l E Y),
    IsNormalizedCoefficientSequence l E X
        ((integralComparisonDerivedSequencePullback l E f).obj ((system E Y).reduction.obj K.obj)) ∧
      sfIntegralConstructible l E X ((coefficientSequenceLimit l E X).obj
        ((integralComparisonDerivedSequencePullback l E f).obj
          ((system E Y).reduction.obj K.obj))) ∧
      IsIso ((system E X).adjunction.counit.app
        ((integralComparisonDerivedSequencePullback l E f).obj
          ((system E Y).reduction.obj K.obj)))
  /-- Ramified scalar change needs no flatness or Tor-amplitude hypothesis. -/
  scalar_effective : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfIntegralConstructibleCategory l E X),
    IsNormalizedCoefficientSequence l L X
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj
          ((system E X).reduction.obj K.obj)) ∧
      sfIntegralConstructible l L X ((coefficientSequenceLimit l L X).obj
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj
          ((system E X).reduction.obj K.obj))) ∧
      IsIso ((system L X).adjunction.counit.app
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj
          ((system E X).reduction.obj K.obj)))
  /-- The actual completion unit is invertible on the constructible-complete domain. -/
  complete : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K : sfIntegralConstructibleCategory l E X), IsIso ((system E X).adjunction.unit.app K.obj)

private theorem complete_unrestricted
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E X))
    (hK : IsSfDerivedComplete l E X K) : IsDerivedCompleteUnrestricted l E X K := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E X D hl K).mp hK⟩

/-- Effective normalized models exist simultaneously.
Source: Stacks 099N(2),(5), 0941; blueprint common-stage transport
(blueprint: lem-trf-effective-comparison-realization-models).

Proof: (1) Exact countable products on the pro-etale site and strict Roos comparison
provide one natural cone/total-limit comparison, normalized by the ordinary limit
tuple and zero shifted coordinate on every K-injective tower.
(2) Use the whole-system adjunction of coefficientDerivedSystemEvaluationCalculus.
Its counit is coefficient change of integralComparisonTowerCounit, as computed by
integralComparisonReductionCounit_formula. On a K-injective resolution q the latter
is the ordinary limit cone followed by the inverse of q, simultaneously as a tower map.
(3) Choose flat-term K-flat representatives using lem-pc-kflat-resolution.
Change of rings preserves their K-flatness. Exact finite inverse image sends their
actual quotient diagram to the defining completed-pullback tower. Applying the
single Roos comparison gives pullback with the prescribed generator normalization.
(4) For scalar change use coefficientExtensionReductionModel: successive quotient
tensors reassociate by (x tensor a) tensor b to x tensor ab, retaining every
transition. The resulting cone is integralScalarExtensionOfUniverses. For three
fields both associations multiply all three scalars; identity coefficients multiply
by the unit. No quotient ring-map flatness is used.
(5) The strict quotient augmentation is a chain map since its quotient tuple is
killed by 1-shift. Its shifted coordinate is zero. The actual unit identity is the
completion-unit strict-quotient-model lemma, and holds on every coherent presentation.
(6) Reduction is normalized; exact whole-system inverse image and the scalar
reduction-model comparison preserve normalization. purNormalizedReconstruction
makes the actual counits invertible and their realizations complete. Its unit
clause applies to the given complete K.
(7) integralOperations_preserve_constructible and
sfIntegralScalarExtension_constructible, transported through the primitive
isomorphisms, give constructible realizations with one uniform finite interval.
(8) The pullback and scalar well-definedness theorems descend the comparisons
through every K-flat representative and common refinement. The Roos comparison
is natural on entire tower complexes and computed on every K-injective tower;
the counit is the natural transformation of the whole-system adjunction.
Thus all formulas are resolution-independent and retain all quotient transitions. -/
theorem effectiveComparisonRealizationModels (l : ℕ) [Fact l.Prime] :
    Nonempty (EffectiveComparisonRealizationModels.{u} l) := by
  classical
  have models (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (W : Scheme.{u})
      [∀ x : W, Invertible (l : W.residueField x)] :=
    effectiveCompletionPresentationModels l F W
  choose S ρ hn using models
  have primitives (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (G : Type u) [Field G] [Algebra ℚ_[l] G]
      [FiniteDimensional ℚ_[l] G] (ι : F →ₐ[ℚ_[l]] G) {X Y : Scheme.{u}}
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :=
    effectiveQuotientModelDescent l F G ι f
      (fun x ↦ isUnit_of_invertible (l : X.residueField x))
      (fun y ↦ isUnit_of_invertible (l : Y.residueField y))
      (S F Y) (S F X) (S G Y) (ρ F X) (ρ G Y)
  let pull (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
      {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :=
    (primitives F F (AlgHom.id ℚ_[l] F) f).2.1.some
  let scalar (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (G : Type u) [Field G] [Algebra ℚ_[l] G]
      [FiniteDimensional ℚ_[l] G] (ι : F →ₐ[ℚ_[l]] G) (W : Scheme.{u})
      [∀ x : W, Invertible (l : W.residueField x)] :=
    (primitives F G ι (𝟙 W)).2.2.some
  refine ⟨{
    system := S
    roos := ρ
    pullback := pull
    scalar := scalar
    completion_normalization := hn
    pullback_effective := ?_
    scalar_effective := ?_
    complete := ?_ }⟩
  · intro F _ _ _ X Y _ _ f K
    have h := (primitives F F (AlgHom.id ℚ_[l] F) f).1 K.obj
    have hc := effectiveQuotientModelConstructible l F F (AlgHom.id ℚ_[l] F) f
      (S F Y) (ρ F X) (ρ F Y) (pull F f)
      (scalar F F (AlgHom.id ℚ_[l] F) Y) K.obj K.property
    exact ⟨h.2.1, hc.2.2.1, h.2.2.2.2.2.1⟩
  · intro F _ _ _ G _ _ _ ι W _ K
    have h := (primitives F G ι (𝟙 W)).1 K.obj
    have hc := effectiveQuotientModelConstructible l F G ι (𝟙 W)
      (S F W) (ρ F W) (ρ G W) (pull F (𝟙 W)) (scalar F G ι W) K.obj K.property
    exact ⟨h.2.2.1, hc.2.2.2, h.2.2.2.2.2.2.1⟩
  · intro F _ _ _ W _ K
    have h := (primitives F F (AlgHom.id ℚ_[l] F) (𝟙 W)).1 K.obj
    exact h.2.2.2.2.2.2.2 (complete_unrestricted l F W K.obj K.property.1)

end WeilConjectures
