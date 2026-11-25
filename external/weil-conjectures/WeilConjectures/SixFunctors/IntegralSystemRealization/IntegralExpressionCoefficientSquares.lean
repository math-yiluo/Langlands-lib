/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralRealizationAssemblyData
import all WeilConjectures.SixFunctors.GeneratorReduction.ShortWordIntegralDomain
import all WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveCompletionEffectivity
import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralCanonicalRealizationSquare
import WeilConjectures.SixFunctors.IntegralSystemRealization.Support.IntegralSupportCounitProjection

/-! # Intermediate assembly data for integral realization
Source: blueprint fix-prop-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem transpose_square {C D : Type*} [Category C] [Category D]
    {R : C ⥤ D} {L : D ⥤ C} (adj : R ⊣ L)
    {M N : D} {K H : C} (c : L.obj M ≅ K) (d : L.obj N ≅ H)
    (s : M ⟶ N) (r : K ⟶ H)
    (h : L.map s ≫ d.hom = c.hom ≫ r) :
    R.map c.inv ≫ adj.counit.app M ≫ s =
      R.map r ≫ R.map d.inv ≫ adj.counit.app N := by
  have ht : c.inv ≫ L.map s = r ≫ d.inv := by
    apply (cancel_mono d.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using congrArg (fun f ↦ c.inv ≫ f) h
  have hs := (adj.homEquiv_naturality_right_square_iff r d.inv c.inv s).2 ht.symm
  simpa only [Adjunction.homEquiv_counit, Category.assoc] using hs.symm

private theorem expression_integral_domain (D : FiniteFieldDatum.{u})
    (o : Operations l E) (comparison : ExpressionRecursion.Comparisons l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    finiteTorConstructibleIntegral l E W.left
      ((e.evaluate (integralInterpretation l E)).obj K.obj) := by
  have h := e.admissibleGood l E o _ K.property.2
  obtain ⟨lo, hi, torLo, torHi, hlo, htor, hlevel⟩ := h.2.1
  exact GeneratorReduction.domain_of_realization l E W.left _ lo hi torLo torHi
    ⟨h.1, h.2.2, hlo, htor, hlevel⟩ _ ((comparison e g).app K).symm

private theorem expression_completion_isIso (D : FiniteFieldDatum.{u})
    (o : Operations l E) (a : AmbientModels l E o)
    (comparison : ExpressionRecursion.Comparisons l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    IsIso (e.completionMap l E a.ringedModels K.obj) := by
  induction e with
  | var i =>
    dsimp only [Expression.completionMap]
    infer_instance
  | pull f e ih =>
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2⟩
    have := ih g.2.2.2.2.2 Ke
    have hd := expression_integral_domain l E D o comparison e g.2.2.2.2.2 Ke
    have hc := GeneratorReduction.finiteTorOrdinaryPullComplete l E f.left
      g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 _ (Or.inl hd)
    have := GeneratorReduction.completion_unit_isIso l E _ _ hc
    dsimp only [Expression.completionMap, OpenFactorCoherence.Pull.unit,
      NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  | push f hp e ih =>
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2⟩
    have := ih g.2.2 Ke
    dsimp only [Expression.completionMap]
    infer_instance
  | shriek j hj hq e ih =>
    let := hj
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2⟩
    have := ih g.2.2 Ke
    dsimp only [Expression.completionMap]
    infer_instance
  | compactSupport f c e ih =>
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2.1⟩
    have := ih g.2.2.2.2.2 Ke
    dsimp only [Expression.completionMap]
    infer_instance
  | @tensor W e t ihe iht =>
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2.1⟩
    let Kt : (t.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2.2⟩
    have := ihe g.2.2.1 Ke
    have := iht g.2.2.2 Kt
    have he := expression_integral_domain l E D o comparison e g.2.2.1 Ke
    have ht := expression_integral_domain l E D o comparison t g.2.2.2 Kt
    have hc := GeneratorReduction.finiteTorOrdinaryTensorComplete l E W.left _ _ he ht
    have hc' : IntegralOnSlice.IsComplete l E W.left none
        ((a.ringedModels.tensor W.left).ordinary.tensor.obj
          ((e.evaluate (integralInterpretation l E)).obj K.obj,
            (t.evaluate (integralInterpretation l E)).obj K.obj)) := by
      rw [a.ringedModels.tensorClosed W.left]
      exact hc
    have := GeneratorReduction.completion_unit_isIso l E W.left _ hc'
    have : IsIso (Prod.mkHom (e.completionMap l E a.ringedModels K.obj)
        (t.completionMap l E a.ringedModels K.obj)) :=
      (Iso.prod (asIso (e.completionMap l E a.ringedModels K.obj))
        (asIso (t.completionMap l E a.ringedModels K.obj))).isIso_hom
    dsimp only [Expression.completionMap, OpenFactorCoherence.Tensor.chi,
      NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance

/-- Coefficient squares of the recursively fixed comparisons and their finite support
projections. All equalities are asserted in derived strict systems before evaluation.
Source: blueprint fix-prop-coherence, generator/context and compactification steps;
Stacks 0941, 07A7 and 0F7B--0F7F
(blueprint: lem-sf-integral-expression-coefficient-squares).

Proof: the actual primitive coefficient transpose formulas identify each recursively
induced coefficient map with R of inverse comparison followed by the actual counit.
For each basic generator use generator-reduction coherence on its finite word;
use tensor/pullback normalization and ringed mate calculus for the explicit exchange,
projection and compactification composites. The proper/open map is pinned by its
lambda adjunct; bridge uniqueness identifies it with the intrinsic semilinear map.
Invertible completion maps allow the independently fixed ordinary ringed arrows
to be transported to completed arrows. Induct on the canonical-pair derivation:
identities and composition follow by functoriality, unary contexts by naturality
of the primitive reduction map, and tensor contexts by bifunctoriality. This is an
equality in the system category; no faithfulness of finite evaluation is used.
For the support assertion, first compare the open/proper composite on a single
complete input with the direct comparison of basic realization. Its finite projection
is the prescribed scalar-adjunction mate. Substitute the inner comparison by
naturality, apply its normalization, and use the defining finite-image and quotient
projection equations. The result retains every actual quotient transition and
applies also to nested support. Induction on expression vertices proves completion
invertibility on exactly their good intermediate domains. -/
theorem integralExpressionCoefficientSquares (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (a : AmbientModels l E o)
    (comparison : ExpressionRecursion.Comparisons l E D o)
    (laws : RecursionLaws l E D o a comparison)
    (reduction : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e : Expression _ I X W) (_geometric : e.geometric),
    (e.domain l E o).ι ⋙ inputReduction l E X ⋙
      e.evaluate (systemInterpretation l E o) ≅
    e.realizationTarget l E o ⋙ (calculus l E W.left).reduction)
    (normalization : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory),
    (calculus l E W.left).reduction.map ((comparison e g).hom.app K) ≫
      (reduction e g).inv.app K =
    (calculus l E W.left).adjunction.counit.app
      ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))) :
    (∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e : Expression _ I X W) (_ge : e.geometric)
    (K : (e.domain l E o).FullSubcategory),
    IsIso (e.completionMap l E a.ringedModels K.obj)) ∧
    (∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e t : Expression _ I X W) (ge : e.geometric) (gt : t.geometric)
    (K : (e.domain l E o).FullSubcategory) (ht : t.domain l E o K.obj)
    (s : e.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K.obj))
    (r : (e.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (t.evaluate (integralInterpretation l E)).obj K.obj),
    CanonicalPair l E o a.compositors a.openComparisons a.canonicalBridge a.properOpen
      a.ringedModels a.ringedOpenComparisons a.ringedProperOpen
      ((inputReduction l E X).obj K.obj) K.obj e t s r →
    (calculus l E W.left).reduction.map ((comparison e ge).inv.app K) ≫
      (calculus l E W.left).adjunction.counit.app
        (e.systemObj l E o ((inputReduction l E X).obj K.obj)) ≫ s =
    (calculus l E W.left).reduction.map r ≫
      (calculus l E W.left).reduction.map ((comparison t gt).inv.app ⟨K.obj, ht⟩) ≫
      (calculus l E W.left).adjunction.counit.app
        (t.systemObj l E o ((inputReduction l E X).obj K.obj))) ∧
    (∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (c : Compactification f.left) (e : Expression _ I X U)
    (g : (Expression.compactSupport f c e).geometric)
    (K : ((Expression.compactSupport f c e).domain l E o).FullSubcategory) (n : ℕ),
    (scalarReductionDerivedExtension l E V.left n).map
      ((comparison (.compactSupport f c e) g).hom.app K) ≫
        (PurCompactSupport.finiteReductionIso l E V.left n).inv.app
          ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj
            ((e.evaluate (integralInterpretation l E)).obj K.obj)) ≫
        (PurCompactSupport.comparison (PurCompactSupport.reduction l E (n + 1)
          (Nat.le_add_left 1 n)) c).app
            ((e.evaluate (integralInterpretation l E)).obj K.obj) ≫
        (PurCompactSupport.finiteImageIso l E n c).hom.app
          ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
            (Nat.le_add_left 1 n) U.left)).obj
              ((e.evaluate (integralInterpretation l E)).obj K.obj)) ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((PurCompactSupport.finiteReductionIso l E U.left n).hom.app
            ((e.evaluate (integralInterpretation l E)).obj K.obj)) =
    ((calculus l E V.left).reductionEvaluation n).inv.app
      ((coefficientSequenceLimit l E V.left).obj
        (((Expression.compactSupport f c e).evaluate (systemInterpretation l E o)).obj
          ((inputReduction l E X).obj K.obj))) ≫
      (coefficientSequenceDerivedEvaluation l E V.left n).map
        ((calculus l E V.left).adjunction.counit.app
          (((Expression.compactSupport f c e).evaluate (systemInterpretation l E o)).obj
            ((inputReduction l E X).obj K.obj))) ≫
      (supportEvaluation l E o c n).hom.app
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
        ((coefficientSequenceDerivedEvaluation l E U.left n).map
          ((reduction e g.2.2.2.2.2).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.1⟩) ≫
        ((calculus l E U.left).reductionEvaluation n).hom.app
          ((e.evaluate (integralInterpretation l E)).obj K.obj))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro I _ X W e ge K
    exact expression_completion_isIso l E D o a comparison e ge K
  · intro I _ X W e t ge gt K ht s r h
    exact transpose_square (calculus l E W.left).adjunction
      ((comparison e ge).app K) ((comparison t gt).app ⟨K.obj, ht⟩) s r
      (integralCanonicalRealizationSquare l E D hl o a comparison laws e t ge gt K ht s r h)
  · intro I _ X U V f c e g K n
    let Ke : (e.domain l E o).FullSubcategory :=
      ⟨K.obj, K.property.1, by simpa [Expression.admissible] using K.property.2.2.1⟩
    rw [laws.supportRecursion f c e g.2.2.2.2.2 g K]
    exact integralSupportCounitProjection l E D hl o a f c
      (ExpressionRecursion.geometricRoot e g.2.2.2.2.2)
      (ExpressionRecursion.geometricRoot (.compactSupport f c e) g)
      ⟨g.2.2.1, g.2.2.2.1, g.2.2.2.2.1⟩
      (compactOpenQuasiCompact c g.2.2.2.2.1)
      (e.systemObj l E o ((inputReduction l E X).obj K.obj))
      (e.admissibleGood l E o _ Ke.property.2)
      (by simpa [Expression.admissible] using K.property.2.2.2)
      ((Expression.compactSupport f c e).admissibleGood l E o _ K.property.2)
      ((e.evaluate (integralInterpretation l E)).obj K.obj)
      ((comparison e g.2.2.2.2.2).app Ke) ((reduction e g.2.2.2.2.2).app Ke)
      (normalization e g.2.2.2.2.2 Ke) n

end WeilConjectures.IntegralSystemRealization
