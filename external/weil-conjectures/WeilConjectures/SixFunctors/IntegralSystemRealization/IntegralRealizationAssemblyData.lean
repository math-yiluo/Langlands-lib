/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
public import WeilConjectures.SixFunctors.IntegralSystemRealization.ExpressionRecursion.IntegralExpressionRecursion

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

/-- Canonical simultaneous models before expression realization. This records only
ambient operations, their normalized mates and open reconstruction.
Source: Stacks 0941, 07A7, 03DI; blueprint fix-prop-coherence, steps 1--2
(blueprint: def-sf-integral-system-realization-data). -/
structure AmbientModels (o : Operations l E) where
  /-- The proper/open mate, scalar restriction, and normalized pasting package. -/
  compositors : Compositors l E o
  openComparisons : OpenComparisons l E o compositors
  canonicalBridge : CanonicalBridge l E o
  properOpen : ProperOpenCoherence l E o compositors openComparisons canonicalBridge
  /-- The tensor/square identifications obey the displayed equation of
      lem-weil-pbc-ringed-exchange-tensor-coherence, before evaluation. -/
  ringedTensorCoherence : ∀ {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) (M : System l E V) (N : System l E Z),
    (IntegralSystemRealization.pull l E i).map
        (((properProjection l E o p).app M).app N) ≫
      (properExchange l E o compositors k r p i h).app
        ((calculus l E V).systemClosed.tensor.obj
          (M, (IntegralSystemRealization.pull l E p).obj N)) ≫
      (Operations.push l E o r).map
        ((pullbackTensorSystemComparison l E k).hom.app
          (M, (IntegralSystemRealization.pull l E p).obj N) ≫
        (calculus l E U).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((compositors.square l E k r p i h).inv.app N))) =
    (pullbackTensorSystemComparison l E i).hom.app ((Operations.push l E o p).obj M, N) ≫
      (calculus l E W).systemClosed.tensor.map
        (Prod.mkHom ((properExchange l E o compositors k r p i h).app M) (𝟙 _)) ≫
      ((properProjection l E o r).app ((IntegralSystemRealization.pull l E k).obj M)).app
        ((IntegralSystemRealization.pull l E i).obj N)
  realizationModel : RealizationModel l E o
  /-- The open comparison is the actual reduction mate followed by the inverse
      reconstruction unit. Its displayed equation fixes it without finite evaluation. -/
  openRealization : ∀ {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] (_hq : QuasiCompact j) (M : System l E U)
    (_hM : Good l E U M) (_hJ : Good l E V ((Operations.shriek l E o j).obj M)),
    (coefficientSequenceLimit l E V).obj ((Operations.shriek l E o j).obj M) ≅
      ((PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).mapDerivedCategory).obj
        ((coefficientSequenceLimit l E U).obj M)
  openNormalization : ∀ {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] [QuasiCompact j] (M : System l E U)
    (hM : Good l E U M) (hJ : Good l E V ((Operations.shriek l E o j).obj M)),
    (coefficientSequenceLimit l E V).map
      ((Operations.shriek l E o j).map ((calculus l E U).adjunction.counit.app M)) ≫
      (openRealization j inferInstance M hM hJ).hom ≫
      (calculus l E V).adjunction.unit.app
        (((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) j).mapDerivedCategory).obj
          ((coefficientSequenceLimit l E U).obj M)) =
    (coefficientSequenceLimit l E V).map
      ((realizationModel.openReduction l E j).app ((coefficientSequenceLimit l E U).obj M))
  /-- Published completion-unit models fix the localized integral generators. -/
  ringedModels : RingedModels l E
  ringedOpenComparisons : RingedOpenComparisons l E ringedModels
  ringedProperOpen : RingedProperOpen l E ringedModels ringedOpenComparisons

/-- The explicit recursion equations for a given comparison family. These equations
contain neither coefficient normalization nor compatibility with canonical generator maps.
Source: blueprint fix-prop-coherence, expression-tree construction
(blueprint: def-sf-integral-system-realization-data). -/
structure RecursionLaws (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (a : AmbientModels l E o)
    (comparison : ExpressionRecursion.Comparisons l E D o) : Prop where
  /-- Variable comparisons are the inverse of the actual reconstruction unit. -/
  inputNormalization : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))} (i : I)
    (g : (Expression.var (X := X) i).geometric)
    (K : ((Expression.var (X := X) i).domain l E o).FullSubcategory),
    (calculus l E (X i).left).adjunction.unit.app (K.obj i) ≫
      (comparison (.var i) g).hom.app K = 𝟙 (K.obj i)
  /-- The proper-image comparison is the right-adjoint conjugate, recursively
      followed by proper image of the inner comparison. -/
  push : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (hp : IsProper f.left) (e : Expression _ I X U)
    (ge : e.geometric) (g : (Expression.push f hp e).geometric)
    (K : ((Expression.push f hp e).domain l E o).FullSubcategory),
    (comparison (.push f hp e) g).hom.app K =
      (a.realizationModel.push l E f.left).hom.app
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) ≫
      (PurCompactSupport.push (PurCompactSupport.completed l E) f.left).map
        ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
          simpa [Expression.admissible] using K.property.2.2⟩)
  /-- Pullback comparison is fixed by the published K-flat quotient-tower model. -/
  pull : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (e : Expression _ I X V)
    (ge : e.geometric) (g : (Expression.pull f e).geometric)
    (K : ((Expression.pull f e).domain l E o).FullSubcategory),
    (coefficientSequenceLimit l E U.left).map
      ((IntegralSystemRealization.pull l E f.left).map
        ((calculus l E V.left).adjunction.counit.app
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)))) ≫
      (comparison (.pull f e) g).hom.app K =
    (pullbackTensorIntegralPullbackModel l E f.left).inv.app
      ((coefficientSequenceLimit l E V.left).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))) ≫
      (integralDerivedPullback l E f.left).map
        ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
          simpa [Expression.admissible] using K.property.2.2⟩)
  /-- Open comparison uses the specified open-reduction mate and actual unit. -/
  shriek : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (j : U ⟶ V) [hj : IsOpenImmersion j.left] [hq : QuasiCompact j.left]
    (e : Expression _ I X U) (ge : e.geometric)
    (g : (Expression.shriek j hj hq e).geometric)
    (K : ((Expression.shriek j hj hq e).domain l E o).FullSubcategory),
    (comparison (.shriek j hj hq e) g).hom.app K =
      (a.openRealization j.left hq
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
        (e.admissibleGood l E o _ (by
          simpa [Expression.admissible] using K.property.2.2)) K.property.2.1).hom ≫
      ((PurCompactSupport.openExtension
        (PurCompactSupport.completed l E) j.left).mapDerivedCategory).map
        ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
          simpa [Expression.admissible] using K.property.2.2⟩)
  /-- Tensor comparison is fixed by the canonical two-input K-flat total tensor model. -/
  tensor : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e t : Expression _ I X W) (ge : e.geometric) (gt : t.geometric)
    (g : (Expression.tensor e t).geometric)
    (K : ((Expression.tensor e t).domain l E o).FullSubcategory),
    (coefficientSequenceLimit l E W.left).map
      ((calculus l E W.left).systemClosed.tensor.map
        (((calculus l E W.left).adjunction.counit.app
            ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
          ((calculus l E W.left).adjunction.counit.app
            ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))))) ≫
      (comparison (.tensor e t) g).hom.app K =
    (pullbackTensorIntegralTensorModel l E W.left).inv.app
      (((coefficientSequenceLimit l E W.left).obj
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
        ((coefficientSequenceLimit l E W.left).obj
          ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)))) ≫
      (integralCompletedTensor l E W.left).map
        (Prod.mkHom
          ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.1⟩)
          ((comparison t gt).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.2⟩))
  /-- Compact support uses exactly the recursively realized J-then-S composite. -/
  supportRecursion : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (c : Compactification f.left) (e : Expression _ I X U)
    (ge : e.geometric) (g : (Expression.compactSupport f c e).geometric)
    (K : ((Expression.compactSupport f c e).domain l E o).FullSubcategory),
    (comparison (.compactSupport f c e) g).hom.app K =
      (a.realizationModel.push l E c.g).hom.app
        ((Operations.shriek l E o c.i).obj
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))) ≫
      (PurCompactSupport.push (PurCompactSupport.completed l E) c.g).map
        ((a.openRealization c.i (compactOpenQuasiCompact c g.2.2.2.2.1)
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
          (e.admissibleGood l E o _ (by
            simpa [Expression.admissible] using K.property.2.2.1))
          (by simpa [Expression.admissible] using K.property.2.2.2)).hom ≫
        ((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) c.i).mapDerivedCategory).map
          ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.1⟩))

end WeilConjectures.IntegralSystemRealization
