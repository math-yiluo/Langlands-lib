/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExpressionReduction
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryCompactificationExchangeSquare

/-! # Ordinary coefficient exchange square

Source: blueprint fix-prop-coherence, the exchange component of the normalized mate
argument for `lem-sf-integral-ordinary-exchange-projection-squares`.

The proof is split from the conjunction theorem so that the exchange mate can be
proved independently by pasting pullback/reduction comparison squares and
transposing through the proper adjunctions. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleCanonicalTensorComparison ringedPullComp ringedSquare Compositors.square
  mateEquiv ringedAdj Direct.adj

/-- Exchange component of the ordinary coefficient mate square.
Source: Stacks Tags 07A7 and 0E48; blueprint fix-prop-coherence.
(blueprint: lem-sf-integral-ordinary-exchange-projection-squares).

Proof: paste the pullback and reduction comparison squares for the four sides of
the given square, use composition normalization to identify the boundary with
`ringedSquare` and the system square, and transpose through the two proper
adjunctions. Naturality of the resulting mate inserts the coefficient map of
the expression. The construction uses no cartesianness or invertibility.
-/
theorem ordinaryExchangeSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left) :
    ∀ {U V W Z : Over B}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      (hr : IsProper r.left) (hp : IsProper p.left)
      (w : k.left ≫ p.left = r.left ≫ i.left) (e : Expression B I X V),
      (Expression.pull i (.push p hp e)).ordinaryReduction l E o a K ≫
        (properExchange l E o a.compositors k.left r.left p.left i.left w).app
          (e.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E W.left).reduction.map
          ((mateEquiv (ringedAdj l E p.left) (ringedAdj l E r.left)
            (TwoSquare.mk _ _ _ _
              (ringedSquare l E k.left r.left p.left i.left w).hom)).app
                (e.ringedObj l E a.ringedModels K)) ≫
        (Expression.push r hr (.pull k e)).ordinaryReduction l E o a K := by
  intro U V W Z k r p i hr hp w e
  exact matePastingNaturalSquare
    (ringedAdj l E p.left) (ringedAdj l E r.left)
    (o.direct p.left).adj (o.direct r.left).adj
    (a.realizationModel.reductionPull p.left) (a.realizationModel.reductionPull r.left)
    (a.realizationModel.reductionPull i.left).hom (a.realizationModel.reductionPull k.left).hom
    (TwoSquare.mk _ _ _ _ (ringedSquare l E k.left r.left p.left i.left w).hom)
    (TwoSquare.mk _ _ _ _ (a.compositors.square l E k.left r.left p.left i.left w).hom)
    (properPullCoeff l E o a k.left r.left p.left i.left w)
    (e.ringedObj l E a.ringedModels K) (e.ordinaryReduction l E o a K)

end WeilConjectures.IntegralSystemRealization
