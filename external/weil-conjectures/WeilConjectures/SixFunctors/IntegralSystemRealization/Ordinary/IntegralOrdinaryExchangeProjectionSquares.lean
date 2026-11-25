/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExpressionReduction
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryExchangeSquare
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryProjectionSquare

/-! # Ordinary coefficient squares for exchange and projection

Source: blueprint fix-prop-coherence, the coefficient comparisons of individual maps.
-/

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

/-- Ordinary coefficient compatibility for the two geometric adjunction mates.
Source: blueprint fix-prop-coherence, exchange and projection as normalized mates;
Stacks Tags 07A7 and 0E48.
(blueprint: lem-sf-integral-ordinary-exchange-projection-squares).

Proof: exchange is the mate of the specified pullback square. Paste the four
pullback/reduction comparison squares; composition normalization identifies their
boundary with ringedSquare and the system square. Transpose through the two
geometric adjunctions, whose reduction unit and counit diagrams commute. For
projection, expand rightAdjointProjectionMap into its unit, tensor comparison and
counit. Reduction preserves the ordinary tensor and its pullback comparison;
pasting these diagrams gives the displayed projection square. Naturality inserts
the coefficients of e and t. Both equalities hold without cartesianness or
invertibility of exchange or projection, on ordinary objects before completion. -/
theorem ordinaryExchangeProjectionSquares
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left) :
    (∀ {U V W Z : Over B}
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
        (Expression.push r hr (.pull k e)).ordinaryReduction l E o a K) ∧
    (∀ {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : Expression B I X U) (t : Expression B I X V),
      (Expression.tensor (.push f hf e) t).ordinaryReduction l E o a K ≫
        ((properProjection l E o f.left).app
          (e.systemObj l E o ((inputReduction l E X).obj K))).app
            (t.systemObj l E o ((inputReduction l E X).obj K)) =
      (calculus l E V.left).reduction.map
          (((ringedProperProjection l E a.ringedModels f.left).app
            (e.ringedObj l E a.ringedModels K)).app (t.ringedObj l E a.ringedModels K)) ≫
        (Expression.push f hf (.tensor e (.pull f t))).ordinaryReduction l E o a K) := by
  constructor
  · exact ordinaryExchangeSquare l E o a K
  · exact ordinaryProjectionSquare l E o a K

end WeilConjectures.IntegralSystemRealization
