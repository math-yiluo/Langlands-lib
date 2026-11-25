/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The H-zero map in the representative scalar-normalization calculation.
It is the image under degree-zero homology of the integral sections of the enriched
adjunction map, followed by the chosen scalar-sections comparison: the concrete
composite displayed in the representative transpose theorem.
Source: Stacks 03CZ, 079P and 08JA.
(blueprint: def-coef-derived-sections-scalar-hom-zero-map) -/
noncomputable def coefficientDerivedSectionsScalarHomZeroMap
    (R : CoefficientDerivedSystemReduction l E W)
    (D : CoefficientDerivedSystemScalarCoherence l E W)
    (n : ℕ) (P : DerivedCategory (scalarReductionSource l E W))
    (M : normalizedDVRDerived l E W n) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
        ((coefficientIntegralGlobalHom l E W).obj
          (op P, (coefficientFiniteDerivedRestriction l E W n).obj M)) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
        ((coefficientFiniteGlobalHom l E W n).obj
          (op ((coefficientFiniteDerivedExtension l E W n).obj P), M)) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
    ((coefficientIntegralSections l E W).map
        (coefficientEnrichedAdjunctionMap R.integralClosed (R.finiteClosed n)
          (coefficientFiniteDerivedExtension l E W n)
          (coefficientFiniteAdjunction l E W n) (R.finiteTensor n) P M) ≫
      (D.scalarSections n).hom.app
        ((coefficientFiniteInternalHom l E W n).obj
          (op ((coefficientFiniteDerivedExtension l E W n).obj P), M)))

end WeilConjectures
