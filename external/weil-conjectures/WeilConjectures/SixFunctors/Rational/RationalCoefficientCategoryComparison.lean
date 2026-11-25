/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparisonSystem
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import WeilConjectures.FourierTransform.FdIntegralIdentityRationalEquivalence
import WeilConjectures.FourierTransform.FdCompletionInverseScalarCoherence
import WeilConjectures.FourierTransform.FdCommonStageComparisonDescent
import WeilConjectures.FourierTransform.FdCoefficientComparisonSystem
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
import WeilConjectures.FourierTransform.FrobeniusFixedPairComparison

/-! # Canonical coefficient comparison and Frobenius pairs

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence
(blueprint: lem-fd-rational-coefficient-category-comparison).

The data use the recorded raw categories and operations. No completion of their
object sets and no arbitrary replacement comparison is introduced.

## Main definitions and statement

* `FdComparisonSchemeCoherence`: canonical identity, composition and scalar equations.
* `FdFrobeniusComparison`: finite and common-stage Weil-pair equivalences.
* `rationalCoefficientCategoryComparison`: existence of the coherent comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Avoid generating unused auxiliary lemmas for these large comparison structures.
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

open AlgebraicallyClosedCoefficients (Coefficient)

variable (l : ℕ) [Fact l.Prime]

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Specialization to geometric Frobenius, including finite-stage and algebraically
closed fixed-pair categories and their actual intertwining morphisms.
Source: trace-definition final sentence, proof steps 10--11
(blueprint: lem-fd-rational-coefficient-category-comparison). -/
structure FdFrobeniusComparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (S : FdCoefficientComparisonSystem.{u} l Ω)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] where
  [noetherian : IsNoetherian (D.geometricFiber X₀).left]
  [dimension : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n)]
  [invertible : Fact (∀ x : (D.geometricFiber X₀).left,
    IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x))]
  common : sfCommonStageWeilComplex D l hl X₀ Ω ≌
    CategoryTheory.Endofunctor.IsoAlgebra
      (pbcQbarCompletedPull l Ω (D.geometricFrobenius X₀).asIso.hom)
  common_functor : HEq common.functor
    (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
      (S.pullback (D.geometricFrobenius X₀).asIso).pair)
  finite : ∀ E : Padic.FiniteCoefficientFields l Ω,
    sfWeilComplex D l hl X₀ (pbcFiniteField.{u} l Ω E) ≌
      CategoryTheory.Endofunctor.IsoAlgebra
        ((pbcQbarPullFamily l Ω (D.geometricFrobenius X₀).asIso.hom).Φ E)
  finite_functors : ∀ E, HEq (finite E).functor
    (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
      ((S.pullback (D.geometricFrobenius X₀).asIso).finite E).rational)

end WeilConjectures
