/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages

/-!
# Six-functor operation datum

Source: blueprint master, sec-smooth-purity/sk-def-sf-operations,
def-fix-six-functor-datum (blueprint: def-fix-six-functor-datum), order 1491.

The datum is construction data, including the comparisons, rather than a choice
from an unnormalized existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w v' w' hA hB hA' hB'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.SuppliedExchangeProjection
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures
open TensorProduct
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All coefficient levels with the finite, completed, localized and common-stage
normalizations. Source: all five clauses of def-fix-six-functor-datum
(blueprint: def-fix-six-functor-datum). -/
structure SixFunctorOperationDatum
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    extends SixFunctorFiniteOperations D C E n hn where
  higher : SixFunctorHigherOperations D C E
  integralNormalization : SixFunctorIntegralNormalization D C E higher
  closure : SixFunctorCommonStages D C
  coefficientIntegralNormalization : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    SixFunctorIntegralNormalization D C (Coefficient.{u} C.l C.Qbar E₀)
      (closure.coefficientStages E₀)
  commonStageCoherence : SixFunctorCommonStageCoherence closure
  /- Scalar identity and cocycle equations are theorems of the coefficient
     comparison modules; the datum records the comparison isomorphisms above. -/

/-- Verdier dual at this coefficient level is the recorded derived internal Hom
into the exceptional image of its coefficient unit, including the morphism action.
Source: clause (5) (blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.finiteVerdier
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  S.finiteDuality.verdier (sixFunctorFiniteHom D C E n hn) X c

/-- Verdier dual at this coefficient level is the recorded derived internal Hom
into the exceptional image of its coefficient unit, including the morphism action.
Source: clause (5) (blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.integralVerdier
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  S.higher.integralDuality.verdier (fun X ↦ constructibleIntegralHom C.l E X.obj.left) X c

/-- Verdier dual at this coefficient level is the recorded derived internal Hom
into the exceptional image of its coefficient unit, including the morphism action.
Source: clause (5) (blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.rationalVerdier
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  S.higher.rationalDuality.verdier (fun X ↦ rationalDerivedInternalHom C.l E X.obj.left) X c

/-- The finite tensor on the finite-Tor category. It is the recorded derived tensor,
not another bifunctor chosen as data.
Source: clause (1) (blueprint: def-fix-six-functor-datum). -/
abbrev SixFunctorOperationDatum.finiteTensor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) := S.finiteTensorDomainStage X

/-- The finite-Tor domain is the recorded predicate, restricted to the bounded
constructible category. Source: the initial domains
(blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.finiteTorDomain
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) : ObjectProperty (sixFunctorFiniteCategory D C E n hn X) :=
  fun K ↦ finiteTorConstructible C.l E n hn X.obj.left K.obj

/-- The integral finite-Tor domain is the recorded uniform finite-reduction condition.
Source: the initial domains (blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.integralFiniteTorDomain
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) : ObjectProperty (sfIntegralConstructibleCategory C.l E X.obj.left) :=
  fun K ↦ finiteTorConstructibleIntegral C.l E X.obj.left K.obj

end WeilConjectures
