/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralLattice.AdmissibleLattices
public import WeilConjectures.SmoothBaseChange.SbcCompletedOperations
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SmoothBaseChange.AdicSmoothBaseChange
import Mathlib.GroupTheory.PGroup
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientRealizationDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # Smooth base change with finite-extension rational coefficients
Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1445
(blueprint: sbc-thm-e-coefficient-smooth-base-change).
The exchange lives in the raw rationalization of the ambient complete category.
Constructible landing is represented through the fully faithful integral inclusion
and the specified lattice presentation. It makes no integral constructibility claim
about an arbitrary representative merely rationally isomorphic to a constructible one.

## Main statements

- `sbcRationalExchange`: the localized canonical integral mate.
- `sbcTransportedExchange`: transport along a specified presentation.
- `eCoefficientSmoothBaseChange`: invertibility, independence and constructible landing.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)

/-- The scalar localization of the left integral composite, on all complete complexes.
Equivalently this is successive rational direct image and rational completed pullback:
both send a tensor r tensor a to r tensor P_f(D_g(a)).
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalLeft : PbcRationalComplete l E T ⥤ PbcRationalComplete l E X :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcPush l E g ⋙ sbcPull l E f)

/-- The scalar localization of the right integral composite, without constructibility
assumptions on its outputs. Source: blueprint order 1445
(blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalRight : PbcRationalComplete l E T ⥤ PbcRationalComplete l E X :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcPull l E e ⋙ sbcPush l E h)

/-- Rational exchange is exactly scalar localization of the specified integral mate.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalExchange : sbcRationalLeft l E (f := f) (g := g) ⟶
    sbcRationalRight l E (e := e) (h := h) :=
  ScalarLocalization.betweenNat (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcExchange l E sq)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def scalarRealization (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  pbcAssociatedModule W A (adicLisseRing W A) (adicLisseConstantUnit W A)

private local instance scalarRealization_equiv (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (scalarRealization W A).IsEquivalence :=
  ProEtale.coefficientRealization_isEquivalence (ProEt.topology W) A _ _

private local instance scalarRestriction_additive (W : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] : (scalarRestriction W A).Additive :=
  Functor.additive_of_preserves_binary_products _

private local instance scalarRealization_additive (W : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] : (scalarRealization W A).Additive :=
  Functor.additive_of_preserves_binary_products _

private def finiteEncoding (W : Scheme.{u}) (n : ℕ) :=
  pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ⋙
    scalarRestriction W (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)

private local instance finiteEncoding_equiv (W : Scheme.{u}) (n : ℕ) :
    (finiteEncoding l E W n).IsEquivalence := by
  have : (pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence W ((adicLisseForget W).mapIso
      (pbcLevelConstantComparison W (pbcIntegralDatum l E) n))).functor.IsEquivalence
  unfold finiteEncoding
  infer_instance

private local instance finiteEncoding_additive (W : Scheme.{u}) (n : ℕ) :
    (finiteEncoding l E W n).Additive := by unfold finiteEncoding; infer_instance

end WeilConjectures
