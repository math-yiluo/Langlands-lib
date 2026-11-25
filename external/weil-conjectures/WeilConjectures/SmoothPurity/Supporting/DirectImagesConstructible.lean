/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import all WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
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
import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportConstructibility
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Direct images preserve bounded constructibility

Source: Weil blueprint, `def-weil-ordinary-compact-cohomology` (blueprint:
lem-weil-structure-direct-images-constructible).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The coefficient prime is a unit in the finite-field fibre.
Source: blueprint `def-weil-ordinary-compact-cohomology`, finite-field hypotheses
(blueprint: lem-weil-structure-direct-images-constructible).
Proof: the cardinality of the base field gives characteristic D.p, and its algebraic
closure has the same characteristic. If the image of l vanished, D.p would divide l.
Since both are prime, this would force l = D.p, contrary to hl. Thus l is nonzero
in the field D.k, and hence is a unit. -/
theorem finiteFieldDatumPrimeUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hc : Fintype.card D.k₀ = D.q := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base
  have _ : Fact D.p.Prime := ⟨D.prime⟩
  have _ : CharP D.k₀ D.p :=
    charP_of_card_eq_prime_pow (hc.trans D.cardinality_eq)
  have _ : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hne : (l : D.k) ≠ 0 := by
    intro h
    have hdvd : D.p ∣ l := by
      exact (CharP.cast_eq_zero_iff D.k D.p l).mp h
    obtain h | h := (Nat.dvd_prime (Fact.out : l.Prime)).mp hdvd
    · exact D.prime.ne_one h
    · exact hl h.symm
  exact isUnit_iff_ne_zero.mpr hne

end WeilConjectures
