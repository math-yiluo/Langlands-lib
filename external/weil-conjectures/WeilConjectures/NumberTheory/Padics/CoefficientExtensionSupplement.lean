/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import WeilConjectures.NumberTheory.Padics.CoefficientExtension

/-!
# Finite p-adic coefficient extensions

Source: Weil conjectures blueprint, `def-weil-finite-field-fiber`, order 411;
slopmaster2, Definition `def:weil-finite-coefficient-datum`
(blueprint: def-weil-l-adic-coefficient-extension).

The absolute value is the spectral absolute value. The ring of integers, its maximal
ideal, and one uniformizer are selected from `Padic.extension_integers_dvr`.
The claims about these data are the separately cited dependency theorems.
-/

@[expose] public section

universe u

namespace Padic

/-- The finite residue field `k_E = 𝒪_E / 𝔪_E`.

Source: blueprint `def-weil-finite-field-fiber`, order 411, and slopmaster2 Definition
`def:weil-finite-coefficient-datum` (blueprint: def-weil-l-adic-coefficient-extension). -/
@[reducible]
noncomputable def coefficientExtensionResidueField (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Type u :=
  coefficientExtensionIntegers l E ⧸ coefficientExtensionMaximalIdeal l E

end Padic
