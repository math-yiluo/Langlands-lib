/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison

/-! # The fixed-scalar pro-etale finite-Tor constructible category

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1464 (blueprint: definition-constructible-sheaves).

The pro-etale predicate is transported through the recorded canonical coefficient
realization. It uses precisely the intrinsic constant-ring predicate, without replacing
constructibility by etale origin. The published etale predicate and the integral and
field stages are imported unchanged.
A separate module preserves the import closure of existing etale-only consumers.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The fixed-coefficient module-sheaf presentation of the recorded pro-etale
`Dᵇ_ctf(Y,A_{E,n})`. Applying the exact canonical realization termwise identifies
this with the original full subcategory of modules over the constant ring sheaf.
Source: blueprint order 1464 (blueprint: definition-constructible-sheaves). -/
noncomputable def finiteTorConstructibleProEtaleModule
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))) :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  fun K ↦ finiteTorConstructible l E n hn Y
    ((ProEtale.finiteCoefficientIntrinsicRealization Y
      (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj K)

end WeilConjectures
