/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.InvertibleExponent
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Finite closed-support constructibility coordinates

The finite-ring derived comparison identifies the intrinsic bounded constructibility
predicate with bounded constructible complexes in fixed-scalar coordinates. This proof
uses no compact-support coefficient comparison or normalized coefficient system.
Source: Stacks, Tag 09AL, and the finite-domain step of the current blueprint proof
of `lemma-change-coefficients-exceptional-inverse-image--1` (blueprint:
lem-coef-finite-closed-realization-domain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
