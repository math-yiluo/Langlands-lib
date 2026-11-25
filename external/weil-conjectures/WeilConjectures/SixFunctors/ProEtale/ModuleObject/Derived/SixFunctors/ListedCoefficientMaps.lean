/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index

/-! # The listed coefficient maps

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/_section.md,
coefficient list (1)--(4) (blueprint: def-sfb-listed-coefficient-maps).

The generators retain their actual ring-object maps. Finite maps are characterized
by postcomposition on sections, so no flatness or surjectivity is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The specified continuous map O_E to a finite discrete ring, as postcomposition
on all profinite sections. The valuation topology is the existing restricted topology.
Source: blueprint coefficient list (3)
(blueprint: def-sfb-listed-coefficient-maps). -/
def IsIntegralFiniteScalarMap (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (A : Type u) [CommRing A]
    (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
      ⟨cartesianFinitePointRing A⟩) : Prop :=
  letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
  ∃ φ : PadicAlgCl.integers ell E.1 →+* A,
    @Continuous _ _ inferInstance ⊥ φ ∧
    ∀ (P : Profinite.{u}) (s : ULift.{u + 1} C(P, PadicAlgCl.integers ell E.1))
      (x : P), ((a.hom.hom.hom.app (op P)) s).down x = φ (s.down x)

end AlgebraicGeometry.ProEtale.CondensedRing
