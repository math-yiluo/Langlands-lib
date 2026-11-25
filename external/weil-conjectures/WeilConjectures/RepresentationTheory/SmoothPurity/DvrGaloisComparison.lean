/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.RingTheory.Excellent
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RepresentationTheory.SmoothPurity.DiscreteContinuousCohomology
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.Excellent
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.RepresentationTheory.SmoothPurity.KernelInvariantsCohomology

/-!
# Comparison with the tame procyclic quotient

This is the structural comparison used by `DvrGalois`: invariants under the
prime-to-`ell` kernel identify the local Galois cohomology with the cohomology
of the additive `ell`-adic quotient.  The statement is kept separate because
the averaging and injective-resolution argument is itself a lemma of the
local Galois calculation.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Rep

attribute [local irreducible] discreteContinuousCohomologyFunctor

end Rep
