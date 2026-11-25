/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorShifts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.KFlatDerivedAdjunctionTransportShifts
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Canonical shifts of the ambient condensed-module exchange

Source: Stacks Project, derived.tex, Tags 015F, 05SU and 0DVC; blueprint
compactification coherence, refinement (2)
(blueprint: lem-sfb-ambient-qcqs-exchange-canonical-shifts).

All categories are ordinary unbounded derived categories. The pullback shifts are
transported from exact termwise inverse image by `modulePullbackExactComparison`;
the pushforward shifts are the fixed K-injective shifts. The transformation is the
published `condensedAmbientExchange`, rather than a choice of base-change map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
  {f : X ⟶ Y} {f' : X' ⟶ C}

end AlgebraicGeometry.ProEtale.CondensedRing
