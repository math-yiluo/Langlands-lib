/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section
set_option autoImplicit false
universe u
/-- The exterior conormal, regarded as a module over the ambient ring.
Source: Stacks Project, Tag 062I.
(blueprint: new-r4-self-tor-conormal-comparison).
(blueprint: new-r4-conormal-exterior-module)
-/
noncomputable abbrev conormalExteriorModule (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (A ⧸ I) (⋀[A ⧸ I]^n I.Cotangent))

