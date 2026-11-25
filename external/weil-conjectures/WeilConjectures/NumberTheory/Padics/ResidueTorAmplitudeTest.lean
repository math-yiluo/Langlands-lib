/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitudeResidue
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

set_option linter.privateModule false

/-!
# Testing finite Tor amplitude at the residue field

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-trace-perfectness/
`lem-exc-residue-tor-test.md` (blueprint: theorem-f-shriek-finite-coefficients--1).
-/

@[expose] public section

-- Keep quotient coefficient rings on the same instance path as the generic residue criterion.
-- Otherwise checking its specialization unfolds the full quotient-ring construction repeatedly.
attribute [local instance 20000] CommRing.toRing

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace Padic

end Padic

namespace AlgebraicGeometry.Etale

-- Match the braidings used by the existing étale derived tensor construction.
attribute [local instance 20000] SymmetricCategory.toBraidedCategory sheafBraidedCategory

private theorem derivedTensor_eq_curriedTensor
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) :
    derivedTensor A T = curriedTensor (_root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :=
  rfl

end AlgebraicGeometry.Etale
