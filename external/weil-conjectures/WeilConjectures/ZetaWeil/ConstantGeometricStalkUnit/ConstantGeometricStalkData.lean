/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace

import all WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension

/-! # Constructions for constant geometric coefficient stalks

Source: the constant-sheaf clause of `theorem-grothendieck-lefschetz-trace-formula--8`, reviewed
expansion steps 2--8 (blueprint: def-zl-constant-geometric-stalk-constructions).

The existing section, pullback, iteration and scalar-comparison constructions are
re-exported through their original module without changing their definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConstantGeometricStalkUnit

attribute [-instance] coefficientComplexModuleDerived pointScalarModuleDerived
  pointCompletedSheafDerived pointScalarAbLocallyBijective
  coefficientComplexIntegralLimits
  coefficientComplexIntegralColimits coefficientComplexRationalAdditive
  coefficientComplexRationalLimits coefficientComplexRationalColimits
  coefficientComplexFieldAdditive coefficientComplexFieldLimits coefficientComplexFieldColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

end WeilConjectures.ConstantGeometricStalkUnit
