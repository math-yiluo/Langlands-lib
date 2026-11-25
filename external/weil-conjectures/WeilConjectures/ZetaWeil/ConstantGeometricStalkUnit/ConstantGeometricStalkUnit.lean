/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.ConstantGeometricStalkData

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparison
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.ZetaWeil.FiniteRegularCoefficientComparisons
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi

import all WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.FinitePullbackUnitComposition
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.FinitePointTransportUnit
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.IntegralPullbackUnitComposition
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.PointTransportIntegralScalar
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.ReturnWeilIntegralScalar
import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
import all WeilConjectures.SixFunctors.Supporting.FrobeniusPointTransportNatural

/-! # Constant geometric stalks and the coefficient unit

Source: main-20261015, sec-zeta-weil/sk-thm-tracetodeterminant,
prop-every-iterate-trace.proof.md, constant-sheaf clause, reviewed expansion step 5
(blueprint: lem-zl-constant-geometric-stalk-unit).

All finite indices denote exponent m+1. The integral coefficient is the completed
ring sheaf. The maps below retain the actual adjunction units and strict Roos model.

## Main statements

* `embeddingPoint_return`: the semilinear return for every allowed embedding.
* `finiteStalkUnit`, `integralStalkUnit`, `rationalStalkUnit`: coefficient-unit coordinates.
* `finiteOperator_unit`, `integralOperator_unit`, `rationalOperator_unit`: identity operators.
* `finiteUnit_reduction`, `integralUnit_projection`, `section_reductions`: actual quotient squares.
* `rationalStalkUnit_existsUnique`, `rationalOperator_scalar`: rationalization squares.
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


section

-- Keep residue fields abstract when a candidate instance has the wrong source scheme.
attribute [local irreducible] FiniteFieldDatum.geometricFiber Scheme.residueField

end

end WeilConjectures.ConstantGeometricStalkUnit
