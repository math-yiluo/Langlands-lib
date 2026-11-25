/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCofinalData

/-! # Uniform bounds for ramified left recovery

Source: Zheng, Construction 4.1 and Proposition 5.24; integral scalar mates, step 2
(blueprint: lem-sf-ramified-system-recovery-bounds).
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  Opposite SheafOfModules
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

end WeilConjectures.ExceptionalIntegralScalar
