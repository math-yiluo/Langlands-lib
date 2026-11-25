/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChangeDefinitions
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistSchemeCompatibility

/-! # Completed integral twist base change

Source: main-20261015 blueprint, sec-six-functors-basics/sk-prop-sf-existence,
`prop-weil-twist-preserves.proof.md`, first and final sentences
(blueprint: lem-weil-integral-twist-base-change).

The line, coefficient inclusion and scalar-extension isomorphism are the published
constructions of `definition-tate-twists`. Scheme naturality is expressed
on their underlying semilinear maps, using the actual inverse-image adjunction.
The helper predicates specify the pullback identifications by roots, powers and evaluation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
