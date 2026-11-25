/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PullbackIdentitiesScalarExtension
import WeilConjectures.AlgebraicGeometry.Integral.IntegralInverseImageComparisonComposition
import WeilConjectures.SmoothPurity.Integral.IntegralIdentityCompositorSections
import WeilConjectures.TraceFormula.Supporting.NormalizedIntegralGeometricCoherence
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonNatural
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting

set_option linter.privateModule false

/-!
# Integral inverse cancellation after precomposition

The normalized ordinary unit is checked on sections. Composition compatibility and
naturality then force kappa to respect the completed unit, giving the inverse
cancellation identity without another normalization assumption.

Source: the Weil-structures paragraph of the open-closed triangle proof; Stacks
Tags 03D6, 015F and 04VG.
(blueprint: lem-sf-integral-automorphism-cancellation-precomposition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local irreducible] integralDerivedPullback integralComparisonComposition
  integralComparisonUnit inverseImagePullbackComparisonDerived pullbackIdentityEpsilon
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def moduleTransport (X : Scheme.{u}) {f g : X ⟶ X}
    [IsIso f] [IsIso g] (w : f = g) :
    inverseImageIntegralModules l E f ≅ inverseImageIntegralModules l E g := by
  subst g
  exact Iso.refl _

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
set_option allowUnsafeReducibility true in
attribute [local irreducible] moduleTransport
  inverseImageCompletedCoefficientMap

end WeilConjectures
