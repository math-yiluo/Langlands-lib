/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
import WeilConjectures.CategoryTheory.DerivedCategory.PoincareDuality.PrincipalDerivedTensorCone
import WeilConjectures.PoincareDuality.Point.PointReductionCoefficientRing

/-! The cone comparison for point-section reduction.

The coefficient calculation is isolated from the transport along a chosen model of sections.
This avoids restating the whole target as an intermediate theorem: the core lemma below has
an arbitrary module complex as input, while the exported clause only transports it along the
supplied isomorphism.  The coefficient calculation is the two-term free resolution of the
principal quotient; its small torsion-freeness input is recorded separately.
(blueprint: lem-pod-point-sections-derived-reduction-cone) -/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Core coefficient cone calculation, for an arbitrary integral module complex.
Source: Stacks Tags 05RT and 06Y6.  Choose a flat-term K-flat representative of `C`; the
universal mixed-tensor counit identifies the derived quotient with its termwise tensor by the
principal quotient.  The two-term free resolution `[R --t--> R]` and
`DerivedCategory.reductionIso` then identify that tensor with the displayed multiplication
cone.  Exactness of the quotient sequence uses the normalized quotient-kernel formula.
(blueprint: lem-pod-point-sections-derived-reduction-cone) -/
theorem point_sections_derived_reduction_module_cone (_hl : l ≠ D.p) (n : ℕ)
    (C : CochainComplex (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ) :
    Nonempty (((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (pointReductionQuotient l E n)).mapDerivedCategory).obj
        ((pointReductionModuleTensor l E n).obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone
        ((ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)) • 𝟙 C))) := by
  exact DerivedCategory.principalDerivedTensorCone (pointReductionQuotient l E n)
    (ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (n + 1))
    (pointReductionQuotient_properties l E n).1
    (pointReductionQuotient_properties l E n).2.1
    (pointReductionQuotient_properties l E n).2.2 C

end WeilConjectures
