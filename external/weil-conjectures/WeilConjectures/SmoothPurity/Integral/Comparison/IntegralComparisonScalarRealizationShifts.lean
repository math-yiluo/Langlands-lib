/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonCanonicalShifts
public import WeilConjectures.SmoothPurity.Completed.CompletedScalarShiftCoordinates

/-! # Shift compatibility of the normalized scalar realization
Source: Stacks Tags 014E, 06YY and 0941.
(blueprint: lem-sf-integral-scalar-realization-shifts). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The scalar realization respects the universal counit shift on strict systems
and the adjoint reduction shift, with the actual representative descent.

Source: Stacks Tags 014E, 06YY and 0941; the Weil-structures paragraph
of the open-closed triangle proof, expanded in parent node steps 2–7.
(blueprint: lem-sf-integral-scalar-realization-shifts).

Proof: take a flat-term K-flat representative P and a simultaneous quotient
presentation from SE.reductionModel. Compute each total-limit projection on an
injective replacement and its shift;
the projection in degree j becomes the same projection in degree j+m.
Transpose this equation through the finite scalar adjunction. By the normalized
counit projection identity its mate is the finite evaluation comparison for
reduction. Hence the adjoint shift on reduction commutes with every such
comparison, and the universal finite scalar counit identifies it with degree
reindexing on the presentation. Present P[m] by C[m], taking its derived
presentation isomorphism to be e[m] conjugated by the reduction and localization
shifts. Its finite presentation equation is the mate equation, and its
horizontal transition equation is the shift of the old equation.
The universal cochain scalar counit commutes with its chosen coherent shift
on every complex C; no K-flatness of the quotient diagram C is required. Its generator
x tensor a is unchanged by shift and commutes with every quotient transition.
Define the shifted scalar presentation q_m by conjugating q[m] with the
termwise restriction and scalar shifts. Its prescribed scalar-unit generator
has exactly the old image in degree j+m. Generators determine maps of the
extension modules by their tensor/sheafification universal property, so the
presentation normalization gives this q_m. The two universal scalar counit
squares therefore give the scalar presentation square in the whole diagram. Compute
the Roos comparison using a K-injective resolution and its shifted resolution.
The comparison is induced by (0,z): its first coordinate is the limit tuple,
and its second is zero, by integralComparisonLimitToRoos. The two coordinate
equations show directly that shifting it commutes with the signed Roos shift.
The formula rho.computes identifies this with the chosen bridge on injectives;
naturality along the replacement extends the equation to the original tower.
Compare M's normalization on P and P[m]; the two coordinates in hc fix
exactly that shift on the completed scalar complex. Cancel the presentation
isomorphisms and apply hs to identify the descended scalar shift. The composite
with the scalar counit after total limit is invertible by this normalization;
no invertibility of the scalar counit before total limit is needed. This gives
the square on Q(P). Naturality with respect to a K-flat resolution transports
it to arbitrary derived objects, independently of the chosen presentation. -/
theorem integralComparisonScalarRealization_commShift
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X)
    (M : IntegralComparisonScalarModel l E L ι X SE ρ)
    (c : (integralScalarComplexFunctor l E L ι X).CommShift ℤ)
    (hc : ∀ P m, completedScalarShiftConeFormula ι X c P m)
    (s : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ)
    (hs : completedScalarShiftIntegralNormalization ι X c s) :
    letI := s
    letI := integralComparisonReductionShift l E X SE
    letI := integralComparisonSequenceScalarShift l E L ι X
    letI := integralComparisonLimitShift l L X
    NatTrans.CommShift M.realization.hom ℤ := by
  sorry

end WeilConjectures
