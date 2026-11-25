/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
import WeilConjectures.FourierTransform.CompletedScalarShift
import WeilConjectures.SmoothPurity.Point.PointSectionsTensorShift

/-! # Shift comparison and exactness on finite-stage triangles

Source: steps 13–14 of the point-fibre argument, using the canonical completion
and sections-tensor comparisons.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The common-stage fibre commutes with shifts and has distinguished image on
each distinguished finite-stage triangle.
Source: blueprint finite-coefficient-point, final display, steps 13–14;
pointCompletedScalarShift and pointSectionsTensorShift.
(blueprint: lem-weil-point-qbar-fibre-shift-descent).

Proof: use the exact rational sections comparison supplied by localization at
each coefficient field, and then the termwise field tensor comparison. The
completed scalar comparison and the sections-tensor comparison commute with
every integer shift by their recorded theorems. Their composite and inverse do
as well, hence so does pointStageFibreScalarIso, including the rationalization
and carrier-lift normalizations. Conjugate these comparisons by the source and
target isoToStage maps. Naturality, the identity comparison, and the three-field
comparison equation make the result independent of the chosen representative
and give the zero and addition shift laws for pointQbarFibre. For a triangle
at stage E, its rational fibre triangle is distinguished by pointRationalFibre_exact.
The coefficient ring equivalence from Shrink E to E and extension from E to the
algebraic closure are exact. Their tensor tower comparisons, and the just-proved
shift compatibility, identify this extended triangle with the realized image
under pointQbarFibre of the stage inclusion. Its three vertices are bounded
finite-dimensional by the definition of pointStageFibre. These data witness
pointFdQbarDistinguished. This proves the assertion only on stage images;
descent along an arbitrary source triangle isomorphism is a separate final step. -/
theorem pointQbarFibre_shift_descent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    ∃ c : (pointQbarFibre D l hl Ω).CommShift ℤ,
      ∀ (i : Padic.FiniteCoefficientFields l Ω)
        (T : Triangle (GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) i)),
        T ∈ distTriang _ → DerivedCategory.pointFdQbarDistinguished l Ω
          ((@Functor.mapTriangle _ _ _ _ _ _ _ c).obj
            ((GeneralAlgebraicallyClosedCoefficients.inclusion i).mapTriangle.obj T)) := by
  sorry

end WeilConjectures
