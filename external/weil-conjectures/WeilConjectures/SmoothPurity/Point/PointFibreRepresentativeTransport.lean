/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPointStages

/-! # Further-extension invariance of the point-fibre representative

Source: the scalar-extension tower equation for point sections and the common-stage calculus.
(blueprint: lem-weil-point-fibre-representative-transport).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Enlarging a common coefficient field leaves the displayed point-fibre arrow unchanged.
Source: sections-scalar-extension tower compatibility and common-stage transport,
expanded in the proof of the finite-coefficient point construction, clause 4.
(blueprint: lem-weil-point-fibre-representative-transport).

Proof: write alpha for the source stage associator, phi for pointStageFibreScalarIso,
and tau for the target tensor tower. The normalization of phi by the rational sections
comparison, its tower equation, the pure-tensor normalization of the carrier-lift
comparison, and the Shrink coefficient square give the tower equation for phi.
Apply it to the two endpoints of f. Substitute source transport
alpha_source inverse, T(f), alpha_target into the displayed representative. Naturality
of phi for the last extension moves T(f) across phi. Cancel the adjacent inverse phi
factors at both endpoints. The remaining tau factors cancel against the tower equation
for pointFdQbarStageComp, which is the fieldScalarTower associativity equation.
The resulting arrow is exactly the original representative. This works for reflexive
extensions and zero objects as well: all comparisons remain isomorphisms and the same
cancellation applies; no faithfulness of a scalar transition is used. -/
theorem pointQbarFibreRepresentative_transport
    (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (G H : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ G) (hB : B.stage ≤ G)
    (h : G ≤ H) (f : A.toStage hA ⟶ B.toStage hB) :
    pointQbarFibreRepresentative D l hl Ω A B H (hA.trans h) (hB.trans h)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).tr h f) =
      pointQbarFibreRepresentative D l hl Ω A B G hA hB f := by sorry

end WeilConjectures
