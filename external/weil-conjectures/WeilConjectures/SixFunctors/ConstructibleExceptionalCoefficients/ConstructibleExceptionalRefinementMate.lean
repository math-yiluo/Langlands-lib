/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Completing a left refinement by its adjunction conjugate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Complete a shift-compatible left refinement by the conjugate right isomorphism.
Source: Mathlib adjunction conjugation; blueprint exceptional construction, refinement step
(blueprint: def-sf-constructible-exceptional-refinement-mate).
The counit and unit equations are the defining conjugation equations. For shifts, express
its right map as the old unit, the image of the left map and the new counit; each factor
commutes with shifts because both adjunctions and the left map do. -/
def refinementComparisonOfLeft {X Y : Scheme.{max u v}} {s : Stage.{max u v} l}
    (A B : Operation.{u, v} l Ω X Y s) (α : A.F ≅ B.F)
    (hα : α.hom.CommShift ℤ) : RefinementComparison.{u, v} l Ω A B where
  left := α
  right := conjugateIsoEquiv B.adjunction A.adjunction α
  counit L := (conjugateEquiv_counit B.adjunction A.adjunction α.hom L).symm
  unit K := unit_conjugateEquiv B.adjunction A.adjunction α.hom K
  leftShift := hα
  rightShift := by
    let := hα
    let := A.unitShift
    let := A.counitShift
    let := B.unitShift
    let := B.counitShift
    have he : (conjugateIsoEquiv B.adjunction A.adjunction α).hom =
        B.G.rightUnitor.inv ≫ Functor.whiskerLeft B.G A.adjunction.unit ≫
          (Functor.associator B.G A.F A.G).inv ≫
          Functor.whiskerRight (Functor.whiskerLeft B.G α.hom) A.G ≫
          Functor.whiskerRight B.adjunction.counit A.G ≫ A.G.leftUnitor.hom := by
      ext L
      simp [conjugateEquiv_apply_app]
    rw [he]
    infer_instance

end WeilConjectures.ConstructibleExceptionalCoefficients
