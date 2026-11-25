/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-! # Coefficient inclusions with explicit field-induced structures -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients
  (Index Coefficient coefficientInclusion coefficientInclusion_laws)

/-- Cache the existing coefficient inclusion with field-induced semiring structures.
Source: the finite-coefficient models of the current blueprint automorphism pullback;
`AlgebraicallyClosedCoefficients.coefficientInclusion` is used verbatim.
(blueprint: def-pod-isomorphism-coefficient-inclusions). -/
def isomorphismCoefficientInclusion
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E L : Index l Ω) (h : E ≤ L) :
    @AlgHom ℚ_[l] (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      inferInstance
      (show Field (Coefficient.{u} l Ω E) from inferInstance).toSemiring
      (show Field (Coefficient.{u} l Ω L) from inferInstance).toSemiring
      inferInstance inferInstance := coefficientInclusion l Ω E L h

section
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

end

end WeilConjectures
