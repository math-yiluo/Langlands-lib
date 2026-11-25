/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstruction

/-! # Integral exceptional operation and compact-support realization -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- An integral exceptional operation with its compact-support realization exists.
Source: Zheng, Construction 5.25 and Propositions 5.24 and 5.26; coefficient
construction step 3 (blueprint: lem-sf-integral-support-operation-realization).

Proof: construct the normalized reduction/total-limit operation on the complete
finite-Tor categories, transport its system adjunction through the recorded
reconstruction equivalences, and identify its ambient realization with the
proper/open compact-support image. The full finite-Tor inclusions then provide
the required operation and left realization.
-/
theorem exists_integral_support_operation_realization
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (E : FieldStage.{u} l) :
    ∃ A : Operation.{u} l Ω X Y (.integral E),
      Nonempty (LeftRealization.{u} l Ω c (.integral E) A) := by
  obtain ⟨_, rX, rY, s, a, hd⟩ :=
    ExceptionalIntegralReconstruction.exceptionalIntegralReconstruction
      l E.carrier D hl f c
  obtain ⟨d⟩ := hd
  let := d.leftAdditive
  let := d.rightAdditive
  let := d.leftShift
  let := d.rightShift
  exact ⟨{
    F := ExceptionalIntegralReconstruction.integralLeft l E.carrier c rX rY s a
    G := ExceptionalIntegralReconstruction.integralRight l E.carrier c rX rY s a
    adjunction := ExceptionalIntegralReconstruction.integralAdjunction
      l E.carrier c rX rY s a
    leftExact := d.leftExact
    rightExact := d.rightExact
    unitShift := d.unitShift
    counitShift := d.counitShift }, ⟨d.realization⟩⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
