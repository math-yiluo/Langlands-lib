/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarOperationCore

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- The finite operation package exists for every finite coefficient stage.
Source: Zheng, Proposition 2.23; Stacks 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-operation).

This is the operation portion of the eight-step proof: the compact-support and
exceptional functors are restricted to the full finite-Tor categories, their
adjunction is normalized on etale-origin witnesses, and the inherited shift data
is retained.  The remaining scalar compatibility is stated separately below.
-/
theorem finiteScalarOperation_exists
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Nonempty (Operation l E n c) := by
  classical
  obtain ⟨o⟩ := operationCore_exists D l _hl E n f c
  let o' : Operation l E n c := {
    F := o.F
    G := o.G
    left := o.left
    right := o.right
    adjunction := o.adjunction
    leftShift := o.leftShift
    rightShift := o.rightShift
    unitShift := o.unitShift
    counitShift := o.counitShift
    leftShiftRealization := o.leftShiftRealization
    normalized := operationCore_normalized D l _hl E n f c o }
  exact ⟨o'⟩

end WeilConjectures.ExceptionalFiniteScalar
