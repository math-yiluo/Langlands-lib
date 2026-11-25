/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMates
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalTransportEndpointReconstruction

/-! # Reconstruction choices for exceptional integral transport

This is the reconstruction subproblem isolated from the core transport record.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

structure TransportCorePreData
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s)) where
  leftShift : ∀ s : RingStage.{u} l, (left s).hom.CommShift ℤ
  reconstruction : ∀ E : FieldStage.{u} l, ∀ side : Bool,
    Reconstruction l E (endpoint X Y side)

/-- The normalized reduction/limit reconstructions can be chosen at both endpoints.
Source: Zheng, Construction 5.25 and Proposition 5.26.
The proof applies the normalized reduction/limit theorem to the coefficient sequence at
`X` and `Y`, restricts to the replete subcategories with the common finite and Tor
bounds, and records the resulting equivalence, unit, counit, and evaluation maps.
(blueprint: new-lem-sf-exceptional-ring-transport-reconstructions)
The left realizations are supplied with their integer shift-compatibility witnesses.
-/
theorem exists_exceptional_transport_reconstructions
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (leftShift : ∀ s : RingStage.{u} l, (left s).hom.CommShift ℤ) :
    Nonempty (TransportCorePreData l Ω D hl c operation left) := by
  classical
  have hrecon : ∀ E : FieldStage.{u} l, ∀ side : Bool,
      Nonempty (Reconstruction l E (endpoint X Y side)) := by
    intro E side
    exact exists_exceptional_transport_endpoint_reconstruction l E
  exact ⟨{
    leftShift := leftShift
    reconstruction := fun E side => (hrecon E side).some }⟩

end WeilConjectures.ExceptionalIntegralScalar
