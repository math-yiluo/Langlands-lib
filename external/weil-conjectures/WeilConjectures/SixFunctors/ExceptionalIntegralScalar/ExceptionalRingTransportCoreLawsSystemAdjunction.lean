/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! The adjunction comparison part of the exceptional integral transport system laws.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-adjunction-law).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

section RightComparison

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
  (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
  (d : TransportCoreData l Ω D hl c operation left)

/-- The right realization dictated by the specified adjunction and left realization.
It is the inverse of Mathlib's uniqueness isomorphism between right adjoints of
`(operation (.integral E)).F`. This is a concrete construction from the two
adjunctions, without choosing an arbitrary witness of an existence theorem.
Source: Zheng, Construction 5.25; expanded by uniqueness of right adjoints.
(blueprint: lem-sf-exceptional-system-adjunction-normalized-comparison) -/
abbrev normalizedRealizeG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ≅
      PurReconstruction.realized (d.reconstruction E false).equivalence
        (d.reconstruction E true).equivalence (d.G E) :=
  d.realizeG E

/-- The constructed right realization makes the adjunction comparison exact.
Proof: transporting by the uniqueness isomorphism recovers the specified unit,
and equality of units implies equality of adjunctions.
Source: Zheng, Construction 5.25, with Mathlib's right-adjoint uniqueness formula.
(blueprint: lem-sf-exceptional-system-adjunction-normalized-comparison) -/
theorem normalizedRealizeG_adjunction (E : FieldStage.{u} l) :
    (operation (.integral E)).adjunction =
      ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm).ofNatIsoRight
          (normalizedRealizeG l Ω D hl c operation left d E).symm := by
  exact ((Adjunction.ofNatIsoRight_eq_iff _ _ _).2 rfl).symm

end RightComparison

/--
The strict-system adjunction comparison, transported through the two chosen
reconstruction equivalences, is the adjunction component of the system laws.
The right comparison is constructed from the two adjunctions by
`Adjunction.rightAdjointUniq`. Transporting along its inverse recovers the
specified integral adjunction by `Adjunction.ofNatIsoRight_eq_iff`. This theorem
isolates that single component so the reduction equations can be handled independently.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-adjunction-law).
-/
theorem exists_exceptional_transport_core_system_adjunction_law
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
    (d : TransportCoreData l Ω D hl c operation left) :
    Nonempty (∀ E : FieldStage.{u} l,
      (operation (.integral E)).adjunction =
        ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
          (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
          (d.realizeF E).symm).ofNatIsoRight (d.realizeG E).symm) := by
  exact ⟨normalizedRealizeG_adjunction l Ω D hl c operation left d⟩

end WeilConjectures.ExceptionalIntegralScalar
