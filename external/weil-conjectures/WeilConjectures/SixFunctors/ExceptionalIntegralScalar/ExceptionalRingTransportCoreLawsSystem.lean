/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreLawsSystemSupport
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreLawsSystemAdjunction
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreLawsSystemReduction

/-! The system-level compatibility laws for exceptional integral transport.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

structure TransportCoreSystemLaws
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) where
  support (E : FieldStage.{u} l) :
    d.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g
  adjunction_eq (E : FieldStage.{u} l) :
    (operation (.integral E)).adjunction =
      ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm).ofNatIsoRight (d.realizeG E).symm
  reductionF_eq (E : FieldStage.{u} l)
      (K : C.{u} l Ω X (.integral E)) :
    (d.reductionF E).hom.app K =
      (d.reconstruction E false).equivalence.functor.map ((d.realizeF E).hom.app K) ≫
        (d.reconstruction E false).equivalence.counit.app
          ((d.F E).obj ((d.reconstruction E true).equivalence.functor.obj K))
  reductionG_eq (E : FieldStage.{u} l)
      (K : C.{u} l Ω Y (.integral E)) :
    (d.reductionG E).hom.app K =
      (d.reconstruction E true).equivalence.functor.map ((d.realizeG E).hom.app K) ≫
        (d.reconstruction E true).equivalence.counit.app
          ((d.G E).obj ((d.reconstruction E false).equivalence.functor.obj K))

/-- The system laws are supplied by strict-system transport and reconstruction.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Proposition 5.24.
Proof: transport the strict-system support and reconstruction comparisons through
both equivalences and retain their displayed equations.
(blueprint: lem-sf-exceptional-ring-transport-core-system-laws)
-/
theorem exists_exceptional_transport_core_system_laws
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
    Nonempty (TransportCoreSystemLaws l Ω D hl c operation left d) := by
  obtain ⟨hs⟩ := exists_exceptional_transport_core_system_support_law
    l Ω D hl f c operation left d
  obtain ⟨ha⟩ := exists_exceptional_transport_core_system_adjunction_law
    l Ω D hl f c operation left d
  obtain ⟨hrF, hrG⟩ := exists_exceptional_transport_core_system_reduction_laws
    l Ω D hl f c operation left d
  exact ⟨{
    support := hs
    adjunction_eq := ha
    reductionF_eq := hrF
    reductionG_eq := hrG }⟩

end WeilConjectures.ExceptionalIntegralScalar
