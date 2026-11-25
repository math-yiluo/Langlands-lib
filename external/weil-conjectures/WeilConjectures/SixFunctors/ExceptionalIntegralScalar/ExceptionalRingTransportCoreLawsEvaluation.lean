/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreEvaluationUnit
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreEvaluationCounit
/-! Finite-evaluation laws for exceptional integral transport.
Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: lem-sf-exceptional-ring-transport-core-evaluation-laws) -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
structure TransportCoreEvaluationLaws
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
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) where
  evaluation_unit (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E X).FullSubcategory) :
    ((d.reconstruction E true).evaluation n).map ((d.adjunction E).unit.app K) ≫
      (d.evaluationG E n).hom.app ((d.F E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
        ((d.evaluationF E n).hom.app K) =
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
        (((d.reconstruction E true).evaluation n).obj K)
  evaluation_counit (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E Y).FullSubcategory) :
    (d.evaluationF E n).hom.app ((d.G E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
        ((d.evaluationG E n).hom.app K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
        (((d.reconstruction E false).evaluation n).obj K) =
      ((d.reconstruction E false).evaluation n).map ((d.adjunction E).counit.app K)
/-- The finite adjunction equations hold for the supplied compatible right comparison.
The support comparison is constructed after normalization in `ExceptionalRingTransportCore`;
it is not a law of arbitrary data.
Proof: apply the evaluated unit and counit equations at level `n`.
Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: lem-sf-exceptional-ring-transport-core-evaluation-laws) -/
theorem exists_exceptional_transport_core_evaluation_laws
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) :
    Nonempty (TransportCoreEvaluationLaws l Ω D hl c operation left d) := by
  refine ⟨{
    evaluation_unit := exceptional_transport_core_evaluation_unit
      l Ω D hl f c operation left d
    evaluation_counit := exceptional_transport_core_evaluation_counit
      l Ω D hl f c operation left d }⟩
end WeilConjectures.ExceptionalIntegralScalar
