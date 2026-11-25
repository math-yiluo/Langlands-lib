/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMates
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreLaws

/-! # Core transport assembly for the exceptional ring family -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

private def normalizedEvaluation
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : ExceptionalIntegralScalar.TransportCoreData l Ω D hl c operation left)
    (h : ExceptionalIntegralScalar.TransportCoreLaws l Ω D hl c operation left d)
    (E : FieldStage.{u} l) (n : ℕ) :
    d.F E ⋙ (d.reconstruction E false).evaluation n ≅
      (d.reconstruction E true).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F := by
  let RX := d.reconstruction E true
  let RY := d.reconstruction E false
  let I := (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).ι
  let V := sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E.carrier (n + 1)) c
  let eA :=
    Functor.isoWhiskerLeft (d.F E) (eqToIso (RY.evaluation_eq n)) ≪≫
      Functor.isoWhiskerRight (eqToIso (h.support E))
        (coefficientSequenceDerivedEvaluation l E.carrier Y n) ≪≫
      Functor.isoWhiskerLeft (ExceptionalIntegralScalar.sequenceProperty l E X).ι
        (IntegralSystemRealization.supportEvaluation
          l E.carrier (d.operations E) c n)
  let eB := Functor.isoWhiskerLeft (RX.evaluation n)
      (left (.finite E ⟨n + 1, Nat.succ_pos n⟩)) ≪≫
    Functor.isoWhiskerLeft
      (RX.evaluation n ⋙ (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) X).ι)
      (PurCompactSupport.finiteImageIso l E.carrier n c) ≪≫
    Functor.isoWhiskerRight (eqToIso (RX.evaluation_eq n)) V
  exact Functor.fullyFaithfulCancelRight I (eA ≪≫ eB.symm)

/-- The normalized evaluation lifts the system support evaluation: after the finite
left realization its finite inclusion is the support evaluation.
Proof: cancel the full inclusion by `map_preimage`, cancel the finite left
realization and the finite image comparison, and remove the equality transports.
Source: Zheng, Proposition 5.26 (blueprint: lem-sf-exceptional-ring-transport-core). -/
private theorem normalizedEvaluation_support
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : ExceptionalIntegralScalar.TransportCoreData l Ω D hl c operation left)
    (h : ExceptionalIntegralScalar.TransportCoreLaws l Ω D hl c operation left d)
    (E : FieldStage.{u} l) (n : ℕ)
    (K : (ExceptionalIntegralScalar.sequenceProperty l E X).FullSubcategory) :
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).ι.map
        ((normalizedEvaluation l Ω D hl c operation left d h E n).hom.app K) ≫
      (left (.finite E ⟨n + 1, Nat.succ_pos n⟩)).hom.app
        (((d.reconstruction E true).evaluation n).obj K) ≫
      (PurCompactSupport.finiteImageIso l E.carrier n c).hom.app
        (((d.reconstruction E true).evaluation n).obj K).obj ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E.carrier (n + 1)) c).map
        ((eqToIso ((d.reconstruction E true).evaluation_eq n)).hom.app K) ≍
      (IntegralSystemRealization.supportEvaluation l E.carrier (d.operations E) c n).hom.app
        K.obj := by
  let eB := Functor.isoWhiskerLeft ((d.reconstruction E true).evaluation n)
      (left (.finite E ⟨n + 1, Nat.succ_pos n⟩)) ≪≫
    Functor.isoWhiskerLeft
      ((d.reconstruction E true).evaluation n ⋙
        (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) X).ι)
      (PurCompactSupport.finiteImageIso l E.carrier n c) ≪≫
    Functor.isoWhiskerRight (eqToIso ((d.reconstruction E true).evaluation_eq n))
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E.carrier (n + 1)) c)
  have hB : (left (.finite E ⟨n + 1, Nat.succ_pos n⟩)).hom.app
        (((d.reconstruction E true).evaluation n).obj K) ≫
      (PurCompactSupport.finiteImageIso l E.carrier n c).hom.app
        (((d.reconstruction E true).evaluation n).obj K).obj ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E.carrier (n + 1)) c).map
        ((eqToIso ((d.reconstruction E true).evaluation_eq n)).hom.app K) = eB.hom.app K := rfl
  erw [hB]
  dsimp only [normalizedEvaluation]
  simp only [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  erw [Iso.trans_hom, NatTrans.comp_app, Category.assoc, Iso.symm_hom,
    Iso.inv_hom_id_app, Category.comp_id]
  erw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app]
  erw [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  erw [eqToIso.hom, eqToHom_app, eqToHom_comp_heq_iff, eqToIso.hom, eqToHom_app, eqToHom_map,
    eqToHom_comp_heq_iff]
  rfl

/-- The normalized integral system transport can be assembled from the already
constructed finite and integral operation family. The construction uses the
reduction/limit equivalences at each finite coefficient field, the actual
proper/open system realization, and the evaluation/unit/counit comparison maps.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26; this is the transport-data part of the exceptional ring family proof
(blueprint: lem-sf-exceptional-ring-transport-core).

Proof: for each finite coefficient field, apply the actual strict-system
transport and normalized reconstruction equivalence. Conjugate its system
adjunction through the equivalence, and use the simultaneous proper/open
realization to obtain the prescribed integral left realization. Retain the
whole-system unit and counit, their finite evaluations, and all common bounds.
The finite and integral operations supplied by the ring-stage assembly are the
corresponding reconstructed operations, so these maps satisfy every field of
`ExceptionalIntegralScalar.Transported`. Empty schemes use the zero adjunction
and positive finite levels use exponent `n + 1`.
The left realizations are supplied with their integer shift-compatibility witnesses.
-/
theorem exists_exceptional_transport_for_operations
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
    Nonempty (ExceptionalIntegralScalar.Transported l Ω D hl c
      operation left) := by
  obtain ⟨d, ⟨h⟩⟩ := ExceptionalIntegralScalar.exists_exceptional_transport_core_laws
    l Ω D hl f c operation left leftShift
  let d' : ExceptionalIntegralScalar.TransportCoreData l Ω D hl c operation left :=
    { d with
      evaluationF := normalizedEvaluation l Ω D hl c operation left d h
      evaluationG := fun _ _ ↦ Adjunction.compatibleRightComparison _ _ _ }
  exact ⟨{
    leftShift := d'.leftShift
    reconstruction := d'.reconstruction
    operations := d'.operations
    realizations := d'.realizations
    F := d'.F
    G := d'.G
    adjunction := d'.adjunction
    support := h.support
    realizeF := d'.realizeF
    realizeG := d'.realizeG
    adjunction_eq := h.adjunction_eq
    reductionF := d'.reductionF
    reductionF_eq := h.reductionF_eq
    reductionG := d'.reductionG
    reductionG_eq := h.reductionG_eq
    evaluationF := d'.evaluationF
    evaluationG := d'.evaluationG
    evaluation_unit := fun E n K ↦ (d'.evaluationG E n).unit K
    evaluation_counit := fun E n K ↦ (d'.evaluationG E n).counit K
    evaluation_support := fun E n K ↦
      normalizedEvaluation_support l Ω D hl c operation left d h E n K
    integralLeft := d'.integralLeft
    integralLeft_normalized := h.integralLeft_normalized
    inputGood := h.inputGood
    openGood := h.openGood
    integral_system_normalized := h.integral_system_normalized }⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
