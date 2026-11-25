/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCorePostData
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Data fields for exceptional integral transport

This interface isolates the object, functor, adjunction, and comparison-isomorphism
fields of the normalized exceptional transport record. The right comparison is
constructed by uniqueness of right adjoints. The finite right evaluation comparison
carries its evaluated unit and counit equations. It is constructed by the mates
correspondence; its inverse is not used. The remaining compatibility equations
are supplied separately by `ExceptionalRingTransportCoreLaws`.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

structure TransportCoreData
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
      LeftRealization.{u} l Ω c s (operation s)) where
  leftShift (s : RingStage.{u} l) : (left s).hom.CommShift ℤ
  reconstruction (E : FieldStage.{u} l) (side : Bool) :
    Reconstruction l E (endpoint X Y side)
  operations (E : FieldStage.{u} l) : IntegralSystemRealization.Operations l E.carrier
  realizations (E : FieldStage.{u} l) :
    IntegralSystemRealization.Realizations l E.carrier D (operations E)
  F (E : FieldStage.{u} l) : (sequenceProperty l E X).FullSubcategory ⥤
    (sequenceProperty l E Y).FullSubcategory
  G (E : FieldStage.{u} l) : (sequenceProperty l E Y).FullSubcategory ⥤
    (sequenceProperty l E X).FullSubcategory
  adjunction (E : FieldStage.{u} l) : F E ⊣ G E
  realizeF (E : FieldStage.{u} l) : (operation (.integral E)).F ≅
    PurReconstruction.realized (reconstruction E true).equivalence
      (reconstruction E false).equivalence (F E)
  evaluationF (E : FieldStage.{u} l) (n : ℕ) :
    F E ⋙ (reconstruction E false).evaluation n ≅
      (reconstruction E true).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F
  evaluationG (E : FieldStage.{u} l) (n : ℕ) :
    Adjunction.CompatibleRightComparison (adjunction E)
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction (evaluationF E n)
  integralLeft (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier

/-- The canonical right comparison determined by the two specified adjunctions
and the left comparison. This is an explicit construction, not a freely chosen
isomorphism: its inverse is the unique adjunction-compatible comparison.
Source: Zheng, Construction 5.25, with uniqueness of right adjoints.
(blueprint: lem-sf-exceptional-ring-transport-core-data) -/
def TransportCoreData.realizeG
    {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {D : FiniteFieldDatum.{u}} {hl : l ≠ D.p}
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (d : TransportCoreData l Ω D hl c operation left) (E : FieldStage.{u} l) :
    (operation (.integral E)).G ≅
      PurReconstruction.realized (d.reconstruction E false).equivalence
        (d.reconstruction E true).equivalence (d.G E) :=
  (Adjunction.rightAdjointUniq
    ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
      (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm)
    (operation (.integral E)).adjunction).symm

section ReductionComparisons
variable {l : ℕ} [Fact l.Prime] {Ω : Type u} [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] {D : FiniteFieldDatum.{u}} {hl : l ≠ D.p}
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  {c : Compactification f}
  {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
  {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
  (d : TransportCoreData l Ω D hl c operation left)

/-- The reduction comparison is the realization comparison followed by the target
reconstruction counit. It is constructed from these maps, rather than chosen independently.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-ring-transport-core-data) -/
def TransportCoreData.reductionF (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ (d.reconstruction E false).equivalence.functor ≅
      (d.reconstruction E true).equivalence.functor ⋙ d.F E :=
  Functor.isoWhiskerRight (d.realizeF E) (d.reconstruction E false).equivalence.functor ≪≫
    Functor.isoWhiskerLeft ((d.reconstruction E true).equivalence.functor ⋙ d.F E)
      (d.reconstruction E false).equivalence.counitIso ≪≫ Functor.rightUnitor _

/-- The right-adjoint reduction comparison uses the realization comparison and the
source reconstruction counit, with the two endpoints interchanged.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-ring-transport-core-data) -/
def TransportCoreData.reductionG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ⋙ (d.reconstruction E true).equivalence.functor ≅
      (d.reconstruction E false).equivalence.functor ⋙ d.G E :=
  Functor.isoWhiskerRight (d.realizeG E) (d.reconstruction E true).equivalence.functor ≪≫
    Functor.isoWhiskerLeft ((d.reconstruction E false).equivalence.functor ⋙ d.G E)
      (d.reconstruction E true).equivalence.counitIso ≪≫ Functor.rightUnitor _

end ReductionComparisons

/-- The data fields have the construction described in the transport proof.
(blueprint: lem-sf-exceptional-ring-transport-core-data)
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26.  The strict-system transport, reconstruction equivalences, and integral
proper/open realization are assembled first; all displayed functors and
isomorphisms are the resulting data. (blueprint: lem-sf-exceptional-ring-transport-core)
The left realizations are supplied with their integer shift-compatibility witnesses.
-/
theorem exists_exceptional_transport_core_data
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
    Nonempty (TransportCoreData l Ω D hl c operation left) := by
  classical
  obtain ⟨pre⟩ :=
    exists_exceptional_transport_reconstructions l Ω D hl f c operation left leftShift
  let leftShift := pre.leftShift
  let recon := pre.reconstruction
  let operations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Operations l E.carrier :=
    fun E ↦ (IntegralSystemRealization.integralCompactificationSystemRealization
      l E.carrier D hl).choose
  have hrealizations : ∀ E : FieldStage.{u} l,
      Nonempty (IntegralSystemRealization.Realizations l E.carrier D (operations E)) := by
    intro E
    exact (IntegralSystemRealization.integralCompactificationSystemRealization
      l E.carrier D hl).choose_spec
  let realizations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Realizations l E.carrier D (operations E) :=
    fun E ↦ (hrealizations E).some
  obtain ⟨p⟩ := exists_exceptional_transport_post_data l Ω D hl f c operation left
    recon operations realizations
  refine ⟨{
    leftShift := leftShift,
    reconstruction := recon,
    operations := operations,
    realizations := realizations,
    F := p.F,
    G := p.G,
    adjunction := p.adjunction,
    realizeF := p.realizeF,
    evaluationF := p.evaluationF,
    evaluationG := p.evaluationG,
    integralLeft := p.integralLeft }⟩

end WeilConjectures.ExceptionalIntegralScalar
