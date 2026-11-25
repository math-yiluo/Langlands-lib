/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreReconstruction
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCorePostFunctorData

/-! # Functor and comparison fields for exceptional integral transport -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

/-- The transported functors and their comparison maps can be assembled once the
reconstruction, operation, and integral realization choices are fixed.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24 and 5.26.
The proof transports the strict-system adjunction through the two reconstruction
 equivalences, identifies its finite evaluations, and uses the proper/open integral
realization to define the final integral-left comparison.
(blueprint: new-lem-sf-exceptional-ring-transport-post-data)
-/
structure TransportCorePostData
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
    (reconstruction : ∀ E : FieldStage.{u} l, ∀ side : Bool,
      Reconstruction l E (endpoint X Y side))
    (operations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Operations l E.carrier)
    (realizations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Realizations l E.carrier D (operations E)) where
  F (E : FieldStage.{u} l) : (sequenceProperty l E X).FullSubcategory ⥤
    (sequenceProperty l E Y).FullSubcategory
  G (E : FieldStage.{u} l) : (sequenceProperty l E Y).FullSubcategory ⥤
    (sequenceProperty l E X).FullSubcategory
  adjunction (E : FieldStage.{u} l) : F E ⊣ G E
  realizeF (E : FieldStage.{u} l) : (operation (.integral E)).F ≅
    PurReconstruction.realized (reconstruction E true).equivalence
      (reconstruction E false).equivalence (F E)
  realizeG (E : FieldStage.{u} l) : (operation (.integral E)).G ≅
    PurReconstruction.realized (reconstruction E false).equivalence
      (reconstruction E true).equivalence (G E)
  reductionF (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ (reconstruction E false).equivalence.functor ≅
      (reconstruction E true).equivalence.functor ⋙ F E
  reductionG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ⋙ (reconstruction E true).equivalence.functor ≅
      (reconstruction E false).equivalence.functor ⋙ G E
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

/-- Existence of the transported functor and comparison fields.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24 and 5.26.
The strict-system transport supplies the adjunction, its finite evaluations, and the
reduction comparisons; the integral compactification realization supplies `integralLeft`.
(blueprint: new-lem-sf-exceptional-ring-transport-post-data)
-/
theorem exists_exceptional_transport_post_data
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (reconstruction : ∀ E : FieldStage.{u} l, ∀ side : Bool,
      Reconstruction l E (endpoint X Y side))
    (operations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Operations l E.carrier)
    (realizations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Realizations l E.carrier D (operations E)) :
    Nonempty
      (TransportCorePostData l Ω D hl c operation left reconstruction operations realizations) := by
  classical
  obtain ⟨p⟩ := exists_exceptional_transport_post_functor_data
    l Ω D hl f c operation left reconstruction operations realizations
  obtain ⟨integralLeft⟩ := exists_exceptional_transport_integral_left
    l Ω D hl f c operation left reconstruction operations realizations
  exact ⟨{
    F := p.F
    G := p.G
    adjunction := p.adjunction
    realizeF := p.realizeF
    realizeG := p.realizeG
    reductionF := p.reductionF
    reductionG := p.reductionG
    evaluationF := p.evaluationF
    evaluationG := p.evaluationG
    integralLeft := integralLeft }⟩

end WeilConjectures.ExceptionalIntegralScalar
