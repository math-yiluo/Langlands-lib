/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreReconstruction
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportFiniteComparison

/-! # Functor and comparison fields for exceptional integral transport

This module isolates the transported functors and comparison maps from the
reconstruction and integral realization choices.  It is the strictly smaller
assembly package used by `TransportCorePostData`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

/-- The transported functors and comparison fields, with the reconstruction and
integral realization choices supplied as parameters.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: new-lem-sf-exceptional-ring-transport-post-functor-data)
-/
structure TransportCorePostFunctorData
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

private def reconstructionFiniteReduction
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (n : ℕ) :
    R.equivalence.functor ⋙ R.evaluation n ⋙
        (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) T).ι ≅
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        pbcDerivedExtend (PurCompactSupport.projection l E.carrier (n + 1)
          (Nat.succ_pos n) T) :=
  Functor.isoWhiskerLeft R.equivalence.functor (eqToIso (R.evaluation_eq n)) ≪≫
    Functor.isoWhiskerRight (eqToIso R.reduction)
      (coefficientSequenceDerivedEvaluation l E.carrier T n) ≪≫
    Functor.isoWhiskerLeft (finiteTorConstructibleIntegral l E.carrier T).ι
      (R.calculus.reductionEvaluation n) ≪≫
    Functor.isoWhiskerLeft (finiteTorConstructibleIntegral l E.carrier T).ι
      (PurCompactSupport.finiteReductionIso l E.carrier T n).symm

private def conjugateRealization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (eX : A ≌ B) (eY : C ≌ D) (F : A ⥤ C) :
    F ≅ PurReconstruction.realized eX eY
      (PurReconstruction.realized eX.symm eY.symm F) :=
  (eX.funInvIdAssoc (F ⋙ eY.functor ⋙ eY.inverse) ≪≫
    Functor.isoWhiskerLeft F eY.unitIso.symm ≪≫ F.rightUnitor).symm

private def integralLeftEvaluation
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (E : FieldStage.{u} l) (n : ℕ)
    (A : Operation.{u} l Ω X Y (.integral E))
    (B : Operation.{u} l Ω X Y (.finite E ⟨n + 1, Nat.succ_pos n⟩))
    (leftA : LeftRealization.{u} l Ω c (.integral E) A)
    (leftB : LeftRealization.{u} l Ω c (.finite E ⟨n + 1, Nat.succ_pos n⟩) B)
    (RX : Reconstruction l E X) (RY : Reconstruction l E Y) :
    A.F ⋙ RY.equivalence.functor ⋙ RY.evaluation n ≅
      RX.equivalence.functor ⋙ RX.evaluation n ⋙ B.F := by
  let q := Functor.whiskerLeft (finiteTorConstructibleIntegral l E.carrier X).ι
    (PurCompactSupport.comparison
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)) c)
  have : IsIso q := by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ q
      (fun K ↦ (sfQcqsCompactSupport_finiteComparison l E.carrier D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c ⟨K.obj, K.property.1⟩).2 n)
  exact ((finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).fullyFaithfulι
    |>.whiskeringRight (finiteTorConstructibleIntegralCategory l E.carrier X)).preimageIso
      (Functor.isoWhiskerLeft A.F (reconstructionFiniteReduction l E Y RY n) ≪≫
        Functor.isoWhiskerRight leftA
          (pbcDerivedExtend (PurCompactSupport.projection l E.carrier (n + 1)
            (Nat.succ_pos n) Y)) ≪≫
        asIso q ≪≫
        Functor.isoWhiskerRight (reconstructionFiniteReduction l E X RX n).symm
          (PurCompactSupport.image
            (PurCompactSupport.finite l E.carrier (n + 1) (Nat.succ_pos n)) c) ≪≫
        Functor.isoWhiskerLeft (RX.equivalence.functor ⋙ RX.evaluation n) leftB.symm)

set_option linter.unusedVariables false in
/-- The strict-system transport and normalized reconstruction calculus produce
all transported functors, adjunctions, evaluations, and the integral-left
comparison once the reconstruction and realization choices are fixed.
The proof is the construction in Zheng, Constructions 4.1 and 5.25,
Lemma 5.22 and Propositions 5.24 and 5.26: transport the strict adjunction,
conjugate it through the two reconstruction equivalences, identify finite left
evaluations, and construct their right comparisons by the mates correspondence.
The unit and counit identities are part of this explicit construction.
(blueprint: new-lem-sf-exceptional-ring-transport-post-functor-data)
-/
theorem exists_exceptional_transport_post_functor_data
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
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
      IntegralSystemRealization.Realizations l E.carrier D (operations E)) :
    Nonempty (TransportCorePostFunctorData l Ω D hl c operation left reconstruction
      operations realizations) := by
  classical
  let eX (E : FieldStage.{u} l) := (reconstruction E true).equivalence
  let eY (E : FieldStage.{u} l) := (reconstruction E false).equivalence
  let F (E : FieldStage.{u} l) :=
    PurReconstruction.realized (eX E).symm (eY E).symm (operation (.integral E)).F
  let G (E : FieldStage.{u} l) :=
    PurReconstruction.realized (eY E).symm (eX E).symm (operation (.integral E)).G
  refine ⟨{
    F := F
    G := G
    adjunction := fun E ↦ PurReconstruction.realizedAdjunction
      (eX E).symm (eY E).symm (operation (.integral E)).adjunction
    realizeF := fun E ↦ conjugateRealization (eX E) (eY E) (operation (.integral E)).F
    realizeG := fun E ↦ conjugateRealization (eY E) (eX E) (operation (.integral E)).G
    reductionF := fun E ↦ ((eX E).funInvIdAssoc
      ((operation (.integral E)).F ⋙ (eY E).functor)).symm
    reductionG := fun E ↦ ((eY E).funInvIdAssoc
      ((operation (.integral E)).G ⋙ (eX E).functor)).symm
    evaluationF := fun E n ↦
      Functor.isoWhiskerLeft (eX E).inverse
        (integralLeftEvaluation l Ω D hl f c E n (operation (.integral E))
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩))
          (left (.integral E)) (left (.finite E ⟨n + 1, Nat.succ_pos n⟩))
          (reconstruction E true) (reconstruction E false)) ≪≫
        (eX E).invFunIdAssoc ((reconstruction E true).evaluation n ⋙
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F)
    evaluationG := fun E n ↦
      Adjunction.compatibleRightComparison _ _ _ }⟩

set_option linter.unusedVariables false in
/-- The coherent integral realization supplies the remaining integral-left
comparison for each field stage.  This is the one-field remainder of the
transport package isolated above.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Proposition 5.26.
(blueprint: new-lem-sf-exceptional-ring-transport-integral-left)
-/
theorem exists_exceptional_transport_integral_left
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
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
      IntegralSystemRealization.Realizations l E.carrier D (operations E)) :
    Nonempty (∀ E : FieldStage.{u} l,
      (operation (.integral E)).F ⋙
          PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
        PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
          sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier) := by
  refine ⟨fun E ↦ ?_⟩
  exact ((sfIntegralConstructible l E.carrier Y).fullyFaithfulι.whiskeringRight
    (finiteTorConstructibleIntegralCategory l E.carrier X)).preimageIso
      (left (.integral E) ≪≫ Functor.isoWhiskerLeft
        (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X)
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c))

end WeilConjectures.ExceptionalIntegralScalar
