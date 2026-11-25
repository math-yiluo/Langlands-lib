/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompatibleRightComparison
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemTransport
public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMates
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCofinalMate
public import WeilConjectures.SmoothPurity.Completed.CompletedScalarShiftCoordinates
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
public import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization

/-! # Data for integral scalar mates of the exceptional adjunction

Source: Zheng, Constructions 4.1 and 5.15, Lemma 5.22 and Propositions 5.24, 5.26.
(blueprint: def-sf-exceptional-integral-scalar-transport-data)

The original normalized systems, reconstruction, scalar mates, and transport records
are retained under their original names. Finite evaluation explicitly uses the canonical
comparison between ordinary derived tensor and the recorded quotient derived functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite SheafOfModules
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
attribute [instance] ConstructibleExceptionalCoefficients.Scalar.commShift
  ConstructibleExceptionalCoefficients.Scalar.additive
  ConstructibleExceptionalCoefficients.Operation.leftShift
  ConstructibleExceptionalCoefficients.Operation.rightShift

/-- The inherited shift on the actual finite or integral full inclusion.
Source: blueprint full finite-Tor categories
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
instance inclusionShift (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) (s : RingStage.{u} l) :
    (RingStage.inclusion.{u} l Ω T s).CommShift ℤ :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance

variable (l : ℕ) [Fact l.Prime]

/-- The actual selected coefficient sheaves. Natural index n means exponent n+1.
Source: Zheng, Construction 4.1
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
abbrev rings (E : FieldStage.{u} l) (T : Scheme.{u}) (r : ℕ ↪o ℕ) :=
  selectedSystemRings.{u + 1, u, u + 1} (coefficientSequenceCommRingSystem l E.carrier T) r

/-- Evaluation on the actual selected strict-system localization.
Source: Zheng, Construction 4.1
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
abbrev evaluation (E : FieldStage.{u} l) (T : Scheme.{u}) (r : ℕ ↪o ℕ) (n : ℕ) :=
  derivedSystemEvaluation.{u + 1, u, u + 1} (rings l E T r) n

/-- Normalized sequence-site modules, with one cohomological and one Tor interval.
This is the sequence-site presentation of the strict-system predicate above.
Source: Zheng, Construction 4.1 and Proposition 5.24
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
def sequenceProperty (E : FieldStage.{u} l) (T : Scheme.{u}) :
    ObjectProperty (coefficientSequenceDerived l E.carrier T) :=
  fun N ↦ IsNormalizedCoefficientSequence l E.carrier T N ∧
    ∃ a b c d : ℤ, a ≤ b ∧ c ≤ d ∧ ∀ n : ℕ,
      finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T
        ((coefficientSequenceDerivedEvaluation l E.carrier T n).obj N) ∧
      ((coefficientSequenceDerivedEvaluation l E.carrier T n).obj N).IsGE a ∧
      ((coefficientSequenceDerivedEvaluation l E.carrier T n).obj N).IsLE b ∧
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E.carrier (n + 1))
        ((coefficientSequenceDerivedEvaluation l E.carrier T n).obj N) c d

/-- The specified reduction/limit equivalence with its actual unit and counit.
These equations specify the transport named in the hypothesis; they assume no
coefficient comparison or mate to be constructed by this lemma.
Source: Zheng, Construction 5.25 and Proposition 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure Reconstruction (E : FieldStage.{u} l) (T : Scheme.{u}) where
  calculus : CoefficientDerivedSystemCalculus l E.carrier T
  equivalence : finiteTorConstructibleIntegralCategory l E.carrier T ≌
    (sequenceProperty l E T).FullSubcategory
  reduction : equivalence.functor ⋙ (sequenceProperty l E T).ι =
    (finiteTorConstructibleIntegral l E.carrier T).ι ⋙ calculus.reduction
  limit : equivalence.inverse ⋙ (finiteTorConstructibleIntegral l E.carrier T).ι =
    (sequenceProperty l E T).ι ⋙ coefficientSequenceLimit l E.carrier T
  unit : ∀ K, HEq
    ((finiteTorConstructibleIntegral l E.carrier T).ι.map (equivalence.unit.app K))
    (calculus.adjunction.unit.app K.obj)
  counit : ∀ N, HEq ((sequenceProperty l E T).ι.map (equivalence.counit.app N))
    (calculus.adjunction.counit.app N.obj)
  evaluation (n : ℕ) : (sequenceProperty l E T).FullSubcategory ⥤
    finiteTorConstructibleCategory l E.carrier (n + 1) (Nat.succ_pos _) T
  evaluation_eq (n : ℕ) : evaluation n ⋙
      (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos _) T).ι =
    (sequenceProperty l E T).ι ⋙ coefficientSequenceDerivedEvaluation l E.carrier T n

/-- Ambient finite evaluation of the specified reconstruction.
Source: Zheng, Construction 4.1 and Proposition 5.26.
(blueprint: def-sf-exceptional-integral-scalar-transport-data). -/
def Reconstruction.evaluationRealization (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (n : ℕ) :
    (R.equivalence.functor ⋙ R.evaluation n) ⋙
        (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) T).ι ≅
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        coefficientFiniteDerivedExtension l E.carrier T n :=
  isoWhiskerLeft R.equivalence.functor (eqToIso (R.evaluation_eq n)) ≪≫
    isoWhiskerRight (eqToIso R.reduction)
      (coefficientSequenceDerivedEvaluation l E.carrier T n) ≪≫
    isoWhiskerLeft (finiteTorConstructibleIntegral l E.carrier T).ι
      (R.calculus.reductionEvaluation n)

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Scalar comparisons for the fixed proper/open adjunctions. All scalars are
conclusions, with the exact published finite and completed realizations.
Source: Zheng, Lemma 5.22 and Proposition 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure Mates {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)) where
  scalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) : Scalar.{u} l Ω a (endpoint X Y side)
  scalarShift {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) : (scalar a ha side).realization.hom.CommShift ℤ
  finiteScalar_eq {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).functor ⋙
        RingStage.inclusion.{u} l Ω (endpoint X Y side) (RingStage.finite E n) =
      RingStage.inclusion.{u} l Ω (endpoint X Y side) s ⋙
        pbcDerivedExtend (a.map (endpoint X Y side))
  finiteScalar_normalized {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).realization =
      eqToIso (finiteScalar_eq (s := s) E n a ha side)
  integralScalar_eq (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) :
    (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).functor ⋙
        RingStage.inclusion.{u} l Ω (endpoint X Y side) (RingStage.integral L) =
      RingStage.inclusion.{u} l Ω (endpoint X Y side) (RingStage.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side)
  integralScalar_normalized (E L : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i (endpoint X Y side)).app K.obj)
  comparison {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    Comparison.{u} l Ω (operation s) (operation t)
      (scalar a ha true).functor (scalar a ha false).functor
  comparison_normalized {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    QNormalized.{u} l Ω c a (scalar a ha true) (scalar a ha false)
      (left s) (left t) (comparison a ha)
  scalarComposition {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) (side : Bool) :
    ScalarComposition.{u} l Ω h (endpoint X Y side)
      (scalar a ha side) (scalar b hb side) (scalar d hd side)
  cocycle {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) :
    Cocycle.{u} l Ω (comparison a ha) (comparison b hb) (comparison d hd)
      (scalarComposition a b d h ha hb hd true).iso
      (scalarComposition a b d h ha hb hd false).iso
  scalarIdentity {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a) (side : Bool) :
    ScalarIdentity.{u} l Ω h (endpoint X Y side) (scalar a ha side)
  identityLeft {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a)
      (K : C.{u} l Ω X (s.stage l)) :
    (comparison a ha).q.hom.app K ≫
        (operation s).F.map ((scalarIdentity a h ha true).iso.hom.app K) =
      (scalarIdentity a h ha false).iso.hom.app ((operation s).F.obj K)
  identityRight {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a)
      (L : C.{u} l Ω Y (s.stage l)) :
    (comparison a ha).b.hom.app L ≫
        (operation s).G.map ((scalarIdentity a h ha false).iso.hom.app L) =
      (scalarIdentity a h ha true).iso.hom.app ((operation s).G.obj L)

  tor_interval (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) (K : C.{u} l Ω (endpoint X Y side) (.integral E)) (a b : ℤ)
      (h : ∀ n : ℕ, HasProEtaleTorAmplitude (endpoint X Y side)
        (Padic.coefficientExtensionRing l E.carrier (n + 1))
        ((scalarReductionDerivedExtension l E.carrier (endpoint X Y side) n).obj K.obj) a b) :
    ∀ n : ℕ, HasProEtaleTorAmplitude (endpoint X Y side)
      (Padic.coefficientExtensionRing l L.carrier (n + 1))
      ((scalarReductionDerivedExtension l L.carrier (endpoint X Y side) n).obj
        ((scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) side).functor.obj K).obj) a b
  completed_shift (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) :
    ∃ eC : (integralScalarComplexFunctor l E.carrier L.carrier i
        (endpoint X Y side)).CommShift ℤ,
      (∀ (P : CochainComplex (integralTowerModules l E.carrier (endpoint X Y side)) ℤ)
        (m : ℤ), completedScalarShiftConeFormula i (endpoint X Y side) eC P m) ∧
      ∀ (P : CochainComplex (integralTowerModules l E.carrier (endpoint X Y side)) ℤ)
        (m : ℤ),
        (((completedOrdinaryScalarExtension l E.carrier L.carrier i
            (endpoint X Y side)).mapCochainComplexShiftIso m).hom.app P) ≫
            ((completedScalarChainComparison l E.carrier L.carrier i
              (endpoint X Y side)).app P)⟦m⟧' =
          (completedScalarChainComparison l E.carrier L.carrier i
            (endpoint X Y side)).app (P⟦m⟧) ≫
            (Functor.commShiftIso (integralScalarComplexFunctor l E.carrier L.carrier i
              (endpoint X Y side)) (self := eC) m).hom.app P

/-- The q arrow with the scalar shift witnesses supplied from its owning record.
Source: Zheng, Lemma 5.22
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
def Mates.q {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (d : Mates l Ω c operation left) {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a) :=
  letI := (d.scalar a ha true).commShift
  letI := (d.scalar a ha false).commShift
  (d.comparison a ha).q

/-- The b arrow with the same explicitly supplied scalar shift witnesses.
Source: Zheng, Lemma 5.22
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
def Mates.b {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (d : Mates l Ω c operation left) {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a) :=
  letI := (d.scalar a ha true).commShift
  letI := (d.scalar a ha false).commShift
  (d.comparison a ha).b

/-- The fixed system adjunction and its actual reconstruction, not scalar mates.
The evaluations include both adjunction equations; the proper/open word and the
prescribed integral compact support are fixed by their named realization maps.
Source: Zheng, Lemma 5.22, Construction 5.25 and Proposition 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure Transported (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)) where
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
  support (E : FieldStage.{u} l) : F E ⋙ (sequenceProperty l E Y).ι =
    (sequenceProperty l E X).ι ⋙
      (IntegralSystemRealization.Operations.shriek l E.carrier (operations E) c.i ⋙
        IntegralSystemRealization.Operations.push l E.carrier (operations E) c.g)
  realizeF (E : FieldStage.{u} l) : (operation (.integral E)).F ≅
    PurReconstruction.realized (reconstruction E true).equivalence
      (reconstruction E false).equivalence (F E)
  realizeG (E : FieldStage.{u} l) : (operation (.integral E)).G ≅
    PurReconstruction.realized (reconstruction E false).equivalence
      (reconstruction E true).equivalence (G E)
  adjunction_eq (E : FieldStage.{u} l) : (operation (.integral E)).adjunction =
    ((PurReconstruction.realizedAdjunction (reconstruction E true).equivalence
      (reconstruction E false).equivalence (adjunction E)).ofNatIsoLeft
        (realizeF E).symm).ofNatIsoRight (realizeG E).symm
  reductionF (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ (reconstruction E false).equivalence.functor ≅
      (reconstruction E true).equivalence.functor ⋙ F E
  reductionF_eq (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    (reductionF E).hom.app K =
      (reconstruction E false).equivalence.functor.map ((realizeF E).hom.app K) ≫
        (reconstruction E false).equivalence.counit.app
          ((F E).obj ((reconstruction E true).equivalence.functor.obj K))
  reductionG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ⋙ (reconstruction E true).equivalence.functor ≅
      (reconstruction E false).equivalence.functor ⋙ G E
  reductionG_eq (E : FieldStage.{u} l) (K : C.{u} l Ω Y (.integral E)) :
    (reductionG E).hom.app K =
      (reconstruction E true).equivalence.functor.map ((realizeG E).hom.app K) ≫
        (reconstruction E true).equivalence.counit.app
          ((G E).obj ((reconstruction E false).equivalence.functor.obj K))
  evaluationF (E : FieldStage.{u} l) (n : ℕ) :
    F E ⋙ (reconstruction E false).evaluation n ≅
      (reconstruction E true).evaluation n ⋙ (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F
  evaluationG (E : FieldStage.{u} l) (n : ℕ) :
    Adjunction.CompatibleRightComparison (adjunction E)
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction (evaluationF E n)
  evaluation_unit (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E X).FullSubcategory) :
    ((reconstruction E true).evaluation n).map ((adjunction E).unit.app K) ≫
      (evaluationG E n).hom.app ((F E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
        ((evaluationF E n).hom.app K) =
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
        (((reconstruction E true).evaluation n).obj K)
  evaluation_counit (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E Y).FullSubcategory) :
    (evaluationF E n).hom.app ((G E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
        ((evaluationG E n).hom.app K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
        (((reconstruction E false).evaluation n).obj K) =
      ((reconstruction E false).evaluation n).map ((adjunction E).counit.app K)
  evaluation_support (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E X).FullSubcategory) :
    HEq ((finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).ι.map
        ((evaluationF E n).hom.app K) ≫
      (left (.finite E ⟨n + 1, Nat.succ_pos n⟩)).hom.app
        (((reconstruction E true).evaluation n).obj K) ≫
      (PurCompactSupport.finiteImageIso l E.carrier n c).hom.app
        (((reconstruction E true).evaluation n).obj K).obj ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E.carrier (n + 1)) c).map
        ((eqToIso ((reconstruction E true).evaluation_eq n)).hom.app K))
      ((IntegralSystemRealization.supportEvaluation l E.carrier (operations E) c n).hom.app K.obj)
  integralLeft (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier
  integralLeft_normalized (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    (sfIntegralConstructible l E.carrier Y).ι.map ((integralLeft E).hom.app K) =
      (left (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  /-- The canonical realization of the input and its open extension is defined
      on precisely the normalized constructible finite-Tor transport domain. -/
  inputGood (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier X
      (((reconstruction E true).equivalence.functor.obj K).obj)
  openGood (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier c.Z
      ((IntegralSystemRealization.Operations.shriek l E.carrier (operations E) c.i).obj
        (((reconstruction E true).equivalence.functor.obj K).obj))
  /-- This square fixes the integral left realization, including its sign, by the
      canonical proper conjugate, normalized open mate and reconstruction unit. -/
  integral_system_normalized (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    HEq ((finiteTorConstructibleIntegral l E.carrier Y).ι.map
        ((realizeF E).inv.app K) ≫ (left (.integral E)).hom.app K)
      (((realizations E).realizationModel.push l E.carrier c.g).hom.app
          ((IntegralSystemRealization.Operations.shriek l E.carrier (operations E) c.i).obj
            (((reconstruction E true).equivalence.functor.obj K).obj)) ≫
        (PurCompactSupport.push (PurCompactSupport.completed l E.carrier) c.g).map
          (((realizations E).openRealization c.i
              (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance)
              (((reconstruction E true).equivalence.functor.obj K).obj)
              (inputGood E K) (openGood E K)).hom ≫
            ((PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
              c.i).mapDerivedCategory).map
              ((eqToIso (congrArg
                  (fun H ↦ H.obj ((reconstruction E true).equivalence.functor.obj K))
                  (reconstruction E true).limit)).inv ≫
                (finiteTorConstructibleIntegral l E.carrier X).ι.map
                  ((reconstruction E true).equivalence.unitIso.inv.app K))))

/-- One actual ramified finite map, allowing any zero-based target index m
whose positive exponent is e(n+1). The heterogeneous equality is only the
transport across this explicit exponent equality, never an identification en=n.
Source: Zheng, Construction 4.1
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure RamifiedMap (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e) where
  n : ℕ
  m : ℕ
  exponent : m + 1 = e * (n + 1)
  change : PurCompactSupport.Change
    ((RingStage.finite E ⟨n + 1, Nat.succ_pos n⟩).coefficients l)
    ((RingStage.finite L ⟨m + 1, Nat.succ_pos m⟩).coefficients l)
  allowed : Allowed l change
  actual : ∀ T : Scheme.{u}, HEq (change.map T)
    ((PurCompactSupport.finiteChange l E.carrier L.carrier i e he e.pos
      (n + 1) (Nat.succ_pos n)).map T)

/-- Evaluation is the integral reduction comparison, including the given system
adjunction's unit and counit, with the actual reduction/limit projection counit.
Source: Zheng, Lemma 5.22 and Proposition 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure ReductionMates (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
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
    (tr : Transported l Ω D hl c operation left) (d : Mates l Ω c operation left)
    (E : FieldStage.{u} l) (n : ℕ) where
  evaluation (side : Bool) :
    (d.scalar (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) side).functor ≅
    (tr.reconstruction E side).equivalence.functor ⋙ (tr.reconstruction E side).evaluation n
  -- Keep the canonical comparison between the two derived quotient tensors explicit.
  evaluation_normalized (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n)
      (endpoint X Y side)).ι.map ((evaluation side).inv.app K) =
      ((tr.reconstruction E side).evaluationRealization l E (endpoint X Y side) n).hom.app K ≫
        (PurCompactSupport.finiteReductionIso l E.carrier (endpoint X Y side) n).inv.app K.obj ≫
        (eqToIso (d.finiteScalar_eq (s := .integral E) E ⟨n + 1, Nat.succ_pos n⟩
          (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
          (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) side)).inv.app K
  q_evaluation (K : C.{u} l Ω X (.integral E)) :
    (Mates.q l Ω d (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).hom.app K ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
        ((evaluation true).hom.app K) =
    (evaluation false).hom.app ((operation (.integral E)).F.obj K) ≫
      ((tr.reconstruction E false).evaluation n).map ((tr.reductionF E).hom.app K) ≫
      (tr.evaluationF E n).hom.app ((tr.reconstruction E true).equivalence.functor.obj K)
  b_evaluation (N : C.{u} l Ω Y (.integral E)) :
    (Mates.b l Ω d (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).hom.app N ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
        ((evaluation false).hom.app N) =
    (evaluation true).hom.app ((operation (.integral E)).G.obj N) ≫
      ((tr.reconstruction E true).evaluation n).map ((tr.reductionG E).hom.app N) ≫
      (tr.evaluationG E n).hom.app ((tr.reconstruction E false).equivalence.functor.obj N)

/-- The whole-system completed coefficient comparisons, before any total limit.
The scalar realization is the existing representative-normalized coherent counit,
so these are comparisons for the published strict-tower functor, not arbitrary maps.
Source: Zheng, Construction 4.1, Lemma 5.22 and Proposition 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates). -/
structure SystemMates (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
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
    (tr : Transported l Ω D hl c operation left) (d : Mates l Ω c operation left)
    (red : ∀ (E : FieldStage.{u} l) (n : ℕ),
      ReductionMates l Ω D hl c operation left tr d E n)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) where
  coefficient (side : Bool) : CoefficientExtensionSystems l E.carrier L.carrier i
    (endpoint X Y side)
  coefficient_model (side : Bool) : CoefficientExtensionReductionData
    l E.carrier L.carrier i (endpoint X Y side)
    (tr.reconstruction E side).calculus (tr.reconstruction L side).calculus (coefficient side)
  scalar (side : Bool) : (sequenceProperty l E (endpoint X Y side)).FullSubcategory ⥤
    (sequenceProperty l L (endpoint X Y side)).FullSubcategory
  scalar_eq (side : Bool) : scalar side ⋙ (sequenceProperty l L (endpoint X Y side)).ι =
    (sequenceProperty l E (endpoint X Y side)).ι ⋙ (coefficient side).scalar.T
  reduction (side : Bool) :
    (d.scalar (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i)
      (Allowed.integral E L i) side).functor ⋙
        (tr.reconstruction L side).equivalence.functor ≅
      (tr.reconstruction E side).equivalence.functor ⋙ scalar side
  reduction_normalized (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((sequenceProperty l L (endpoint X Y side)).ι.map ((reduction side).hom.app K))
      ((coefficientExtensionReductionIso l E.carrier L.carrier i (endpoint X Y side)
        (tr.reconstruction E side).calculus (tr.reconstruction L side).calculus
        (coefficient side) (coefficient_model side)).hom.app K.obj)
  q : tr.F E ⋙ scalar false ≅ scalar true ⋙ tr.F L
  b : tr.G E ⋙ scalar true ≅ scalar false ⋙ tr.G L
  counit (N : (sequenceProperty l E Y).FullSubcategory) :
    q.hom.app ((tr.G E).obj N) ≫ (tr.F L).map (b.hom.app N) ≫
      (tr.adjunction L).counit.app ((scalar false).obj N) =
        (scalar false).map ((tr.adjunction E).counit.app N)
  q_reduction (K : C.{u} l Ω X (.integral E)) :
    (tr.reconstruction L false).equivalence.functor.map
        ((Mates.q l Ω d (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i)).hom.app K) ≫
      (tr.reductionF L).hom.app
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) true).functor.obj K) ≫
      (tr.F L).map ((reduction true).hom.app K) =
    (reduction false).hom.app ((operation (.integral E)).F.obj K) ≫
      (scalar false).map ((tr.reductionF E).hom.app K) ≫
        q.hom.app ((tr.reconstruction E true).equivalence.functor.obj K)
  b_reduction (N : C.{u} l Ω Y (.integral E)) :
    (tr.reconstruction L true).equivalence.functor.map
        ((Mates.b l Ω d (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i)).hom.app N) ≫
      (tr.reductionG L).hom.app
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) false).functor.obj N) ≫
      (tr.G L).map ((reduction false).hom.app N) =
    (reduction true).hom.app ((operation (.integral E)).G.obj N) ≫
      (scalar true).map ((tr.reductionG E).hom.app N) ≫
        b.hom.app ((tr.reconstruction E false).equivalence.functor.obj N)

  selected (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool) :
    scalar side ⋙ (tr.reconstruction L side).evaluation z.m ≅
      (tr.reconstruction E side).evaluation z.n ⋙
        (d.scalar z.change z.allowed side).functor
  selected_square (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (T : Scheme.{u}) :
    (PurCompactSupport.completedChange l E.carrier L.carrier i).map T ≫
        (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map T =
      (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map T ≫
        z.change.map T
  selected_balanced (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
      (endpoint X Y side)).ι.map
        ((red L z.m).evaluation side |>.hom.app
            ((d.scalar (s := .integral E) (t := .integral L)
              (PurCompactSupport.completedChange l E.carrier L.carrier i)
              (Allowed.integral E L i) side).functor.obj K)) ≫
      (finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
        (endpoint X Y side)).ι.map
        (((tr.reconstruction L side).evaluation z.m).map ((reduction side).hom.app K) ≫
          (selected e he z side).hom.app
            ((tr.reconstruction E side).equivalence.functor.obj K) ≫
          (d.scalar z.change z.allowed side).functor.map
            (((red E z.n).evaluation side).inv.app K)))
      ((pbcDerivedExtend ((PurCompactSupport.reduction l L.carrier
          (z.m + 1) (Nat.succ_pos z.m)).map (endpoint X Y side))).map
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) side).realization.hom.app K) ≫
        (PurCompactSupport.tensorSquare
          ((PurCompactSupport.completedChange l E.carrier L.carrier i).map
            (endpoint X Y side)) (z.change.map (endpoint X Y side))
          ((PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map
            (endpoint X Y side))
          ((PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map
            (endpoint X Y side)) (selected_square e he z (endpoint X Y side))).hom.app K.obj)
  q_selected (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (N : (sequenceProperty l E X).FullSubcategory) :
    ((tr.reconstruction L false).evaluation z.m).map (q.hom.app N) ≫
      (tr.evaluationF L z.m).hom.app ((scalar true).obj N) ≫
      (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).F.map
        ((selected e he z true).hom.app N) =
    (selected e he z false).hom.app ((tr.F E).obj N) ≫
      (d.scalar z.change z.allowed false).functor.map
        ((tr.evaluationF E z.n).hom.app N) ≫
      (Mates.q l Ω d z.change z.allowed).hom.app
        (((tr.reconstruction E true).evaluation z.n).obj N)
  b_selected (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (N : (sequenceProperty l E Y).FullSubcategory) :
    ((tr.reconstruction L true).evaluation z.m).map (b.hom.app N) ≫
      (tr.evaluationG L z.m).hom.app ((scalar false).obj N) ≫
      (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).G.map
        ((selected e he z false).hom.app N) =
    (selected e he z true).hom.app ((tr.G E).obj N) ≫
      (d.scalar z.change z.allowed true).functor.map
        ((tr.evaluationG E z.n).hom.app N) ≫
      (Mates.b l Ω d z.change z.allowed).hom.app
        (((tr.reconstruction E false).evaluation z.n).obj N)

end WeilConjectures.ExceptionalIntegralScalar
