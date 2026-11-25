/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedRationalLeftLaws

/-! # The normalized compact-support action on finite coefficient stages -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
attribute [local irreducible] HasDerivedCategory.standard ScalarLocalization.category
  sfRationalConstructibleLocalization sfRationalTriangulationDatum sfRationalScalarExtension
  sfRationalScalarComp GeneralAlgebraicallyClosedCoefficients.scalarAssociator

private theorem transport_stage_morphism
    {I : Type*} [Preorder I] {C B : I → Type*}
    [∀ i, Category (C i)] [∀ i, Category (B i)]
    {S S' : StageSystem C} {T T' : StageSystem B}
    (hS : S = S') (hT : T = T') (F : S.Morphism T) :
    ∃ A : S'.Morphism T', (∀ i, HEq (A.Φ i) (F.Φ i)) ∧
      ∀ (i j : I) (h : i ≤ j), HEq (A.β h) (F.β h) := by
  subst S' T'
  exact ⟨F, (fun _ ↦ HEq.rfl), fun _ _ _ ↦ HEq.rfl⟩

section
variable (l : ℕ) [Fact l.Prime] (Ω : Type)
  [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  [IsAlgClosure (Padic l) (ULift.{u} Ω)]

private abbrev modelField (E : Index l Ω) : FieldStage.{u} l where
  carrier := Coefficient.{u} l Ω E

private def finiteInclusion (E L : Index l Ω) (h : E ≤ L) :
    (modelField l Ω E).carrier →ₐ[Padic l] (modelField l Ω L).carrier :=
  coefficientInclusion l Ω E L h

omit [IsAlgClosure (Padic l) Ω] in
private theorem coefficient_coherence
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction.{u, u} l (ULift.{u} Ω) D hl (f := f))
  (c : Compactification f)
    (E L M : FieldStage.{u} l)
    (i : E.carrier →ₐ[Padic l] L.carrier)
    (j : L.carrier →ₐ[Padic l] M.carrier)
    (a : E.carrier →ₐ[Padic l] M.carrier) (ha : j.comp i = a)
    (ax : sfRationalScalarExtension l E.carrier X 0
        (Fact.out : l.Prime).ne_zero L.carrier i ⋙
      sfRationalScalarExtension l L.carrier X 0
        (Fact.out : l.Prime).ne_zero M.carrier j ≅
      sfRationalScalarExtension l E.carrier X 0
        (Fact.out : l.Prime).ne_zero M.carrier a)
    (ay : sfRationalScalarExtension l E.carrier Y 0
        (Fact.out : l.Prime).ne_zero L.carrier i ⋙
      sfRationalScalarExtension l L.carrier Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j ≅
      sfRationalScalarExtension l E.carrier Y 0
        (Fact.out : l.Prime).ne_zero M.carrier a)
    (hx : HEq ax (GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
      E.carrier L.carrier M.carrier i j a ha X))
    (hy : HEq ay (GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
      E.carrier L.carrier M.carrier i j a ha Y))
    (K : sfRationalConstructibleCategory l E.carrier X) :
    (sfRationalScalarExtension l L.carrier Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j).map
        ((P.fields.rationalComparison c E L i).q.hom.app K) ≫
      (P.fields.rationalComparison c L M j).q.hom.app
        ((sfRationalScalarExtension l E.carrier X 0
          (Fact.out : l.Prime).ne_zero L.carrier i).obj K) ≫
      (P.ring.operation c (.rational M)).F.map
        (ax.hom.app K) =
      ay.hom.app
          ((P.ring.operation c (.rational E)).F.obj K) ≫
      (P.fields.rationalComparison c E M a).q.hom.app K := by
  have hx' := eq_of_heq hx
  have hy' := eq_of_heq hy
  subst ax ay
  subst a
  have hc := (normalized_rational_left_laws.{u, u}
    l (ULift.{u} Ω) D hl P.ring P.fields).1 c E L M i j K
  simpa only [GeneralAlgebraicallyClosedCoefficients.scalarAssociator,
    eqToIso_refl, Iso.trans_refl] using hc

private theorem stageAction_exists
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction.{u, u} l (ULift.{u} Ω) D hl (f := f))
  (c : Compactification f) : ∃ A :
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y),
      (∀ E : Index l Ω,
        HEq (A.Φ E) (P.ring.operation c (.rational (modelField l Ω E))).F) ∧
      (∀ (E L : Index l Ω) (h : E ≤ L),
        HEq (A.β h) ((P.fields.rationalComparison c (modelField l Ω E) (modelField l Ω L)
          (coefficientInclusion l Ω E L h)).q)) := by
  classical
  let S : StageSystem (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X) :=
    { T := fun {E L} h ↦ GeneralAlgebraicallyClosedCoefficients.transition
        l Ω X E L h
      assoc := fun {E L M} h k ↦ GeneralAlgebraicallyClosedCoefficients.associator
        l Ω X E L M h k
      cocycle := fun h k m K ↦ GeneralAlgebraicallyClosedCoefficients.associator_cocycle
        l Ω X _ _ _ _ h k m K }
  let T : StageSystem (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y) :=
    { T := fun {E L} h ↦ GeneralAlgebraicallyClosedCoefficients.transition
        l Ω Y E L h
      assoc := fun {E L M} h k ↦ GeneralAlgebraicallyClosedCoefficients.associator
        l Ω Y E L M h k
      cocycle := fun h k m K ↦ GeneralAlgebraicallyClosedCoefficients.associator_cocycle
        l Ω Y _ _ _ _ h k m K }
  have hS : S = GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X :=
    (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω X).unique
      ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩
      (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
        l Ω X).exists.choose_spec
  have hT : T = GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y :=
    (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω Y).unique
      ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩
      (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
        l Ω Y).exists.choose_spec
  let phi (E : Index l Ω) :
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E ⥤
        GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E :=
    (P.ring.operation c (.rational (modelField l Ω E))).F
  let beta {E L : Index l Ω} (h : E ≤ L) :
      phi E ⋙ T.T h ≅ S.T h ⋙ phi L := by
    dsimp only [phi, S, T, GeneralAlgebraicallyClosedCoefficients.transition]
    have q := CounitFieldComparison.q.{u, u} l (ULift.{u} Ω)
      (P.fields.rationalComparison c (modelField l Ω E) (modelField l Ω L)
        (finiteInclusion l Ω E L h))
    exact q
  let F : S.Morphism T :=
    { Φ := phi
      β := beta
      coh := by
        intro E L M h k K
        exact coefficient_coherence l Ω D hl P c
          (modelField l Ω E) (modelField l Ω L) (modelField l Ω M)
          (finiteInclusion l Ω E L h) (finiteInclusion l Ω L M k)
          (finiteInclusion l Ω E M (h.trans k))
          ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws.{u, 0}
            l Ω).2 E L M h k)
          (GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k)
          (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k)
          (GeneralAlgebraicallyClosedCoefficients.associator_existsUnique
            l Ω X E L M h k).exists.choose_spec
          (GeneralAlgebraicallyClosedCoefficients.associator_existsUnique
            l Ω Y E L M h k).exists.choose_spec K }
  obtain ⟨A, ha, hb⟩ := transport_stage_morphism hS hT F
  exact ⟨A, ha, hb⟩

end

variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

/-- Rational compact support with its prescribed scalar comparisons is a stage morphism.
Source: the coefficient construction and its rational cocycle; blueprint common-field
comparisons, step 10 of the native compact-support realization.
(blueprint: lem-sf-locally-finite-compact-support-stage-action).

Proof: at E take the rational operation of P at finiteField E, and for E ≤ L take
P.fields.rationalComparison along coefficientInclusion. Identify the transition
functors with GeneralAlgebraicallyClosedCoefficients.transition using the specification
of stageSystem. The associators are its normalized balanced-tensor associators.
The composition clause of normalized_rational_left_laws gives the stage morphism equation,
after identifying the composite coefficient inclusion with the inclusion E ≤ M.
Transport these functors and comparisons through the specified transition equalities.
This retains the exact functors and scalar comparisons as heterogeneous equalities,
including E = L. The coherence proof is a proposition, so introduces no new choices.
The auxiliary lifted closure does not change the finite coefficient fields. -/
theorem locally_finite_compact_support_stage_action :
    Nonempty (StageAction l D hl P c) := by
  obtain ⟨A, ha, hb⟩ := stageAction_exists l (PadicAlgCl l) D hl P c
  exact ⟨⟨A, ha, hb⟩⟩

end WeilConjectures.LocallyFiniteAdicCompactSupport
