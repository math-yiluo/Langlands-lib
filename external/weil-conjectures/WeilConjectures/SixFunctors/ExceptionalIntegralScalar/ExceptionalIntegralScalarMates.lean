/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMatesData

import WeilConjectures.Algebra.Homology.System.SystemSelectedAdjunctionIsos
import WeilConjectures.Algebra.Homology.System.SystemSelectedNormalization
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.RamifiedSystemRecoveryBounds
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.CategoryTheory.AdjointEquivalenceConjugation.AdjointEquivalenceConjugation
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralReductionLeftCompatibility
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarMates
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralRightScalarInvertibility
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMateCompletion
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralSystemScalarCore
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralSystemSelectedLeft

/-! # Integral scalar mates for the exceptional adjunction

Source: Zheng, Constructions 4.1 and 5.15, Lemma 5.22 and Propositions 5.24, 5.26
(blueprint: lem-sf-exceptional-integral-scalar-mates).

## Main definitions and statements

- `systemBounds`, `systemProperty`, `Recovery`: normalized ramified strict towers.
- `sequenceProperty`, `Reconstruction`, `Transported`: actual reduction/limit transport.
- `Mates`, `ReductionMates`, `SystemMates`: normalized scalar comparisons and equations.
- `exceptionalIntegralScalarMates`, `ramifiedRecovery`: the two clauses of the node.
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

variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section
universe a b x y av bv xv yv
open CategoryTheory CategoryTheory.Functor
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  (eX : A ≌ X) (eY : B ≌ Y) {F : X ⥤ Y} {G : Y ⥤ X} (adj : F ⊣ G)
  {F₀ : A ⥤ B} {G₀ : B ⥤ A}
  (rF : F₀ ≅ eX.functor ⋙ F ⋙ eY.inverse)
  (rG : G₀ ≅ eY.functor ⋙ G ⋙ eX.inverse)

private theorem conjugatedCounit (N : B) :
    (eY.functor.map (rF.hom.app (G₀.obj N)) ≫
      eY.counit.app (F.obj (eX.functor.obj (G₀.obj N)))) ≫
      F.map (eX.functor.map (rG.hom.app N) ≫
        eX.counit.app (G.obj (eY.functor.obj N))) ≫
      adj.counit.app (eY.functor.obj N) =
    eY.functor.map
      (((((eX.toAdjunction.comp adj).comp eY.symm.toAdjunction).ofNatIsoLeft
        rF.symm).ofNatIsoRight rG.symm).counit.app N) := by
  simp only [Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Iso.symm_inv,
    AdjointEquivalenceConjugation.conjugation_counit, Functor.map_comp,
    Equivalence.counit, Equivalence.symm_inverse]
  have hr := rF.hom.naturality (rG.hom.app N)
  dsimp only [Functor.comp_map] at hr
  have hc (Z : Y) (k : Z ⟶ eY.functor.obj N) :
      eY.functor.map (eY.inverse.map k) ≫ eY.functor.map (eY.unitIso.inv.app N) =
        eY.counit.app Z ≫ k := by
    rw [← eY.counit_app_functor N]
    exact eY.counit_naturality k
  symm
  calc
    _ = eY.functor.map (rF.hom.app (G₀.obj N)) ≫
        eY.functor.map (eY.inverse.map
          (F.map (eX.functor.map (rG.hom.app N)) ≫
            F.map (eX.counit.app (G.obj (eY.functor.obj N))) ≫
              adj.counit.app (eY.functor.obj N))) ≫
        eY.functor.map (eY.unitIso.inv.app N) := by
      simpa only [Functor.map_comp, Category.assoc, Functor.comp_map] using
        congrArg (fun k ↦ eY.functor.map k ≫
          eY.functor.map (eY.inverse.map
            (F.map (eX.counit.app (G.obj (eY.functor.obj N))))) ≫
          eY.functor.map (eY.inverse.map (adj.counit.app (eY.functor.obj N))) ≫
          eY.functor.map (eY.unitIso.inv.app N)) hr
    _ = _ := by rw [hc]; simp only [Category.assoc]

end

section
universe a b x y av bv xv yv
open CategoryTheory CategoryTheory.Functor
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
  {F' : X ⥤ Y} {G' : Y ⥤ X} (adj' : F' ⊣ G')
  {TX U : A ⥤ X} {TY V : B ⥤ Y}
  (q₀ : F ⋙ TY ≅ TX ⋙ F') (b₀ : G ⋙ TX ⟶ TY ⋙ G')
  (q₁ : F ⋙ V ≅ U ⋙ F') (b₁ : G ⋙ U ⟶ V ⋙ G')
  (eX : TX ≅ U) (eY : TY ≅ V)
  (h₀ : ∀ N, q₀.hom.app (G.obj N) ≫ F'.map (b₀.app N) ≫
    adj'.counit.app (TY.obj N) = TY.map (adj.counit.app N))
  (h₁ : ∀ N, q₁.hom.app (G.obj N) ≫ F'.map (b₁.app N) ≫
    adj'.counit.app (V.obj N) = V.map (adj.counit.app N))
  (hq : ∀ K, q₀.hom.app K ≫ F'.map (eX.hom.app K) =
    eY.hom.app (F.obj K) ≫ q₁.hom.app K)

include adj adj' h₀ h₁ hq in
private theorem scalarMateIntertwines (N : B) :
    b₀.app N ≫ G'.map (eY.hom.app N) = eX.hom.app (G.obj N) ≫ b₁.app N := by
  apply ((adj'.homEquiv _ _).symm).injective
  change F'.map _ ≫ _ = F'.map _ ≫ _
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi (q₀.hom.app (G.obj N))).mp
  have hε := adj'.counit.naturality (eY.hom.app N)
  dsimp only [Functor.comp_map, Functor.id_map] at hε
  calc
    _ = q₀.hom.app (G.obj N) ≫ F'.map (b₀.app N) ≫
        adj'.counit.app (TY.obj N) ≫ eY.hom.app N := by rw [hε]
    _ = TY.map (adj.counit.app N) ≫ eY.hom.app N := by
      simpa only [Category.assoc] using congrArg (· ≫ eY.hom.app N) (h₀ N)
    _ = eY.hom.app (F.obj (G.obj N)) ≫ V.map (adj.counit.app N) :=
      eY.hom.naturality (adj.counit.app N)
    _ = eY.hom.app (F.obj (G.obj N)) ≫ q₁.hom.app (G.obj N) ≫
        F'.map (b₁.app N) ≫ adj'.counit.app (V.obj N) := by rw [h₁]
    _ = _ := by rw [← Category.assoc, ← hq]; simp only [Category.assoc]

end

section
universe a b x y p q av bv xv yv pv qv
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
  {P : Type p} [Category.{pv} P] {Q : Type q} [Category.{qv} Q]
  {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
  {F' : X ⥤ Y} {G' : Y ⥤ X} (adj' : F' ⊣ G')
  {F'' : P ⥤ Q} {G'' : Q ⥤ P} (adj'' : F'' ⊣ G'')
  {TX : A ⥤ X} {TY : B ⥤ Y} {VX : X ⥤ P} {VY : Y ⥤ Q}
  (q₁ : F ⋙ TY ≅ TX ⋙ F') (b₁ : G ⋙ TX ⟶ TY ⋙ G')
  (q₂ : F' ⋙ VY ≅ VX ⋙ F'') (b₂ : G' ⋙ VX ⟶ VY ⋙ G'')
  (h₁ : ∀ N, q₁.hom.app (G.obj N) ≫ F'.map (b₁.app N) ≫
    adj'.counit.app (TY.obj N) = TY.map (adj.counit.app N))
  (h₂ : ∀ N, q₂.hom.app (G'.obj N) ≫ F''.map (b₂.app N) ≫
    adj''.counit.app (VY.obj N) = VY.map (adj'.counit.app N))
include h₁ h₂ in
private theorem pasteCounit (N : B) :
    VY.map (q₁.hom.app (G.obj N)) ≫ q₂.hom.app (TX.obj (G.obj N)) ≫
      F''.map (VX.map (b₁.app N) ≫ b₂.app (TY.obj N)) ≫
      adj''.counit.app (VY.obj (TY.obj N)) =
      VY.map (TY.map (adj.counit.app N)) := by
  simp only [Functor.map_comp, Category.assoc]
  have hn := q₂.hom.naturality (b₁.app N)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [h₂ (TY.obj N)]
  rw [← VY.map_comp_assoc, ← VY.map_comp, Category.assoc, h₁]
end

/-- Construction of the mate data used by the integral scalar comparison.  This is the
first strictly smaller part of the construction; the remaining reduction maps are
recorded separately below because they require the same chosen mate.
Source: Zheng, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-mates).
The finite scalar constructions are transported through the specified reconstruction,
and the completed scalar comparison supplies the integral component.  The resulting
record contains the fixed scalar functors, their realizations, and all mate equations.
-/
theorem exceptionalIntegralScalarMates_data_mates
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
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
    (transport : Transported l Ω D hl c operation left) :
    Nonempty (Mates l Ω c operation left) := by
  obtain ⟨z⟩ := exceptionalIntegralLeftScalarMates l Ω D hl c operation left transport
  exact exceptionalIntegralScalarMateCompletion l Ω z
    (exceptionalIntegralRightScalarInvertibility l Ω D hl c operation left transport z)

private theorem reductionCounit
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
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
    (transport : Transported l Ω D hl c operation left)
    (E : FieldStage.{u} l) (N : C.{u} l Ω Y (.integral E)) :
    (transport.reductionF E).hom.app ((operation (.integral E)).G.obj N) ≫
      (transport.F E).map ((transport.reductionG E).hom.app N) ≫
      (transport.adjunction E).counit.app
        ((transport.reconstruction E false).equivalence.functor.obj N) =
      (transport.reconstruction E false).equivalence.functor.map
        ((operation (.integral E)).adjunction.counit.app N) := by
  rw [transport.reductionF_eq, transport.reductionG_eq, transport.adjunction_eq]
  exact conjugatedCounit (transport.reconstruction E true).equivalence
    (transport.reconstruction E false).equivalence (transport.adjunction E)
    (transport.realizeF E) (transport.realizeG E) N

/-! The pointwise reduction construction is the remaining independent part of the
    reduction-data theorem.  Isolating one coefficient stage and one level keeps the
    unresolved construction strictly below the quantified assertion above it.
    Source: Zheng, Lemma 5.22 and Proposition 5.26.
    (blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction-pointwise).
    The finite-level adjunction units and counits are transported through the chosen
    reconstruction, and their normalized evaluation equations give the four fields of
    `ReductionMates` for this fixed `E` and `n`. -/
theorem exceptionalIntegralScalarMates_data_reduction_pointwise
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
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
    (transport : Transported l Ω D hl c operation left)
    (d : Mates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ) :
    Nonempty (ReductionMates l Ω D hl c operation left transport d E n) := by
  let ex := (transport.reconstruction E true).equivalence.functor
  let ey := (transport.reconstruction E false).equivalence.functor
  let vx := (transport.reconstruction E true).evaluation n
  let vy := (transport.reconstruction E false).evaluation n
  let ev (side : Bool) := integralReductionEvaluation l Ω d E n side
    (transport.reconstruction E side)
  let q := isoWhiskerRight (transport.reductionF E) vy ≪≫
    isoWhiskerLeft ex (transport.evaluationF E n)
  let b := whiskerRight (transport.reductionG E).hom vx ≫
    whiskerLeft ey (transport.evaluationG E n).hom
  have hq := integralReductionLeftCompatibility l Ω D hl c operation left transport d E n
  have hc (N : C.{u} l Ω Y (.integral E)) :
      q.hom.app ((operation (.integral E)).G.obj N) ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map (b.app N) ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
          ((ey ⋙ vy).obj N) = (ey ⋙ vy).map
            ((operation (.integral E)).adjunction.counit.app N) := by
    dsimp only [q, b, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Functor.comp_obj,
      Functor.comp_map]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (transport.evaluationF E n).hom.naturality
      ((transport.reductionG E).hom.app N)
    dsimp only [Functor.comp_map] at hn
    calc
      _ = vy.map ((transport.reductionF E).hom.app
            ((operation (.integral E)).G.obj N)) ≫
          vy.map ((transport.F E).map ((transport.reductionG E).hom.app N)) ≫
          (transport.evaluationF E n).hom.app ((transport.G E).obj (ey.obj N)) ≫
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
            ((transport.evaluationG E n).hom.app (ey.obj N)) ≫
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
            (vy.obj (ey.obj N)) := by
        simpa only [ex, ey, vx, vy, Functor.comp_obj, Category.assoc] using
          congrArg (fun k ↦ vy.map ((transport.reductionF E).hom.app
            ((operation (.integral E)).G.obj N)) ≫ k ≫
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
            ((transport.evaluationG E n).hom.app (ey.obj N)) ≫
          (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
            (vy.obj (ey.obj N))) hn.symm
      _ = vy.map ((transport.reductionF E).hom.app
            ((operation (.integral E)).G.obj N)) ≫
          vy.map ((transport.F E).map ((transport.reductionG E).hom.app N)) ≫
          vy.map ((transport.adjunction E).counit.app (ey.obj N)) := by
        rw [transport.evaluation_counit]
      _ = _ := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg vy.map (reductionCounit l Ω D hl c operation left transport E N)
  refine ⟨{
    evaluation := ev
    evaluation_normalized := fun side K ↦
      integralReductionEvaluation_normalized l Ω d E n side
        (transport.reconstruction E side) K
    q_evaluation := hq
    b_evaluation := ?_ }⟩
  intro N
  let := (d.scalar (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
    (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
    (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) true).commShift
  let := (d.scalar (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
    (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
    (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) false).commShift
  exact scalarMateIntertwines (operation (.integral E)).adjunction
    (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction
    (U := ex ⋙ vx) (V := ey ⋙ vy)
    (Mates.q l Ω d _ (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩))
    (Mates.b l Ω d _ (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).hom q b
    (ev true) (ev false)
    (d.comparison (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).counit hc hq N

/-
The reduction part is a separate strictly smaller assertion: once the scalar mate
record is fixed, it supplies the reduction comparison at every finite level.
Source: Zheng, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-scalar-mates-data-reduction).
The system evaluation and counit maps are obtained by applying the actual finite
scalar maps to the reconstruction unit and counit; their equations are the transported
adjunction equations.  The statement is parameterized by the chosen mate record.
-/
theorem exceptionalIntegralScalarMates_data_reduction
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
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
    (transport : Transported l Ω D hl c operation left)
    (d : Mates l Ω c operation left) :
    Nonempty (∀ (E : FieldStage.{u} l) (n : ℕ),
      ReductionMates l Ω D hl c operation left transport d E n) := by
  classical
  exact ⟨fun E n =>
    Classical.choice (exceptionalIntegralScalarMates_data_reduction_pointwise
      l Ω D hl c operation left transport d E n)⟩

/-- Construction of the mate and finite-reduction data used by the integral scalar comparison.
Source: Zheng, Lemma 5.22 and Proposition 5.26; the finite reduction and completed scalar
transport steps of the exceptional coefficient construction.
(blueprint: lem-sf-exceptional-integral-scalar-mates-data).
The proof constructs the finite scalar maps from the ordinary etale adjunction, transports them
through the reduction/limit reconstruction, and assembles the integral scalar functor using the
published completed scalar comparison. The counit transpose and all shift witnesses are retained.
-/
theorem exceptionalIntegralScalarMates_data
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
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
    (transport : Transported l Ω D hl c operation left) :
    ∃ d : Mates l Ω c operation left,
      ∃ red : ∀ (E : FieldStage.{u} l) (n : ℕ),
        ReductionMates l Ω D hl c operation left transport d E n, True := by
  obtain ⟨d⟩ := exceptionalIntegralScalarMates_data_mates l Ω D hl c operation left transport
  obtain ⟨red⟩ := exceptionalIntegralScalarMates_data_reduction
    l Ω D hl c operation left transport d
  exact ⟨d, red, trivial⟩

/-- Construction of the whole-system scalar mate from the integral mate data.
Source: Zheng, Construction 4.1, Lemma 5.22 and Proposition 5.26; the cofinal ramified
subsequence, finite-free comparison, and normalized system transport steps.
(blueprint: lem-sf-exceptional-integral-scalar-mates-system).
The proof transports finite-level mates along the normalized subsequence equivalence, uses the
completed scalar comparison to identify the chosen integral functor, and conjugates the system
counit equation through reconstruction. Balanced associativity supplies transitions and shifts.
-/
theorem exceptionalIntegralScalarMates_system
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
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
    (transport : Transported l Ω D hl c operation left)
    (d : Mates l Ω c operation left)
    (red : ∀ (E : FieldStage.{u} l) (n : ℕ),
      ReductionMates l Ω D hl c operation left transport d E n)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    Nonempty (SystemMates l Ω D hl c operation left transport d red E L i) := by
  obtain ⟨core⟩ := exceptionalIntegralSystemScalarCore
    l Ω D hl c operation left transport d E L i
  obtain ⟨sel⟩ := exceptionalIntegralSystemSelectedLeft
    l Ω D hl c operation left transport d red E L i core
  refine ⟨{ coefficient := core.coefficient, coefficient_model := core.coefficient_model
            scalar := core.scalar, scalar_eq := core.scalar_eq
            reduction := core.reduction, reduction_normalized := core.reduction_normalized
            q := core.q, b := core.b, counit := core.counit
            q_reduction := core.q_reduction, b_reduction := core.b_reduction
            selected := sel.selected, selected_square := sel.selected_square
            selected_balanced := sel.selected_balanced, q_selected := sel.q_selected
            b_selected := ?_ }⟩
  intro e he z N
  let := (d.scalar z.change z.allowed true).commShift
  let := (d.scalar z.change z.allowed false).commShift
  let TX := (transport.reconstruction E true).evaluation z.n
  let TY := (transport.reconstruction E false).evaluation z.n
  let VX := (transport.reconstruction L true).evaluation z.m
  let VY := (transport.reconstruction L false).evaluation z.m
  let SX := (d.scalar z.change z.allowed true).functor
  let SY := (d.scalar z.change z.allowed false).functor
  let q₀ := isoWhiskerRight core.q VY ≪≫
    isoWhiskerLeft (core.scalar true) (transport.evaluationF L z.m)
  let b₀ := whiskerRight core.b.hom VX ≫
    whiskerLeft (core.scalar false) (transport.evaluationG L z.m).hom
  let q₁ := isoWhiskerRight (transport.evaluationF E z.n) SY ≪≫
    isoWhiskerLeft TX (Mates.q l Ω d z.change z.allowed)
  let b₁ := whiskerRight (transport.evaluationG E z.n).hom SX ≫
    whiskerLeft TY (Mates.b l Ω d z.change z.allowed).hom
  have h₀ := pasteCounit (transport.adjunction E) (transport.adjunction L)
    (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).adjunction
    core.q core.b.hom (transport.evaluationF L z.m) (transport.evaluationG L z.m).hom
    core.counit (transport.evaluation_counit L z.m)
  have h₁ := pasteCounit (transport.adjunction E)
    (operation (.finite E ⟨z.n + 1, Nat.succ_pos z.n⟩)).adjunction
    (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).adjunction
    (transport.evaluationF E z.n) (transport.evaluationG E z.n).hom
    (Mates.q l Ω d z.change z.allowed) (Mates.b l Ω d z.change z.allowed).hom
    (transport.evaluation_counit E z.n) (d.comparison z.change z.allowed).counit
  have hr := scalarMateIntertwines (transport.adjunction E)
    (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).adjunction
    (TX := core.scalar true ⋙ VX) (TY := core.scalar false ⋙ VY)
    (U := (transport.reconstruction E true).evaluation z.n ⋙ SX)
    (V := (transport.reconstruction E false).evaluation z.n ⋙ SY)
    q₀ b₀ q₁ b₁ (sel.selected e he z true) (sel.selected e he z false)
    (by
      intro N
      simpa only [q₀, b₀, VX, VY, Functor.comp_map, Functor.comp_obj, Iso.trans_hom,
        NatTrans.comp_app, isoWhiskerRight_hom,
        isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Category.assoc] using h₀ N)
    (by
      intro N
      simpa only [q₁, b₁, TX, TY, SX, SY, Functor.comp_map, Functor.comp_obj,
        Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
        isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Category.assoc] using h₁ N)
    (by
      intro K
      simpa only [q₀, q₁, TX, TY, SX, SY, VX, VY, Functor.comp_map,
        Functor.comp_obj, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
        isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Category.assoc] using
        sel.q_selected e he z K) N
  simpa only [b₀, b₁, TX, TY, SX, SY, VX, VY, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Functor.map_comp,
    Functor.comp_map, Functor.comp_obj, Category.assoc] using hr

/-- Core integral scalar mate data before the arithmetic ramified-index witness.
Source: Zheng, Lemma 5.22 and Proposition 5.26. The proof follows the parent's
system transport, finite reduction, completed scalar comparison, reconstruction,
realization, and shift-coherence steps, omitting only the final explicit index choice.
(blueprint: lem-sf-exceptional-integral-scalar-mates-core). -/
theorem exceptionalIntegralScalarMates_core
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
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
    (transport : Transported l Ω D hl c operation left) :
    ∃ d : Mates l Ω c operation left,
      ∃ red : ∀ (E : FieldStage.{u} l) (n : ℕ),
        ReductionMates l Ω D hl c operation left transport d E n,
      ∀ (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier),
        Nonempty (SystemMates l Ω D hl c operation left transport d red E L i) := by
  obtain ⟨d, red, _⟩ := exceptionalIntegralScalarMates_data l Ω D hl c operation left transport
  refine ⟨d, red, ?_⟩
  intro E L i
  exact exceptionalIntegralScalarMates_system l Ω D hl c operation left transport d red E L i

end WeilConjectures.ExceptionalIntegralScalar
