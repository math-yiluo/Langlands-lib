/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMates
import WeilConjectures.SixFunctors.Exceptional.ExceptionalFiniteOperations
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.ExceptionalIntegralSupportAdjoint
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Finite and integral operation families for exceptional transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

@[instance_reducible]
private def ringOperationsCompShift {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] (F : A ⥤ B) (G : B ⥤ C)
    (sF : F.CommShift ℤ) (sG : G.CommShift ℤ) : (F ⋙ G).CommShift ℤ := by
  letI := sF
  letI := sG
  infer_instance

private theorem ringOperationsCompExact {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B] [Limits.HasZeroObject C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated A] [Pretriangulated B] [Pretriangulated C]
    (F : A ⥤ B) (G : B ⥤ C) (sF : F.CommShift ℤ) (sG : G.CommShift ℤ)
    (hF : letI := sF; F.IsTriangulated) (hG : letI := sG; G.IsTriangulated) :
    letI := sF
    letI := sG
    letI := ringOperationsCompShift F G sF sG
    (F ⋙ G).IsTriangulated := by
  let := sF
  let := sG
  let := hF
  let := hG
  infer_instance

set_option linter.unusedVariables false in
/-- Finite and integral exceptional operation families with their compact-support
left realizations exist for every compactification. This is the operation and
realization subargument of the coherent transport construction.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-operations-existence).

Proof: at a finite stage use the existing finite exceptional operations and
identify their literal compact-support realization with the published finite image.
At an integral stage use preservation and right-adjoint existence for the literal
compact-support restriction. Its full faithful ambient inclusion gives the left
shift and exactness; the adjunction gives right additivity, right shifts, exactness,
and shift-compatible unit and counit. Choose these already proved stagewise
existence witnesses and assemble by cases on RingStage. Positive levels are n+1,
and the existing constructors include empty schemes. No scalar comparison is used.
-/
theorem exists_exceptional_ring_operations
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l),
      ∃ left : ∀ s : RingStage.{u} l,
        LeftRealization.{u} l Ω c s (operation s), True := by
  classical
  have finite (E : FieldStage.{u} l) (n : ℕ+) :
      ∃ A : Operation.{u} l Ω X Y (.finite E n),
        Nonempty (LeftRealization.{u} l Ω c (.finite E n) A) := by
    obtain ⟨n, hn⟩ := n
    cases n with
    | zero => omega
    | succ m =>
      let n : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
      change ∃ A : Operation.{u} l Ω X Y (.finite E n), _
      obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (c.g ≫ (Y ↘ Spec (.of D.k)))
      obtain ⟨_, _, h⟩ := exists_sfFiniteExceptionalOperations D l hl f c d hd
      obtain ⟨F, G, eF, _, hFa, hGa, sF, sG, adj, hFt, hGt, hu, hc, _⟩ := h E n
      let := hFa
      let := hGa
      let := sF
      let := sG
      refine ⟨{
        F := F
        G := G
        adjunction := adj
        leftExact := hFt
        rightExact := hGt
        unitShift := hu
        counitShift := hc }, ⟨?_⟩⟩
      refine eqToIso eF ≪≫ Functor.isoWhiskerLeft _ ?_
      have e := (PurCompactSupport.finiteImageIso l E.carrier m c).symm
      dsimp only [n, proEtaleDerivedCategory, PurCompactSupport.finite,
        proEtaleRingModules_hasDerivedCategory, sfAmbientCompactSupportCandidate,
        sfIntrinsicCompactSupport] at e ⊢
      exact e
  have integral (E : FieldStage.{u} l) :
      ∃ A : Operation.{u} l Ω X Y (.integral E),
        Nonempty (LeftRealization.{u} l Ω c (.integral E) A) := by
    classical
    have := integralTriangulated l E X
    have := integralTriangulated l E Y
    let := ExceptionalIntegralScalar.inclusionShift.{u} l Ω X (.integral E)
    let := ExceptionalIntegralScalar.inclusionShift.{u} l Ω Y (.integral E)
    let : (RingStage.inclusion.{u} l Ω X (.integral E)).IsTriangulated :=
      ⟨fun _ hT ↦ hT⟩
    let : (RingStage.inclusion.{u} l Ω Y (.integral E)).Full :=
      (finiteTorConstructibleIntegral l E.carrier Y).fullyFaithfulι.full
    let : (RingStage.inclusion.{u} l Ω Y (.integral E)).Faithful :=
      (finiteTorConstructibleIntegral l E.carrier Y).fullyFaithfulι.faithful
    let : (RingStage.inclusion.{u} l Ω Y (.integral E)).IsTriangulated :=
      ⟨fun _ hT ↦ hT⟩
    let := PurCompactSupport.imageCommShift (PurCompactSupport.completed l E.carrier) c
    obtain ⟨hpres, hadj⟩ := exists_integral_support_adjoint l D hl f c E
    let F : C.{u} l Ω X (.integral E) ⥤ C.{u} l Ω Y (.integral E) :=
      (finiteTorConstructibleIntegral l E.carrier Y).lift
      (RingStage.inclusion.{u} l Ω X (.integral E) ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c) hpres
    let : F.IsLeftAdjoint := hadj
    let G := F.rightAdjoint
    let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
    let r : F ⋙ RingStage.inclusion.{u} l Ω Y (.integral E) ≅
        RingStage.inclusion.{u} l Ω X (.integral E) ⋙
          PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c :=
      (finiteTorConstructibleIntegral l E.carrier Y).liftCompιIso
      (RingStage.inclusion.{u} l Ω X (.integral E) ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c) hpres
    let : (RingStage.inclusion.{u} l Ω X (.integral E) ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).CommShift ℤ := by
      exact ringOperationsCompShift _ _
        (ExceptionalIntegralScalar.inclusionShift.{u} l Ω X (.integral E))
        (PurCompactSupport.imageCommShift (PurCompactSupport.completed l E.carrier) c)
    let : F.CommShift ℤ := Functor.CommShift.ofComp r ℤ
    let : r.hom.CommShift ℤ := Functor.CommShift.ofComp_compatibility r ℤ
    have ht : (RingStage.inclusion.{u} l Ω X (.integral E) ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).IsTriangulated := by
      have hj :
          (PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).IsTriangulated := by
        dsimp only [PurCompactSupport.image]
        infer_instance
      exact ringOperationsCompExact _ _
        (ExceptionalIntegralScalar.inclusionShift.{u} l Ω X (.integral E))
        (PurCompactSupport.imageCommShift (PurCompactSupport.completed l E.carrier) c)
        inferInstance hj
    let : F.IsTriangulated := (Functor.isTriangulated_iff_comp_right r).mpr ht
    let := adj.rightAdjointCommShift ℤ
    let := adj.commShift_of_leftAdjoint ℤ
    let := adj.right_adjoint_additive
    exact ⟨{
      F := F
      G := G
      adjunction := adj
      leftExact := inferInstance
      rightExact := adj.isTriangulated_rightAdjoint
      unitShift := inferInstance
      counitShift := inferInstance }, ⟨r⟩⟩
  have stage (s : RingStage.{u} l) :
      ∃ A : Operation.{u} l Ω X Y (s.stage l),
        Nonempty (LeftRealization.{u} l Ω c s A) := by
    cases s with
    | finite E n => exact finite E n
    | integral E => exact integral E
  choose operation realization using stage
  exact ⟨operation, fun s ↦ Classical.choice (realization s), trivial⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
