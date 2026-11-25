/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.RingStageAssembly.ExceptionalRingStageAssemblyData

import Mathlib.CategoryTheory.Triangulated.Subcategory

import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import WeilConjectures.SixFunctors.Exceptional.ExceptionalFiniteOperations
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.ExceptionalRingScalarMates
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.ExceptionalIntegralSupportAdjoint

/-! # Ring stages before localization in exceptional coefficient assembly

This partial datum contains only finite and integral stages. Field-stage operations,
localization comparisons and common-field comparisons are constructed separately.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
  AlgebraicGeometry.Scheme.completedAdicChange AlgebraicGeometry.Scheme.reductionChange
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.presheafToSheaf
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

attribute [local instance] constructionInclusionShift

private def ringFullyFaithful (T : Scheme.{max u v}) (s : RingStage.{max u v} l) :
    (RingStage.inclusion.{u, v} l Ω T s).FullyFaithful :=
  match s with
  | .finite E n => (finiteTorConstructible l E.carrier n n.pos T).fullyFaithfulι
  | .integral E => (finiteTorConstructibleIntegral l E.carrier T).fullyFaithfulι

@[instance_reducible]
private def compShift {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] (F : A ⥤ B) (G : B ⥤ C)
    (sF : F.CommShift ℤ) (sG : G.CommShift ℤ) : (F ⋙ G).CommShift ℤ := by
  letI := sF
  letI := sG
  infer_instance

private theorem compExact {A B C : Type*} [Category* A] [Category* B] [Category* C]
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
    letI := compShift F G sF sG
    (F ⋙ G).IsTriangulated := by
  letI := sF
  letI := sG
  letI := hF
  letI := hG
  infer_instance

private theorem finiteOperation (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (E : FieldStage.{max u v} l) (n : ℕ+) :
    ∃ A : Operation.{u, v} l Ω X Y (.finite E n),
      ∃ r : LeftRealization.{u, v} l Ω c (.finite E n) A,
        Nonempty (A.G ⋙ RingStage.inclusion.{u, v} l Ω X (.finite E n) ≅
          RingStage.inclusion.{u, v} l Ω Y (.finite E n) ⋙
            ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E.carrier n) c) ∧
        (letI := A.leftShift
         letI := constructionInclusionShift.{u, v} l Ω X (.finite E n)
         letI := constructionInclusionShift.{u, v} l Ω Y (.finite E n)
         r.hom.CommShift ℤ) := by
  classical
  obtain ⟨n, hn⟩ := n
  cases n with
  | zero => omega
  | succ m =>
    let n : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    change ∃ A : Operation.{u, v} l Ω X Y (.finite E n), _
    letI : (finiteTorConstructible l E.carrier n n.pos X).IsTriangulated :=
      finiteTriangulated l E n X
    letI : (finiteTorConstructible l E.carrier n n.pos Y).IsTriangulated :=
      finiteTriangulated l E n Y
    letI := constructionInclusionShift.{u, v} l Ω X (.finite E n)
    letI := constructionInclusionShift.{u, v} l Ω Y (.finite E n)
    letI : (RingStage.inclusion.{u, v} l Ω X (.finite E n)).Full :=
      (ringFullyFaithful.{u, v} l Ω X (.finite E n)).full
    letI : (RingStage.inclusion.{u, v} l Ω X (.finite E n)).Faithful :=
      (ringFullyFaithful.{u, v} l Ω X (.finite E n)).faithful
    letI : (RingStage.inclusion.{u, v} l Ω X (.finite E n)).IsTriangulated :=
      ⟨fun _ hT ↦ hT⟩
    letI : (RingStage.inclusion.{u, v} l Ω Y (.finite E n)).Full :=
      (ringFullyFaithful.{u, v} l Ω Y (.finite E n)).full
    letI : (RingStage.inclusion.{u, v} l Ω Y (.finite E n)).Faithful :=
      (ringFullyFaithful.{u, v} l Ω Y (.finite E n)).faithful
    letI : (RingStage.inclusion.{u, v} l Ω Y (.finite E n)).IsTriangulated :=
      ⟨fun _ hT ↦ hT⟩
    letI := PurCompactSupport.imageCommShift
      (PurCompactSupport.finite l E.carrier n n.pos) c
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (c.g ≫ (Y ↘ Spec (.of D.k)))
    obtain ⟨_, _, h⟩ := exists_sfFiniteExceptionalOperations D l hl f c d hd
    obtain ⟨F₀, G₀, eF, eG, hFadd, _, _, _, adj₀, _⟩ := h E n
    let F : C.{u, v} l Ω X (.finite E n) ⥤ C.{u, v} l Ω Y (.finite E n) := F₀
    let G : C.{u, v} l Ω Y (.finite E n) ⥤ C.{u, v} l Ω X (.finite E n) := G₀
    let adj : F ⊣ G := adj₀
    letI : F.Additive := hFadd
    let r : F ⋙ RingStage.inclusion.{u, v} l Ω Y (.finite E n) ≅
        RingStage.inclusion.{u, v} l Ω X (.finite E n) ⋙
          PurCompactSupport.image (PurCompactSupport.finite l E.carrier n n.pos) c :=
      eqToIso eF ≪≫ Functor.isoWhiskerLeft _
        (by
          have e := (PurCompactSupport.finiteImageIso l E.carrier m c).symm
          dsimp only [n, proEtaleDerivedCategory, PurCompactSupport.finite,
            proEtaleRingModules_hasDerivedCategory, sfAmbientCompactSupportCandidate,
            sfIntrinsicCompactSupport] at e ⊢
          exact e)
    letI : (RingStage.inclusion.{u, v} l Ω X (.finite E n) ⋙
        PurCompactSupport.image (PurCompactSupport.finite l E.carrier n n.pos) c).CommShift ℤ := by
      exact compShift _ _ (constructionInclusionShift.{u, v} l Ω X (.finite E n))
        (PurCompactSupport.imageCommShift (PurCompactSupport.finite l E.carrier n n.pos) c)
    letI : F.CommShift ℤ := Functor.CommShift.ofComp r ℤ
    letI : r.hom.CommShift ℤ := Functor.CommShift.ofComp_compatibility r ℤ
    have ht : (RingStage.inclusion.{u, v} l Ω X (.finite E n) ⋙
        PurCompactSupport.image (PurCompactSupport.finite l E.carrier n n.pos) c).IsTriangulated :=
      by
        have hj : (PurCompactSupport.image
            (PurCompactSupport.finite l E.carrier n n.pos) c).IsTriangulated := by
          dsimp only [PurCompactSupport.image]
          infer_instance
        exact compExact _ _ (constructionInclusionShift.{u, v} l Ω X (.finite E n))
          (PurCompactSupport.imageCommShift (PurCompactSupport.finite l E.carrier n n.pos) c)
          inferInstance hj
    letI : F.IsTriangulated := (Functor.isTriangulated_iff_comp_right r).mpr ht
    letI := adj.rightAdjointCommShift ℤ
    letI := adj.commShift_of_leftAdjoint ℤ
    letI := adj.right_adjoint_additive
    refine ⟨{
      F := F
      G := G
      adjunction := adj
      leftExact := inferInstance
      rightExact := adj.isTriangulated_rightAdjoint
      unitShift := inferInstance
      counitShift := inferInstance }, r, ?_, inferInstance⟩
    letI := c.hasCompactification
    let Λ := ULift.{max u v + 1} (Padic.coefficientExtensionRing l E.carrier n)
    let rc :
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat Λ) c).rightAdjoint ≅
          Etale.rightDerivedUpperShriek Λ f :=
      ((Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat Λ) c)).ofNatIsoLeft
        (Etale.rightDerivedLowerShriekIso Λ c)).rightAdjointUniq
          (Etale.rightDerivedUpperShriekAdjunction Λ f)
    let er : sfFiniteOperationsIntrinsicRight l E n c ≅
        ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E.carrier n) c :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft
          (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E.carrier n)).inverse
          (Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft
              (ProEtale.comparisonLowerStar (ModuleCat Λ) Y).rightDerivedFunctor rc)
            (ProEtale.comparisonUpperStar (ModuleCat Λ) X).mapDerivedCategory))
        (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E.carrier n)).functor
    exact ⟨eqToIso eG ≪≫ Functor.isoWhiskerLeft _ er⟩

private def scalarComposition {s t r : RingStage.{max u v} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
    (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
    (h : ∀ T : Scheme.{max u v}, a.map T ≫ b.map T = d.map T)
    (T : Scheme.{max u v}) (A : Scalar.{u, v} l Ω a T)
    (B : Scalar.{u, v} l Ω b T) (D : Scalar.{u, v} l Ω d T) :
    ScalarComposition.{u, v} l Ω h T A B D := by
  let e : (A.functor ⋙ B.functor) ⋙ RingStage.inclusion.{u, v} l Ω T r ≅
      D.functor ⋙ RingStage.inclusion.{u, v} l Ω T r :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A.functor B.realization ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight A.realization (pbcDerivedExtend (b.map T)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (PurCompactSupport.tensorComposition
        (a.map T) (b.map T) (d.map T) (h T)) ≪≫ D.realization.symm
  let ff := (ringFullyFaithful.{u, v} l Ω T r).whiskeringRight (C.{u, v} l Ω T (s.stage l))
  refine { iso := ff.preimageIso e, normalized := ?_ }
  intro K
  have hm := congr_app (ff.map_preimage e.hom) K
  change (RingStage.inclusion.{u, v} l Ω T r).map ((ff.preimageIso e).hom.app K) =
    e.hom.app K at hm
  rw [hm]
  dsimp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom]
  simp only [Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app]

private theorem integralOperation (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (E : FieldStage.{max u v} l) :
    ∃ A : Operation.{u, v} l Ω X Y (.integral E),
      ∃ r : LeftRealization.{u, v} l Ω c (.integral E) A,
      ∃ e : A.F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
        PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
          sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier,
        (∀ K : C.{u, v} l Ω X (.integral E),
          (sfIntegralConstructible l E.carrier Y).ι.map (e.hom.app K) =
            r.hom.app K ≫ (sfQcqsCompactSupportRealization l E.carrier D.k
              (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
              ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)) ∧
        (letI := A.leftShift
         letI := constructionInclusionShift.{u, v} l Ω X (.integral E)
         letI := constructionInclusionShift.{u, v} l Ω Y (.integral E)
         r.hom.CommShift ℤ) := by
  classical
  haveI := integralTriangulated l E X
  haveI := integralTriangulated l E Y
  letI := constructionInclusionShift.{u, v} l Ω X (.integral E)
  letI := constructionInclusionShift.{u, v} l Ω Y (.integral E)
  letI : (RingStage.inclusion.{u, v} l Ω X (.integral E)).Full :=
    (ringFullyFaithful.{u, v} l Ω X (.integral E)).full
  letI : (RingStage.inclusion.{u, v} l Ω X (.integral E)).Faithful :=
    (ringFullyFaithful.{u, v} l Ω X (.integral E)).faithful
  letI : (RingStage.inclusion.{u, v} l Ω X (.integral E)).IsTriangulated :=
    ⟨fun _ hT ↦ hT⟩
  letI : (RingStage.inclusion.{u, v} l Ω Y (.integral E)).Full :=
    (ringFullyFaithful.{u, v} l Ω Y (.integral E)).full
  letI : (RingStage.inclusion.{u, v} l Ω Y (.integral E)).Faithful :=
    (ringFullyFaithful.{u, v} l Ω Y (.integral E)).faithful
  letI : (RingStage.inclusion.{u, v} l Ω Y (.integral E)).IsTriangulated :=
    ⟨fun _ hT ↦ hT⟩
  letI := PurCompactSupport.imageCommShift (PurCompactSupport.completed l E.carrier) c
  obtain ⟨hpres, hadj⟩ := exists_integral_support_adjoint l D hl f c E
  let F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E) :=
    (finiteTorConstructibleIntegral l E.carrier Y).lift
    (RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
      PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c) hpres
  letI : F.IsLeftAdjoint := hadj
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  let r : F ⋙ RingStage.inclusion.{u, v} l Ω Y (.integral E) ≅
      RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c :=
    (finiteTorConstructibleIntegral l E.carrier Y).liftCompιIso
    (RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
      PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c) hpres
  letI : (RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
      PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).CommShift ℤ := by
    exact compShift _ _ (constructionInclusionShift.{u, v} l Ω X (.integral E))
      (PurCompactSupport.imageCommShift (PurCompactSupport.completed l E.carrier) c)
  letI : F.CommShift ℤ := Functor.CommShift.ofComp r ℤ
  letI : r.hom.CommShift ℤ := Functor.CommShift.ofComp_compatibility r ℤ
  have ht : (RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
      PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).IsTriangulated := by
    have hj :
        (PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).IsTriangulated := by
      dsimp only [PurCompactSupport.image]
      infer_instance
    exact compExact _ _ (constructionInclusionShift.{u, v} l Ω X (.integral E))
      (PurCompactSupport.imageCommShift (PurCompactSupport.completed l E.carrier) c)
      inferInstance hj
  letI : F.IsTriangulated := (Functor.isTriangulated_iff_comp_right r).mpr ht
  letI := adj.rightAdjointCommShift ℤ
  letI := adj.commShift_of_leftAdjoint ℤ
  letI := adj.right_adjoint_additive
  let eambient :
      (F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y) ⋙
        (sfIntegralConstructible l E.carrier Y).ι ≅
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier) ⋙
        (sfIntegralConstructible l E.carrier Y).ι :=
    r ≪≫ Functor.isoWhiskerLeft
    (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X)
    (sfQcqsCompactSupportRealization l E.carrier D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c)
  let ff := (sfIntegralConstructible l E.carrier Y).fullyFaithfulι.whiskeringRight
    (finiteTorConstructibleIntegralCategory l E.carrier X)
  let e : F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier :=
    ff.preimageIso eambient
  refine ⟨{
    F := F
    G := G
    adjunction := adj
    leftExact := inferInstance
    rightExact := adj.isTriangulated_rightAdjoint
    unitShift := inferInstance
    counitShift := inferInstance }, r, e, ?_, inferInstance⟩
  intro K
  exact congr_app (ff.map_preimage eambient.hom) K

/-- Construct the finite and integral stages, without any field-stage adjunction.
Source: Zheng, Lemma 5.22, Construction 5.25 and Proposition 5.24; coefficient
construction steps 1--4 (blueprint: lem-sf-ring-stage-assembly).

Proof: choose the literal scalar restrictions once for each endpoint, independently of
compactification. Restrict finite compact support and the specified finite exceptional
functor to the actual full finite-Tor categories. Transport the ordinary etale adjunction
through the site comparison and give its right functor the adjoint shift structure.
Choose the finite realization and its inverse image of the canonical proper/open scalar
map; the counit transpose is invertible even for a nonflat quotient. The finite-operation
bounds depend only on the compactification, not the coefficient level.

Apply strict-system transport before taking evaluations, and integral reconstruction to
its normalized finite-Tor outputs with these uniform bounds. Transport the adjunction,
unit and counit through the reconstruction equivalence. The canonical ambient proper/open
realization and its published tower realization give left and integralLeft with exactly
the displayed normalization. Their inherited shifts give leftShift.

Apply the integral scalar-mate construction with these transported adjunctions and the
same ambient realizations. For finite targets use the literal ambient derived extension;
for completed integral extensions use the published strict-tower scalar functor. Ramified
cofinality gives the required generator comparisons. The scalar-only assertion includes
the normalized tensor unitor. Transport the tensor associator through the full inclusion
to prove scalarComposition.
All endpoint scalar choices are the fixed restrictions, so they are shared by every
compactification. Repeat for each compactification; this assertion includes no rational
localization and no common-field descent. Empty source uses zero operations and positive
coefficient levels include the residue level. -/
theorem exists_ring_stage_assembly (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (RingStageAssembly.{u, v} l Ω D hl (f := f)) := by
  classical
  have hf := finiteOperation.{u, v} l Ω D hl f
  choose finite finiteLeft finiteRight finiteShift using hf
  have hi := integralOperation.{u, v} l Ω D hl f
  choose integral integralLeft integralTower integralNormalized integralShift using hi
  let operation (c : Compactification f) (s : RingStage.{max u v} l) :
      Operation.{u, v} l Ω X Y (s.stage l) :=
    match s with
    | .finite E n => finite c E n
    | .integral E => integral c E
  let left (c : Compactification f) (s : RingStage.{max u v} l) :
      LeftRealization.{u, v} l Ω c s (operation c s) :=
    match s with
    | .finite E n => finiteLeft c E n
    | .integral E => integralLeft c E
  have leftShift (c : Compactification f) (s : RingStage.{max u v} l) :
      (left c s).hom.CommShift ℤ := by
    cases s with
    | finite E n => exact finiteShift c E n
    | integral E => exact integralShift c E
  obtain ⟨scalar, finiteEq, finiteNorm, integralEq, integralNorm, identityData,
    comparison, comparisonNorm⟩ :=
    exists_ring_scalar_mates.{u, v} l Ω D hl f operation left leftShift
  refine ⟨{
    operation := operation
    left := left
    finiteRight := fun c E n ↦ Classical.choice (finiteRight c E n)
    integralLeft := integralTower
    integralLeft_normalized := integralNormalized
    scalar := scalar
    finiteScalar_eq := finiteEq
    finiteScalar_normalized := finiteNorm
    integralScalar_eq := integralEq
    integralScalar_normalized := integralNorm
    comparison := comparison
    comparison_normalized := comparisonNorm
    scalarComposition := ?_
    scalarIdentity := identityData
    leftShift := leftShift }⟩
  · intro s t r a b d h ha hb hd side
    exact scalarComposition.{u, v} l Ω a b d h (endpoint X Y side)
      (scalar a ha side) (scalar b hb side) (scalar d hd side)

end WeilConjectures.ConstructibleExceptionalCoefficients
