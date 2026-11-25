/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarData
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarRestrictions
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftComparisonInvertible

/-! # Existence of normalized left integral scalar comparisons

Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
(blueprint: lem-sf-exceptional-integral-left-scalar-mates)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.reductionDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

-- The chosen derived presentations require an extended conversion budget.
private def ringFullyFaithful (T : Scheme.{u}) (s : RingStage.{u} l) :
    (RingStage.inclusion.{u} l Ω T s).FullyFaithful :=
  match s with
  | .finite E n => (finiteTorConstructible l E.carrier n n.pos T).fullyFaithfulι
  | .integral E => (finiteTorConstructibleIntegral l E.carrier T).fullyFaithfulι

-- The chosen derived presentations require an extended conversion budget.
private def scalarComposition {s t r : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
    (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
    (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
    (T : Scheme.{u}) (A : Scalar.{u} l Ω a T)
    (B : Scalar.{u} l Ω b T) (D : Scalar.{u} l Ω d T) :
    ScalarComposition.{u} l Ω h T A B D := by
  let e : (A.functor ⋙ B.functor) ⋙ RingStage.inclusion.{u} l Ω T r ≅
      D.functor ⋙ RingStage.inclusion.{u} l Ω T r :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A.functor B.realization ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight A.realization (pbcDerivedExtend (b.map T)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (PurCompactSupport.tensorComposition
        (a.map T) (b.map T) (d.map T) (h T)) ≪≫ D.realization.symm
  let ff := (ringFullyFaithful.{u} l Ω T r).whiskeringRight (C.{u} l Ω T (s.stage l))
  refine { iso := ff.preimageIso e, normalized := ?_ }
  intro K
  have hm := congr_app (ff.map_preimage e.hom) K
  change (RingStage.inclusion.{u} l Ω T r).map ((ff.preimageIso e).hom.app K) =
    e.hom.app K at hm
  rw [hm]
  dsimp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom]
  simp only [Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app]

private def liftNaturalIso
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F G : A ⥤ B} {I : B ⥤ D} (ff : I.FullyFaithful) (e : F ⋙ I ≅ G ⋙ I) :
    F ≅ G :=
  NatIso.ofComponents (fun K ↦ ff.preimageIso (e.app K)) (fun f ↦ by
    apply ff.map_injective
    simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
      Iso.app_hom, ff.map_preimage]
    exact e.hom.naturality f)

private theorem liftNaturalIso_hom
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F G : A ⥤ B} {I : B ⥤ D} (ff : I.FullyFaithful) (e : F ⋙ I ≅ G ⋙ I) (K : A) :
    I.map ((liftNaturalIso ff e).hom.app K) = e.hom.app K :=
  ff.map_preimage (e.hom.app K)

private theorem liftedIdentity_exists
    {C D : Type*} [Category C] [Category D] (I : C ⥤ D) (ff : I.FullyFaithful)
    (F : C ⥤ C) (T U : D ⥤ D) (r : F ⋙ I ≅ I ⋙ T)
    (v : T ≅ U) (w : U ≅ 𝟭 D) :
    ∃ q : F ≅ 𝟭 C, ∀ K,
      I.map (q.hom.app K) = r.hom.app K ≫ v.hom.app (I.obj K) ≫ w.hom.app (I.obj K) := by
  let e : F ⋙ I ≅ (𝟭 C) ⋙ I :=
    r ≪≫ isoWhiskerLeft I (v ≪≫ w) ≪≫ I.rightUnitor ≪≫ I.leftUnitor.symm
  refine ⟨liftNaturalIso ff e, ?_⟩
  intro K
  rw [liftNaturalIso_hom]
  simp only [e, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.assoc]
  erw [CategoryTheory.Category.comp_id, CategoryTheory.Category.comp_id]

-- Replace the coefficient family by identities before splitting the stage.
private theorem scalarIdentity_nonempty {s : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
    (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (T : Scheme.{u})
    (A : Scalar.{u} l Ω a T) : Nonempty (ScalarIdentity.{u} l Ω h T A) := by
  cases a with
  | mk m sq =>
    have hm : m = fun W ↦ 𝟙 ((s.coefficients l).ring W) := funext h
    subst m
    cases s with
    | finite E n =>
      let s : RingStage.{u} l := .finite E n
      obtain ⟨q, hq⟩ := liftedIdentity_exists (RingStage.inclusion l Ω T s)
        (ringFullyFaithful l Ω T s) A.functor _ _ A.realization
        (eqToIso (congrArg pbcDerivedExtend (h T)))
        (PurCompactSupport.tensorIdentity ((s.coefficients l).ring T))
      exact ⟨{ iso := q, normalized := hq }⟩
    | integral E =>
      let s : RingStage.{u} l := .integral E
      obtain ⟨q, hq⟩ := liftedIdentity_exists (RingStage.inclusion l Ω T s)
        (ringFullyFaithful l Ω T s) A.functor _ _ A.realization
        (eqToIso (congrArg pbcDerivedExtend (h T)))
        (PurCompactSupport.tensorIdentity ((s.coefficients l).ring T))
      exact ⟨{ iso := q, normalized := hq }⟩

private def scalarIdentity {s : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
    (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (T : Scheme.{u})
    (A : Scalar.{u} l Ω a T) : ScalarIdentity.{u} l Ω h T A :=
  Classical.choice (scalarIdentity_nonempty l Ω a h T A)

-- The chosen derived presentations require an extended conversion budget.
private def LeftNormalized {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (A : Operation.{u} l Ω X Y (s.stage l))
    (B : Operation.{u} l Ω X Y (t.stage l))
    (rA : LeftRealization.{u} l Ω c s A)
    (rB : LeftRealization.{u} l Ω c t B)
    (SX : Scalar.{u} l Ω a X) (SY : Scalar.{u} l Ω a Y)
    (q : A.F ⋙ SY.functor ≅ SX.functor ⋙ B.F) : Prop :=
  ∀ K, (RingStage.inclusion.{u} l Ω Y t).map (q.hom.app K) ≫
      rB.hom.app (SX.functor.obj K) ≫
      (PurCompactSupport.image (t.coefficients l) c).map (SX.realization.hom.app K) =
    SY.realization.hom.app (A.F.obj K) ≫
      (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
      (PurCompactSupport.comparison a c).app ((RingStage.inclusion.{u} l Ω X s).obj K)

-- The chosen derived presentations require an extended conversion budget.
private theorem normalizedLeftComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (A : Operation.{u} l Ω X Y (s.stage l))
    (B : Operation.{u} l Ω X Y (t.stage l))
    (rA : LeftRealization.{u} l Ω c s A)
    (rB : LeftRealization.{u} l Ω c t B)
    (SX : Scalar.{u} l Ω a X) (SY : Scalar.{u} l Ω a Y)
    (hA : rA.hom.CommShift ℤ) (hB : rB.hom.CommShift ℤ)
    (hSX : SX.realization.hom.CommShift ℤ) (hSY : SY.realization.hom.CommShift ℤ)
    (hi : IsIso (whiskerLeft (RingStage.inclusion.{u} l Ω X s)
      (PurCompactSupport.comparison a c))) :
    ∃ q : A.F ⋙ SY.functor ≅ SX.functor ⋙ B.F,
      q.hom.CommShift ℤ ∧ ∀ K,
        (RingStage.inclusion.{u} l Ω Y t).map (q.hom.app K) ≫
          rB.hom.app (SX.functor.obj K) ≫
          (PurCompactSupport.image (t.coefficients l) c).map (SX.realization.hom.app K) =
        SY.realization.hom.app (A.F.obj K) ≫
          (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
          (PurCompactSupport.comparison a c).app ((RingStage.inclusion.{u} l Ω X s).obj K) := by
  let IX := RingStage.inclusion.{u} l Ω X s
  let IY := RingStage.inclusion.{u} l Ω Y t
  have instA := hA
  have instB := hB
  have instSX := hSX
  have instSY := hSY
  have instComp := hi
  have instShift := PurCompactSupport.comparison_commShift a c
  let e : (A.F ⋙ SY.functor) ⋙ IY ≅ (SX.functor ⋙ B.F) ⋙ IY :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft A.F SY.realization ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight rA (pbcDerivedExtend (a.map Y)) ≪≫
      Functor.associator _ _ _ ≪≫ asIso (whiskerLeft IX (PurCompactSupport.comparison a c)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight SX.realization.symm (PurCompactSupport.image (t.coefficients l) c) ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft SX.functor rB.symm ≪≫
      (Functor.associator _ _ _).symm
  let ff := (ringFullyFaithful l Ω Y t).whiskeringRight (C.{u} l Ω X (s.stage l))
  let q := ff.preimageIso e
  have hq : whiskerRight q.hom IY = e.hom := ff.map_preimage e.hom
  refine ⟨q, ?_, ?_⟩
  · have heShift : e.hom.CommShift ℤ := by
      dsimp only [e, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
        isoWhiskerRight_hom, asIso_hom]
      infer_instance
    have hqShift : (whiskerRight q.hom IY).CommShift ℤ := by rw [hq]; infer_instance
    have hfaithful : IY.Faithful := (ringFullyFaithful l Ω Y t).faithful
    exact NatTrans.CommShift.of_whiskerRight q.hom IY
  · intro K
    have hm := congr_app hq K
    change IY.map (q.hom.app K) = e.hom.app K at hm
    rw [hm]
    suffices hunit :
        (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
          (PurCompactSupport.comparison a c).app (IX.obj K) ≫
            𝟙 ((PurCompactSupport.image (t.coefficients l) c).obj
              ((pbcDerivedExtend (a.map X)).obj (IX.obj K))) =
        (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
          (PurCompactSupport.comparison a c).app (IX.obj K) by
      simp only [comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, Iso.symm_hom,
        isoWhiskerRight_hom, asIso_hom, NatTrans.comp_app, associator_hom_app,
        whiskerLeft_app, associator_inv_app, whiskerRight_app, Category.comp_id,
        Category.id_comp, Category.assoc, Iso.inv_hom_id_app_assoc, ← map_comp,
        Iso.inv_hom_id_app, map_id, NatIso.cancel_natIso_hom_left, e]
      exact hunit
    erw [Category.comp_id]

-- The chosen derived presentations require an extended conversion budget.
private theorem normalizedLeftCocycle {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {s t r : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
    (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
    (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
    (A : Operation.{u} l Ω X Y (s.stage l))
    (B : Operation.{u} l Ω X Y (t.stage l))
    (D : Operation.{u} l Ω X Y (r.stage l))
    (rA : LeftRealization.{u} l Ω c s A)
    (rB : LeftRealization.{u} l Ω c t B)
    (rD : LeftRealization.{u} l Ω c r D)
    (AX : Scalar.{u} l Ω a X) (AY : Scalar.{u} l Ω a Y)
    (BX : Scalar.{u} l Ω b X) (BY : Scalar.{u} l Ω b Y)
    (DX : Scalar.{u} l Ω d X) (DY : Scalar.{u} l Ω d Y)
    (qa : A.F ⋙ AY.functor ≅ AX.functor ⋙ B.F)
    (qb : B.F ⋙ BY.functor ≅ BX.functor ⋙ D.F)
    (qd : A.F ⋙ DY.functor ≅ DX.functor ⋙ D.F)
    (hna : LeftNormalized l Ω c a A B rA rB AX AY qa)
    (hnb : LeftNormalized l Ω c b B D rB rD BX BY qb)
    (hnd : LeftNormalized l Ω c d A D rA rD DX DY qd)
    (cx : ScalarComposition.{u} l Ω h X AX BX DX)
    (cy : ScalarComposition.{u} l Ω h Y AY BY DY)
    (K : C.{u} l Ω X (s.stage l)) :
    BY.functor.map (qa.hom.app K) ≫ qb.hom.app (AX.functor.obj K) ≫
        D.F.map (cx.iso.hom.app K) =
      cy.iso.hom.app (A.F.obj K) ≫ qd.hom.app K := by
  let IY := RingStage.inclusion.{u} l Ω Y r
  apply (ringFullyFaithful l Ω Y r).map_injective
  apply (cancel_mono (rD.hom.app (DX.functor.obj K))).mp
  let eDX := (PurCompactSupport.image (r.coefficients l) c).mapIso
    (DX.realization.app K)
  apply (cancel_mono eDX.hom).mp
  simp only [eDX, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  have hr := rD.hom.naturality (cx.iso.hom.app K)
  dsimp only [Functor.comp_map] at hr
  rw [reassoc_of% hr]
  rw [← (PurCompactSupport.image (r.coefficients l) c).map_comp, cx.normalized]
  simp only [Functor.map_comp]
  rw [reassoc_of% (hnb (AX.functor.obj K))]
  have hn := BY.realization.hom.naturality (qa.hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hc := (PurCompactSupport.comparison b c).naturality (AX.realization.hom.app K)
  dsimp only [Functor.comp_map] at hc
  rw [← reassoc_of% hc]
  rw [← (pbcDerivedExtend (b.map Y)).map_comp_assoc,
    ← (pbcDerivedExtend (b.map Y)).map_comp_assoc, Category.assoc, hna K]
  simp only [Functor.map_comp, Category.assoc]
  rw [PurCompactSupport.comparison_composition a b d h c
    ((RingStage.inclusion.{u} l Ω X s).obj K)]
  have ht := (PurCompactSupport.tensorComposition
    (a.map Y) (b.map Y) (d.map Y) (h Y)).hom.naturality (rA.hom.app K)
  dsimp only [Functor.comp_map] at ht
  rw [reassoc_of% ht]
  rw [← reassoc_of% (cy.normalized (A.F.obj K)), ← hnd K]

-- The chosen derived presentations require an extended conversion budget.
private theorem normalizedIdentityLeft {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {s : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
    (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _)
    (A : Operation.{u} l Ω X Y (s.stage l))
    (rA : LeftRealization.{u} l Ω c s A)
    (SX : Scalar.{u} l Ω a X) (SY : Scalar.{u} l Ω a Y)
    (q : A.F ⋙ SY.functor ≅ SX.functor ⋙ A.F)
    (hn : LeftNormalized l Ω c a A A rA rA SX SY q)
    (ix : ScalarIdentity.{u} l Ω h X SX) (iy : ScalarIdentity.{u} l Ω h Y SY)
    (K : C.{u} l Ω X (s.stage l)) :
    q.hom.app K ≫ A.F.map (ix.iso.hom.app K) = iy.iso.hom.app (A.F.obj K) := by
  cases a with
  | mk m sq =>
    have hm : m = fun W ↦ 𝟙 ((s.coefficients l).ring W) := funext h
    subst m
    let a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l) :=
      ⟨fun W ↦ 𝟙 ((s.coefficients l).ring W), sq⟩
    cases s with
    | finite E n =>
      let s : RingStage.{u} l := .finite E n
      apply (ringFullyFaithful l Ω Y s).map_injective
      apply (cancel_mono (rA.hom.app K)).mp
      simp only [Functor.map_comp, Category.assoc]
      have hr := rA.hom.naturality (ix.iso.hom.app K)
      dsimp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at hr
      rw [hr, ix.normalized]
      simp only [Functor.map_comp]
      rw [reassoc_of% (hn K)]
      have hc := PurCompactSupport.comparison_identity a h c
        ((RingStage.inclusion.{u} l Ω X s).obj K)
      simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp] at hc
      rw [hc]
      let v := eqToIso (congrArg pbcDerivedExtend (h Y)) ≪≫
        PurCompactSupport.tensorIdentity ((s.coefficients l).ring Y)
      have hv := v.hom.naturality (rA.hom.app K)
      dsimp only [Functor.id_map] at hv
      change SY.realization.hom.app (A.F.obj K) ≫
          ((pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫ v.hom.app _) = _
      rw [hv, ← Category.assoc]
      exact (congrArg (fun z ↦ z ≫ rA.hom.app K) (iy.normalized (A.F.obj K))).symm
    | integral E =>
      let s : RingStage.{u} l := .integral E
      apply (ringFullyFaithful l Ω Y s).map_injective
      apply (cancel_mono (rA.hom.app K)).mp
      simp only [Functor.map_comp, Category.assoc]
      have hr := rA.hom.naturality (ix.iso.hom.app K)
      dsimp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at hr
      rw [hr, ix.normalized]
      simp only [Functor.map_comp]
      rw [reassoc_of% (hn K)]
      have hc := PurCompactSupport.comparison_identity a h c
        ((RingStage.inclusion.{u} l Ω X s).obj K)
      simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp] at hc
      rw [hc]
      let v := eqToIso (congrArg pbcDerivedExtend (h Y)) ≪≫
        PurCompactSupport.tensorIdentity ((s.coefficients l).ring Y)
      have hv := v.hom.naturality (rA.hom.app K)
      dsimp only [Functor.id_map] at hv
      change SY.realization.hom.app (A.F.obj K) ≫
          ((pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫ v.hom.app _) = _
      rw [hv, ← Category.assoc]
      exact (congrArg (fun z ↦ z ≫ rA.hom.app K) (iy.normalized (A.F.obj K))).symm

-- The chosen derived presentations require an extended conversion budget.
/-- Construct scalar extensions, their normalized left proper/open maps, and the
balanced identity and composition comparisons, before constructing right mates.
Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26.
Proof: construct the normalized scalar restrictions independently at X and Y.
The ambient proper/open comparison is invertible on these finite-Tor inputs, by
induction on allowed coefficient changes. Conjugate this comparison by the scalar
and supplied left realizations, then lift it through the fully faithful inclusion
at Y. The ambient normalization determines the resulting left comparison and its
shift compatibility. Lift tensor associators and unitors in the same way. Apply the
faithful inclusion to the two sides of each coherence equation, cancel the final
realization isomorphisms, and use naturality with the ambient comparison composition
and identity laws. This proves leftCocycle and identityLeft and assembles LeftMates.
No right scalar mate or cofinal system transport is used.
(blueprint: lem-sf-exceptional-integral-left-scalar-mates). -/
theorem exceptionalIntegralLeftScalarMates
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
    Nonempty (LeftMates l Ω c operation left) := by
  classical
  obtain ⟨scX⟩ := scalarRestrictions_exists l Ω D hl X
  obtain ⟨scY⟩ := scalarRestrictions_exists l Ω D hl Y
  let sc (side : Bool) : ScalarRestrictions l Ω (endpoint X Y side) :=
    match side with
    | false => scY
    | true => scX
  let scalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) := (sc side).scalar a ha
  have hex {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
      ∃ q : (operation s).F ⋙ (scalar a ha false).functor ≅
          (scalar a ha true).functor ⋙ (operation t).F,
        q.hom.CommShift ℤ ∧
        LeftNormalized l Ω c a (operation s) (operation t) (left s) (left t)
          (scalar a ha true) (scalar a ha false) q :=
    normalizedLeftComparison l Ω c a (operation s) (operation t) (left s) (left t)
      (scalar a ha true) (scalar a ha false) (transport.leftShift s) (transport.leftShift t)
      ((sc true).scalarShift a ha) ((sc false).scalarShift a ha)
      (integralLeftComparison_isIso l Ω D hl c a ha)
  let q {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) := (hex a ha).choose
  let composition {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) (side : Bool) :=
    scalarComposition l Ω a b d h (endpoint X Y side)
      (scalar a ha side) (scalar b hb side) (scalar d hd side)
  let identity {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a) (side : Bool) :=
    scalarIdentity l Ω a h (endpoint X Y side) (scalar a ha side)
  refine ⟨{
    scalar := scalar
    scalarShift := fun a ha side ↦ (sc side).scalarShift a ha
    finiteScalar_eq := fun E n a ha side ↦ (sc side).finiteScalar_eq E n a ha
    finiteScalar_normalized := fun E n a ha side ↦
      (sc side).finiteScalar_normalized E n a ha
    integralScalar_eq := fun E L i side ↦ (sc side).integralScalar_eq E L i
    integralScalar_normalized := fun E L i side K ↦
      (sc side).integralScalar_normalized E L i K
    q := q
    qShift := fun a ha ↦ (hex a ha).choose_spec.1
    q_normalized := fun a ha K ↦ (hex a ha).choose_spec.2 K
    scalarComposition := composition
    leftCocycle := ?_
    scalarIdentity := identity
    identityLeft := ?_
    tor_interval := fun E L i side K a b h ↦ (sc side).tor_interval E L i K a b h }⟩
  · intro s t r a b d h ha hb hd K
    exact normalizedLeftCocycle l Ω c a b d h (operation s) (operation t) (operation r)
      (left s) (left t) (left r) (scalar a ha true) (scalar a ha false)
      (scalar b hb true) (scalar b hb false) (scalar d hd true) (scalar d hd false)
      (q a ha) (q b hb) (q d hd) (hex a ha).choose_spec.2
      (hex b hb).choose_spec.2 (hex d hd).choose_spec.2
      (composition a b d h ha hb hd true) (composition a b d h ha hb hd false) K
  · intro s a h ha K
    exact normalizedIdentityLeft l Ω c a h (operation s) (left s)
      (scalar a ha true) (scalar a ha false) (q a ha) (hex a ha).choose_spec.2
      (identity a h ha true) (identity a h ha false) K

end WeilConjectures.ExceptionalIntegralScalar
