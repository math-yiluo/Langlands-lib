/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingRefinementScalarWord

/-! # Ring proper/open refinement with its integral scalar square

Source: Zheng Section 5 and Stacks 0F7B, 0F7I; normalized exceptional construction
(blueprint: lem-sf-constructible-ring-left-refinement). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance] Operation.leftShift Operation.rightShift constructionInclusionShift
  Scalar.commShift Scalar.additive
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem shift_of_whisker {A B Z : Type*}
    [Category A] [Category B] [Category Z]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift Z ℤ]
    (F G : A ⥤ B) (I : B ⥤ Z) [I.Faithful]
    [F.CommShift ℤ] [G.CommShift ℤ] [I.CommShift ℤ]
    (τ : F ⟶ G) (hτ : (Functor.whiskerRight τ I).CommShift ℤ) :
    τ.CommShift ℤ := by
  let := hτ
  constructor
  intro n
  ext K
  apply I.map_injective
  apply (cancel_mono ((I.commShiftIso n).hom.app (G.obj K))).mp
  have h := NatTrans.shift_app_comm (Functor.whiskerRight τ I) n K
  simpa only [Functor.commShiftIso_comp_hom_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc,
    ← Functor.commShiftIso_hom_naturality] using h

variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))

/-- The ring part of proper/open refinement, including its integral scalar square.
Source: Stacks 0F7B and 0F7I; Zheng 5.13--5.15; exceptional construction step 6
(blueprint: lem-sf-constructible-ring-left-refinement).

Proof: at finite levels form the open-unit comparison from extension by zero for d
into proper pushforward of extension by zero for c. Proper base change on the open
and vanishing on its complement show that this comparison is invertible on bounded
constructible objects. Compose its inverse with the inverse proper compositor and
lift through the full finite-Tor inclusions using the given left realizations.
At integral coefficients form this same word in strict coefficient systems on the
normalized reduction of the input. Finite-level invertibility and conservative
system evaluations give an inverse of the actual system word. Take total limit;
primitive realization identities give the displayed ambient normalization.
The open-unit word and the proper compositor commute with termwise shifts;
realization identifies these with Roos shifts. Conjugating by the assumed
shift-compatible left realizations gives the required shift equations.
For an integral field extension apply the proper/open scalar square to the strict
system word, whisker by the proper direct image and invert. A single finite-free
basis gives compatible coefficient maps on the ramified en subsystem. Cofinal
realization and the specified scalar and counit normalizations identify this with
the square below. No equality of system maps is inferred from evaluations.
Identity refinements and empty inputs use the same open adjunction and zero maps;
no separatedness of X or Y over the ground field is required. -/
theorem exists_ring_left_refinement
    (hR : ∀ (c : Compactification f) (s : RingStage.{max u v} l),
      letI := (R.operation c (s.stage l)).leftShift
      letI := constructionInclusionShift.{u, v} l Ω X s
      letI := constructionInclusionShift.{u, v} l Ω Y s
      (R.left c s).hom.CommShift ℤ)
    {c d : Compactification f} (r : c.Refinement d) :
    ∃ α : ∀ s : RingStage.{max u v} l,
        (R.operation c (s.stage l)).F ≅ (R.operation d (s.stage l)).F,
      ∃ hα : ∀ s,
        letI := (R.operation c (s.stage l)).leftShift
        letI := (R.operation d (s.stage l)).leftShift
        (α s).hom.CommShift ℤ,
      (∀ s, RingRefinementNormalized.{u, v} l Ω r s (R.left c s) (R.left d s)
        (refinementComparisonOfLeft.{u, v} l Ω _ _ (α s) (hα s))) ∧
    ∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u, v} l Ω X (.integral E)),
      let a := PurCompactSupport.completedChange l E.carrier L.carrier i
      let ha := Allowed.integral E L i
      (R.scalar (s := .integral E) (t := .integral L) a ha false).functor.map
          ((α (.integral E)).hom.app K) ≫
          (Scalar.counitQ.{u, v} l Ω
            (R.scalar (s := .integral E) (t := .integral L) a ha true)
            (R.scalar (s := .integral E) (t := .integral L) a ha false)
            (R.comparison d (s := .integral E) (t := .integral L) a ha)).hom.app K =
        (Scalar.counitQ.{u, v} l Ω
            (R.scalar (s := .integral E) (t := .integral L) a ha true)
            (R.scalar (s := .integral E) (t := .integral L) a ha false)
            (R.comparison c (s := .integral E) (t := .integral L) a ha)).hom.app K ≫
          (α (.integral L)).hom.app
            ((R.scalar (s := .integral E) (t := .integral L) a ha true).functor.obj K) := by
  classical
  choose hi hg ε hε hs using
    (fun s ↦ exists_ring_open_refinement.{u, v} l Ω D hl r s)
  let β := fun s ↦ ringRefinementWord.{u, v} l Ω r s (hg s) (ε s)
  let full (T : Scheme.{max u v}) (s : RingStage.{max u v} l) :
      (RingStage.inclusion.{u, v} l Ω T s).Full := by
    cases s with
    | finite E n => exact (finiteTorConstructible l E.carrier n n.pos T).fullyFaithfulι.full
    | integral E => exact (finiteTorConstructibleIntegral l E.carrier T).fullyFaithfulι.full
  let faithful (T : Scheme.{max u v}) (s : RingStage.{max u v} l) :
      (RingStage.inclusion.{u, v} l Ω T s).Faithful := by
    cases s with
    | finite E n => exact (finiteTorConstructible l E.carrier n n.pos T).fullyFaithfulι.faithful
    | integral E => exact (finiteTorConstructibleIntegral l E.carrier T).fullyFaithfulι.faithful
  let W := fun s : RingStage.{max u v} l ↦
    (Functor.whiskeringRight (C.{u, v} l Ω X (s.stage l))
      (C.{u, v} l Ω Y (s.stage l)) _).obj (RingStage.inclusion.{u, v} l Ω Y s)
  let γ := fun s ↦ R.left c s ≪≫ β s ≪≫ (R.left d s).symm
  let α := fun s ↦ (W s).preimageIso (γ s)
  have hmap (s : RingStage.{max u v} l) :
      Functor.whiskerRight (α s).hom (RingStage.inclusion.{u, v} l Ω Y s) =
        (γ s).hom := by
    exact (W s).map_preimage _
  have hα (s : RingStage.{max u v} l) : (α s).hom.CommShift ℤ := by
    have := hR c s
    have := hR d s
    have : (β s).hom.CommShift ℤ := hs s
    apply shift_of_whisker _ _ (RingStage.inclusion.{u, v} l Ω Y s)
    rw [hmap s]
    dsimp only [γ]
    simp only [Iso.trans_hom, Iso.symm_hom]
    infer_instance
  refine ⟨α, hα, ⟨?_, ?_⟩⟩
  · intro s
    refine ⟨hi s, hg s, fun K ↦ ⟨(ε s).app K, hε s K, ?_⟩⟩
    have hm := congr_app (hmap s) K
    dsimp only [Functor.whiskerRight_app, γ, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app] at hm
    dsimp only [refinementComparisonOfLeft]
    rw [hm]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
      Category.comp_id]
    rfl
  · intro E L i K
    let a := PurCompactSupport.completedChange l E.carrier L.carrier i
    let ha := Allowed.integral E L i
    let SX := R.scalar (s := .integral E) (t := .integral L) a ha true
    let SY := R.scalar (s := .integral E) (t := .integral L) a ha false
    let : SX.functor.CommShift ℤ := SX.commShift
    let : SY.functor.CommShift ℤ := SY.commShift
    let JY := RingStage.inclusion.{u, v} l Ω Y (.integral L)
    let TY := pbcDerivedExtend (a.map Y)
    let Hc := PurCompactSupport.image ((RingStage.integral L).coefficients l) c
    let Hd := PurCompactSupport.image ((RingStage.integral L).coefficients l) d
    have hc := R.comparison_normalized c (s := .integral E) (t := .integral L) a ha K
    have hd := R.comparison_normalized d (s := .integral E) (t := .integral L) a ha K
    have hsquare := ring_refinement_scalar_word.{u, v} l Ω D hl r hi hg ε hε
      E L i K (SX.functor.obj K) (SX.realization.app K)
    apply JY.map_injective
    -- Supply the isomorphism explicitly to avoid searching for a Mono instance of its hom.
    apply (Iso.cancel_iso_hom_right _ _
      ((R.left d (.integral L)).app (SX.functor.obj K) ≪≫
        Hd.mapIso (SX.realization.app K))).1
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    dsimp only [Scalar.counitQ, Scalar.q]
    simp only [Functor.map_comp, Category.assoc]
    calc
      _ = JY.map (SY.functor.map ((α (.integral E)).hom.app K)) ≫
          SY.realization.hom.app ((R.operation d (.integral E)).F.obj K) ≫
          TY.map ((R.left d (.integral E)).hom.app K) ≫
          (PurCompactSupport.comparison a d).app K.obj := by
        erw [hd]
        rfl
      _ = SY.realization.hom.app ((R.operation c (.integral E)).F.obj K) ≫
          TY.map ((RingStage.inclusion.{u, v} l Ω Y (.integral E)).map
            ((α (.integral E)).hom.app K)) ≫
          TY.map ((R.left d (.integral E)).hom.app K) ≫
          (PurCompactSupport.comparison a d).app K.obj := by
        erw [← SY.realization.hom.naturality_assoc]
        rfl
      _ = SY.realization.hom.app ((R.operation c (.integral E)).F.obj K) ≫
          TY.map ((R.left c (.integral E)).hom.app K) ≫
          TY.map ((β (.integral E)).hom.app K) ≫
          (PurCompactSupport.comparison a d).app K.obj := by
        have hm := congr_app (hmap (.integral E)) K
        dsimp only [Functor.whiskerRight_app, γ, Iso.trans_hom, Iso.symm_hom,
          NatTrans.comp_app] at hm
        erw [hm]
        simp only [Functor.map_comp, Category.assoc]
        rw [← TY.map_comp_assoc ((R.left d (.integral E)).inv.app K)
          ((R.left d (.integral E)).hom.app K)]
        simp only [Iso.inv_hom_id_app]
        erw [CategoryTheory.Functor.map_id, Category.id_comp]
      _ = SY.realization.hom.app ((R.operation c (.integral E)).F.obj K) ≫
          TY.map ((R.left c (.integral E)).hom.app K) ≫
          (PurCompactSupport.comparison a c).app K.obj ≫
          Hc.map (SX.realization.inv.app K) ≫
          (β (.integral L)).hom.app (SX.functor.obj K) ≫
          Hd.map (SX.realization.hom.app K) := by
        rw [hsquare]
        rfl
      _ = JY.map ((Scalar.counitQ.{u, v} l Ω SX SY
          (R.comparison c (s := .integral E) (t := .integral L) a ha)).hom.app K) ≫
          (R.left c (.integral L)).hom.app (SX.functor.obj K) ≫
          (β (.integral L)).hom.app (SX.functor.obj K) ≫
          Hd.map (SX.realization.hom.app K) := by
        dsimp only [Scalar.counitQ]
        erw [← reassoc_of% hc]
        erw [← Hc.map_comp_assoc (SX.realization.hom.app K) (SX.realization.inv.app K),
          Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
      _ = _ := by
        have hm := congr_app (hmap (.integral L)) (SX.functor.obj K)
        dsimp only [Functor.whiskerRight_app, γ, Iso.trans_hom, Iso.symm_hom,
          NatTrans.comp_app] at hm
        dsimp only [Scalar.counitQ]
        erw [hm]
        simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
        rfl

end WeilConjectures.ConstructibleExceptionalCoefficients
