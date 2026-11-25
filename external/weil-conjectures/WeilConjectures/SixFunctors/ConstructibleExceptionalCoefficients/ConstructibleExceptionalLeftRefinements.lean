/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.ConstructibleRingLeftRefinement
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ConstructibleRationalLeftRefinement

/-! # A geometric step in normalized exceptional coefficient assembly

The coefficient records include the literal localization and representative-arrow action
normalizations; the refinement construction uses these same fixed stage functors. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance] Operation.leftShift Operation.rightShift constructionInclusionShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem inverse_naturality {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) {X Y : A} (e : X ≅ Y)
    (a : F.obj X ⟶ G.obj X) (b : F.obj Y ⟶ G.obj Y)
    (h : F.map e.hom ≫ b = a ≫ G.map e.hom) :
    F.map e.inv ≫ a = b ≫ G.map e.inv := by
  apply (cancel_epi (F.map e.hom)).1
  simp only [← Functor.map_comp_assoc, e.hom_inv_id]
  rw [← Category.assoc, h, Category.assoc, ← G.map_comp, e.hom_inv_id,
    G.map_id, Category.comp_id]
  simp only [F.map_id, Category.id_comp]

private def iso_from_stages {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A : I → Type*} [∀ i, Category (A i)] (S : StageSystem A)
    {B : Type*} [Category B] (F G : S.PairCategory ⥤ B)
    (e : ∀ i, S.ι i ⋙ F ≅ S.ι i ⋙ G)
    (he : ∀ {i j} (h : i ≤ j) (K : A i),
      F.map ((S.transIso h).inv.app K) ≫ (e j).hom.app ((S.T h).obj K) =
        (e i).hom.app K ≫ G.map ((S.transIso h).inv.app K)) : F ≅ G :=
  NatIso.ofComponents (fun K ↦ (e K.stage).app K.obj) (by
    intro ⟨i, K⟩ ⟨j, L⟩ f
    obtain ⟨n, hK, hL, a, rfl⟩ :=
      (StageSystem.exists_stage_representation S).2.1 K L f
    have hL' := inverse_naturality F G ((S.transIso hL).symm.app L)
      ((e j).hom.app L) ((e n).hom.app ((S.T hL).obj L)) (he hL L)
    simp only [Iso.app_inv, Iso.symm_inv] at hL'
    change F.map ((S.transIso hK).inv.app K ≫
      (S.ι n).map a ≫ (S.transIso hL).hom.app L) ≫ (e j).hom.app L =
      (e i).hom.app K ≫ G.map ((S.transIso hK).inv.app K ≫
        (S.ι n).map a ≫ (S.transIso hL).hom.app L)
    simp only [Functor.map_comp, Category.assoc]
    have hn := (e n).hom.naturality_assoc a (G.map ((S.transIso hL).hom.app L))
    simp only [Functor.comp_map] at hn
    rw [hL', hn, ← Category.assoc, he hK K]
    simp only [Category.assoc])

private theorem transition_of_eq {A B D E : Type*}
    [Category A] [Category B] [Category D] [Category E]
    {T U : A ⥤ B} (hT : T = U) (J : B ⥤ D) (I : A ⥤ D)
    (t : T ⋙ J ≅ I) (F G : D ⥤ E)
    (ei : I ⋙ F ≅ I ⋙ G) (ej : J ⋙ F ≅ J ⋙ G) (K : A)
    (hh :
      F.map ((eqToIso (congrArg (fun V ↦ V ⋙ J) hT.symm) ≪≫ t).inv.app K) ≫
          ej.hom.app (U.obj K) =
        ei.hom.app K ≫
          G.map ((eqToIso (congrArg (fun V ↦ V ⋙ J) hT.symm) ≪≫ t).inv.app K)) :
    F.map (t.inv.app K) ≫ ej.hom.app (T.obj K) = ei.hom.app K ≫ G.map (t.inv.app K) := by
  subst U
  simpa only [eqToIso_refl, Iso.refl_trans] using hh

private theorem shift_from_cover {A B : Type*} [Category A] [Category B]
    [HasShift A ℤ] [HasShift B ℤ] (F G : A ⥤ B) [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) {I : Type*} (C : I → Type*) [∀ i, Category (C i)]
    [∀ i, HasShift (C i) ℤ] (J : ∀ i, C i ⥤ A) [∀ i, (J i).CommShift ℤ]
    (hJ : ∀ X : A, ∃ i K, (J i).obj K = X)
    (hτ : ∀ i, (Functor.whiskerLeft (J i) τ).CommShift ℤ) : τ.CommShift ℤ := by
  constructor
  intro m
  ext X
  obtain ⟨i, K, rfl⟩ := hJ X
  let := hτ i
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft (J i) τ) m K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  rw [← τ.naturality_assoc] at h
  exact (cancel_epi (F.map (((J i).commShiftIso m).hom.app K))).1 h

private theorem field_q_shift {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s) (B : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t)
    (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t)
    (d : CounitFieldComparison.{u, v} l Ω A B TX TY)
    (sx : TX.CommShift ℤ) (sy : TY.CommShift ℤ)
    (hx : sx = d.shiftX) (hy : sy = d.shiftY) :
    letI := A.leftShift
    letI := B.leftShift
    letI := sx
    letI := sy
    d.q.hom.CommShift ℤ := by
  subst sx
  subst sy
  let := d.shiftX
  let := d.shiftY
  exact d.comparison.qShift

variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
  (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
  (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
  (H : CoefficientConstructionNormalization.{u, v} l Ω D hl R F M)

private def closed_left_iso
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (H : CoefficientConstructionNormalization.{u, v} l Ω D hl R F M)
    {c d : Compactification f}
    (β : ∀ E : FieldStage.{max u v} l,
      (R.operation c (.rational E)).F ≅ (R.operation d (.rational E)).F)
    (hs : ∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u, v} l Ω X (.rational E)),
      (rationalScalar.{u, v} l Ω E L i Y).map ((β E).hom.app K) ≫
          (F.rationalComparison d E L i).q.hom.app K =
        (F.rationalComparison c E L i).q.hom.app K ≫
          (β L).hom.app ((rationalScalar.{u, v} l Ω E L i X).obj K)) :
    (R.operation c .closed).F ≅ (R.operation d .closed).F := by
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X
  let e (i : AlgebraicallyClosedCoefficients.Index l Ω) :
      commonInclusion l Ω X i ⋙ (R.operation c .closed).F ≅
        commonInclusion l Ω X i ⋙ (R.operation d .closed).F :=
    (M.commonComparison c i).q.symm ≪≫
      Functor.isoWhiskerRight (β (commonField l Ω i)) (commonInclusion l Ω Y i) ≪≫
        (M.commonComparison d i).q
  apply iso_from_stages S _ _ e
  intro i j h K
  change C.{u, v} l Ω X (.rational (commonField l Ω i)) at K
  have hc := H.commonTransitionNatural c i j h K
  have hd := H.commonTransitionNatural d i j h K
  have hβ := hs (commonField l Ω i) (commonField l Ω j)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) K
  have hn := (commonTransition l Ω Y i j h).inv.naturality ((β (commonField l Ω i)).hom.app K)
  simp only [Functor.comp_map] at hn
  have hh :
      (R.operation c .closed).F.map ((commonTransition l Ω X i j h).inv.app K) ≫
          (e j).hom.app ((rationalScalar l Ω (commonField l Ω i) (commonField l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X).obj K) =
        (e i).hom.app K ≫
          (R.operation d .closed).F.map ((commonTransition l Ω X i j h).inv.app K) := by
    apply (Iso.cancel_iso_hom_left ((M.commonComparison c i).q.app K) _ _).1
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    simp only [Category.assoc]
    rw [← Category.assoc, hc]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← (commonInclusion l Ω Y j).map_comp_assoc, ← hβ]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc, ← hn]
    simp only [Category.assoc] at *
    rw [← hd]
  have hT := (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
    l Ω X).exists.choose_spec.1 i j h
  exact transition_of_eq hT (S.ι j) (S.ι i) (S.transIso h)
    _ _ (e i) (e j) K hh

private theorem closed_left_iso_shift
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (H : CoefficientConstructionNormalization.{u, v} l Ω D hl R F M)
    {c d : Compactification f}
    (β : ∀ E : FieldStage.{max u v} l,
      (R.operation c (.rational E)).F ≅ (R.operation d (.rational E)).F)
    (hβ : ∀ E,
      letI := (R.operation c (.rational E)).leftShift
      letI := (R.operation d (.rational E)).leftShift
      (β E).hom.CommShift ℤ)
    (hs : ∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u, v} l Ω X (.rational E)),
      (rationalScalar.{u, v} l Ω E L i Y).map ((β E).hom.app K) ≫
          (F.rationalComparison d E L i).q.hom.app K =
        (F.rationalComparison c E L i).q.hom.app K ≫
          (β L).hom.app ((rationalScalar.{u, v} l Ω E L i X).obj K)) :
    letI := (R.operation c .closed).leftShift
    letI := (R.operation d .closed).leftShift
    (closed_left_iso l Ω D hl R F M H β hs).hom.CommShift ℤ := by
  let := (R.operation c .closed).leftShift
  let := (R.operation d .closed).leftShift
  let (i : AlgebraicallyClosedCoefficients.Index l Ω) := (M.commonComparison c i).shiftX
  let : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      Category (C.{u, v} l Ω X (.rational (commonField l Ω i))) :=
    fun i ↦ category.{u, v} l Ω X (.rational (commonField l Ω i))
  let : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      HasShift (C.{u, v} l Ω X (.rational (commonField l Ω i))) ℤ :=
    fun i ↦ shift.{u, v} l Ω X (.rational (commonField l Ω i))
  apply shift_from_cover _ _ _
    (fun i : AlgebraicallyClosedCoefficients.Index l Ω ↦
      C.{u, v} l Ω X (.rational (commonField l Ω i)))
    (commonInclusion l Ω X)
  · intro K
    exact ⟨K.stage, K.obj, rfl⟩
  · intro i
    let := (R.operation c (.rational (commonField l Ω i))).leftShift
    let := (R.operation d (.rational (commonField l Ω i))).leftShift
    let := (M.commonComparison c i).shiftY
    let := hβ (commonField l Ω i)
    have : (M.commonComparison c i).q.hom.CommShift ℤ :=
      field_q_shift l Ω _ _ _ _ (M.commonComparison c i) _ _ rfl rfl
    have : (M.commonComparison d i).q.hom.CommShift ℤ :=
      field_q_shift l Ω _ _ _ _ (M.commonComparison d i) _ _
        (H.commonShiftX c d i) (H.commonShiftY c d i)
    change ((M.commonComparison c i).q.inv ≫
      Functor.whiskerRight (β (commonField l Ω i)).hom (commonInclusion l Ω Y i) ≫
        (M.commonComparison d i).q.hom).CommShift ℤ
    infer_instance

/-- Construct the left proper/open refinements on normalized coefficient stages.
Source: Stacks 0F7B and 0F7I, Zheng 5.13--5.15; exceptional construction step 6
(blueprint: lem-sf-constructible-exceptional-left-refinements).

Proof: for a proper refinement r use the open unit to obtain the canonical map from
j_d! to Rr_* j_c!. Proper base change identifies its restriction to the open with
identity, so it is invertible on the compact-support objects. Compose its inverse
with proper direct-image composition and transport through the given left
realizations. Full faithfulness lifts this natural isomorphism to the full finite-Tor
categories, giving the exact RingRefinementNormalized formula. At integral stages use
the same map of strict systems before total limit; the prescribed ambient-to-tower
realizations identify it with the ambient proper/open word. Shift compatibility is
termwise and passes to the total limit; transport through the shift-compatible
left realizations preserves it. Localize the integral map on all fraction morphisms.
The identity normalization of the rationalization comparisons gives the displayed
rational equation. At a common finite field use its rational map conjugated by the
common-stage q maps. Every pair-category arrow is a stage arrow at a common field
conjugated by transition isomorphisms; commonTransitionNatural expresses both closed
functors on transitions by the rational scalar q, and the canonical proper/open scalar
square (the localized integral q commutes with the integral refinement map) gives
naturality on them. The common-stage shifts and q maps give the shift equation. For the identity
refinement the open unit and proper composition reduce to identities; for empty
source the maps are the unique maps of zero functors. Only left maps are output;
the right isomorphisms and both adjunction equations are constructed separately by
adjunction conjugation. -/
theorem exists_coefficient_left_refinements (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F)
    (H : CoefficientConstructionNormalization.{u, v} l Ω D hl R F M) :
    Nonempty (CoefficientLeftRefinements.{u, v} l Ω D hl R F M)  := by
  classical
  choose α hα hp using
    (fun (c d : Compactification f) (r : c.Refinement d) ↦
      exists_ring_left_refinement.{u, v} l Ω D hl R H.leftShift r)
  choose β hβ using
    (fun (c d : Compactification f) (r : c.Refinement d) ↦
      exists_rational_left_refinement.{u, v} l Ω D hl R F
        (H.localizationShiftX c d) (H.localizationShiftY c d) H.localizationIdentity
        (fun E ↦ α c d r (.integral E)) (fun E ↦ hα c d r (.integral E))
        (hp c d r).2)
  let left (c d : Compactification f) (r : c.Refinement d) (s : Stage.{max u v} l) :
      (R.operation c s).F ≅ (R.operation d s).F :=
    match s with
    | .finite E n => α c d r (.finite E n)
    | .integral E => α c d r (.integral E)
    | .rational E => β c d r E
    | .closed => closed_left_iso l Ω D hl R F M H (β c d r) (hβ c d r).2.2
  have hleft (c d : Compactification f) (r : c.Refinement d) (s : Stage.{max u v} l) :
      letI := (R.operation c s).leftShift
      letI := (R.operation d s).leftShift
      (left c d r s).hom.CommShift ℤ := by
    cases s with
    | finite E n => exact hα c d r (.finite E n)
    | integral E => exact hα c d r (.integral E)
    | rational E => exact (hβ c d r).1 E
    | closed =>
      exact closed_left_iso_shift l Ω D hl R F M H (β c d r)
        (hβ c d r).1 (hβ c d r).2.2
  refine ⟨{ left := fun {c d} r s ↦ left c d r s
            leftShift := fun {c d} r s ↦ hleft c d r s
            normalized := ?_
            rational := ?_
            common := ?_ }⟩
  · intro c d r s
    cases s with
    | finite E n => exact (hp c d r).1 (.finite E n)
    | integral E => exact (hp c d r).1 (.integral E)
  · intro c d r E K
    exact (hβ c d r).2.1 E K
  · intro c d r i K
    rfl

end WeilConjectures.ConstructibleExceptionalCoefficients
