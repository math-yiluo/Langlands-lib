/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
import WeilConjectures.SmoothPurity.Supporting.Coefficient.StrictCoefficientProperReduction
import WeilConjectures.SmoothPurity.Supporting.Coefficient.StrictCoefficientOpenReduction

/-! The strict proper/open comparison and its finite coordinates.
(blueprint: lem-qcqs-compact-support-strict-reduction-data) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

-- Keep the two standard localizations transparent to the implicit matcher.
attribute [local implicit_reducible] completed finite
  integralOperationsCommHasDerivedCategory scalarReductionSourceDerived
  scalarReductionTargetDerived reductionModulesHasDerivedCategory integralCoefficientSheaf
  coefficientFiniteDerivedExtension
attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheafTransition compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition
attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor scalarReductionExistence scalarReductionDerivedExistence
  SheafOfModules.monoidalCategory

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

private theorem changeCoordinates_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F F' : A ⥤ B} (e : F ≅ F') {G G' : B ⥤ C} (d : G ≅ G')
    {W : B} {U V T : A} (a : W ⟶ F'.obj U) (b : U ⟶ V) (t : T ≅ V) :
    d.inv.app W ≫ G.map (a ≫ e.inv.app U) ≫ G.map (F.map (b ≫ t.inv)) ≫
        G.map (e.hom.app T) ≫ d.hom.app (F'.obj T) ≫ G'.map (F'.map t.hom) =
      G'.map a ≫ G'.map (F'.map b) := by
  rw [← G.map_comp_assoc, ← G.map_comp_assoc]
  simp only [Category.assoc]
  have h : a ≫ e.inv.app U ≫ F.map (b ≫ t.inv) ≫ e.hom.app T =
      a ≫ F'.map (b ≫ t.inv) := by
    rw [← e.inv.naturality_assoc]
    simp only [Iso.inv_hom_id_app, Category.comp_id]
  rw [h, ← d.inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← G'.map_comp, ← G'.map_comp]
  congr 1
  rw [Category.assoc, ← F'.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

-- Naturality pastes the two comparison equations, cancelling their middle coordinates.
private theorem map_paste_cancel
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {U U' V W : C} {A B T R : D} (ρ : U ≅ U')
    (s : A ⟶ B) (t : B ⟶ T) (u : T ⟶ P.obj V) (v : B ⟶ P.obj U)
    (b : U ⟶ V) (c : V ⟶ W) (p : A ⟶ R) (q : R ⟶ P.obj U') (r : U' ⟶ W)
    (hn : t ≫ u = v ≫ P.map b)
    (hp : s ≫ v = p ≫ q ≫ P.map ρ.inv)
    (hj : b ≫ c = ρ.hom ≫ r) :
    (s ≫ t) ≫ u ≫ P.map c = p ≫ q ≫ P.map r := by
  simp only [Category.assoc]
  rw [← Category.assoc t, hn]
  simp only [Category.assoc]
  rw [← Category.assoc s, hp]
  simp only [Category.assoc]
  rw [← P.map_comp, ← P.map_comp, hj]
  simp only [Iso.inv_hom_id_assoc]

-- Evaluation respects a change of finite coordinates for any strict-system object.
omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
private theorem compactSupportSystemEvaluation_coordinates (n : ℕ)
    (M : coefficientSequenceDerived l E X) {U V : normalizedDVRDerived l E X n}
    (b : (coefficientSequenceDerivedEvaluation l E X n).obj M ⟶ V) (t : U ≅ V) :
    (compactSupportSystemEvaluation l E c n).hom.app M ≫
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map b =
      (strictCoefficientProperEvaluation l E c.g n).hom.app
          ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) c.i).obj M) ≫
        (push (finite l E (n + 1) (Nat.le_add_left 1 n)) c.g).map
          ((strictCoefficientOpenEvaluation l E c.i n).hom.app M) ≫
        (image (finite l E (n + 1) (Nat.le_add_left 1 n)) c).map (b ≫ t.inv) ≫
        (finiteImageIso l E n c).hom.app U ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          t.hom := by
  have := sfIntrinsicExtensionByZero_additive c.i
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  have := proEtaleConstantModuleDirectImage_additive c.g
    (Padic.coefficientExtensionRing l E (n + 1))
  let u := Functor.mapDerivedCategoryNatIso (finiteOpenIso l E n c.i)
  let v := Functor.rightDerivedFunctorNatIso (eqToIso (finiteDirectImage_eq l E n c.g))
  let j₀ := ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i n ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (compactSupportOpenModel c.i (Padic.coefficientExtensionRing l E (n + 1))))
  let p₀ := ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g n ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
      (compactSupportDirectModel c.g (Padic.coefficientExtensionRing l E (n + 1))))
  have h := changeCoordinates_comp u v (j₀.hom.app M) b t
  have h' := congrArg (fun z ↦ p₀.hom.app ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i).obj M) ≫ z) h
  simp only [strictCoefficientProperEvaluation, strictCoefficientOpenEvaluation,
    compactSupportSystemEvaluation, finiteImageIso, PurCompactSupport.image,
    sfIntrinsicCompactSupport,
    sfAmbientCompactSupportCandidate, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Functor.comp_map, Functor.map_comp, Category.assoc,
    u, v, j₀, p₀] at h' ⊢
  exact h'.symm

include K₀ hl
-- The existing statement retains the geometric hypotheses of its source.
set_option linter.unusedSectionVars false in

/-- The strict comparison map exists and has the prescribed finite coordinate identity.

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: lem-qcqs-compact-support-strict-reduction-data).

Paste the strict proper comparison after completed open extension with native proper
image of the strict open comparison. Naturality of proper evaluation and the two
finite comparison equations cancel the coefficient coordinates on the middle scheme.
The proved proper/open factorization gives the ambient comparison, and the finite
presentation isomorphisms cancel by naturality. The total-limit comparison is separate.
-/
theorem qcqsCompactSupport_strictReductionData :
    ∃ (SX : CoefficientDerivedSystemCalculus l E X)
      (SY : CoefficientDerivedSystemCalculus l E Y),
    let N := SX.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g
    let e (n : ℕ) : N ⋙ coefficientSequenceDerivedEvaluation l E Y n ≅
        scalarReductionDerivedExtension l E X n ⋙
          sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c :=
      Functor.isoWhiskerLeft SX.reduction (compactSupportSystemEvaluation l E c n) ≪≫
        Functor.isoWhiskerRight (SX.reductionEvaluation n)
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    ∃ (β : image (completed l E) c ⋙ SY.reduction ⟶ N),
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (SY.reductionEvaluation n).inv.app ((image (completed l E) c).obj K) ≫
            (coefficientSequenceDerivedEvaluation l E Y n).map (β.app K) ≫
            (e n).hom.app K =
          (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K) ≫
            (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K ≫
            (finiteImageIso l E n c).hom.app
              ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj
                K) ≫
            (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1))
              c).map ((finiteReductionIso l E X n).hom.app K) := by
  classical
  obtain ⟨SX, _⟩ := coefficientDerivedSystemEvaluationCalculus l E X
  obtain ⟨SZ, _⟩ := coefficientDerivedSystemEvaluationCalculus l E c.Z
  obtain ⟨SY, _⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  obtain ⟨βJ, hJ⟩ := strictCoefficientOpenReduction l E c.i SX SZ
  obtain ⟨βP, hP⟩ := strictCoefficientProperReduction l E c.g SZ SY
  let J := (openExtension (completed l E) c.i).mapDerivedCategory
  let P := push (completed l E) c.g
  let Js := ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i
  let Ps := ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.g
  -- Functor composition is definitionally associative, so the paste needs no associators.
  let β : image (completed l E) c ⋙ SY.reduction ⟶ SX.reduction ⋙ Js ⋙ Ps :=
    Functor.whiskerLeft J βP ≫ Functor.whiskerRight βJ Ps
  refine ⟨SX, SY, β, ?_⟩
  intro K n
  let evZ := coefficientSequenceDerivedEvaluation l E c.Z n
  let evY := coefficientSequenceDerivedEvaluation l E Y n
  let A := finite l E (n + 1) (Nat.le_add_left 1 n)
  let a := reduction l E (n + 1) (Nat.le_add_left 1 n)
  let Jn := (openExtension A c.i).mapDerivedCategory
  let Pn := push A c.g
  let ρX := SX.reductionEvaluation n ≪≫ (finiteReductionIso l E X n).symm
  let ρZ := SZ.reductionEvaluation n ≪≫ (finiteReductionIso l E c.Z n).symm
  let ρY := SY.reductionEvaluation n ≪≫ (finiteReductionIso l E Y n).symm
  let eJ := strictCoefficientOpenEvaluation l E c.i n
  let eP := strictCoefficientProperEvaluation l E c.g n
  have hn := eP.hom.naturality (βJ.app K)
  change evY.map (Ps.map (βJ.app K)) ≫ eP.hom.app (Js.obj (SX.reduction.obj K)) =
    eP.hom.app (SZ.reduction.obj (J.obj K)) ≫ Pn.map (evZ.map (βJ.app K)) at hn
  have hp : evY.map (β.app K) ≫ eP.hom.app (Js.obj (SX.reduction.obj K)) ≫
        Pn.map (eJ.hom.app (SX.reduction.obj K)) =
      ρY.hom.app ((image (completed l E) c).obj K) ≫
        (comparison a c).app K ≫ (image A c).map (ρX.inv.app K) := by
    dsimp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [evY.map_comp]
    have h := map_paste_cancel Pn (ρZ.app (J.obj K))
      (evY.map (βP.app (J.obj K))) (evY.map (Ps.map (βJ.app K)))
      (eP.hom.app (Js.obj (SX.reduction.obj K))) (eP.hom.app (SZ.reduction.obj (J.obj K)))
      (evZ.map (βJ.app K)) (eJ.hom.app (SX.reduction.obj K))
      (ρY.hom.app (P.obj (J.obj K))) ((properComparison a c.g).app (J.obj K))
      ((openComparison a c.i).app K ≫ Jn.map (ρX.inv.app K)) hn (hP (J.obj K) n) (hJ K n)
    rw [comparison_factorization a c K]
    simp only [Functor.map_comp, Category.assoc] at h ⊢
    change _ = ρY.hom.app (P.obj (J.obj K)) ≫
      (properComparison a c.g).app (J.obj K) ≫ Pn.map ((openComparison a c.i).app K) ≫
        Pn.map (Jn.map (ρX.inv.app K))
    exact h
  have ht :
      (Functor.isoWhiskerLeft SX.reduction (compactSupportSystemEvaluation l E c n) ≪≫
        Functor.isoWhiskerRight (SX.reductionEvaluation n)
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))).hom.app K =
        eP.hom.app (Js.obj (SX.reduction.obj K)) ≫
          Pn.map (eJ.hom.app (SX.reduction.obj K)) ≫
          (image A c).map (ρX.hom.app K) ≫
          (finiteImageIso l E n c).hom.app
            ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K) ≫
          (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1))
            c).map ((finiteReductionIso l E X n).hom.app K) := by
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.app_hom, Iso.app_inv, ρX] using
      compactSupportSystemEvaluation_coordinates l E c n (SX.reduction.obj K)
        ((SX.reductionEvaluation n).hom.app K) ((finiteReductionIso l E X n).app K)
  rw [ht]
  rw [reassoc_of% hp]
  simp only [ρY, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← (image A c).map_comp_assoc, Iso.inv_hom_id_app]
  erw [(image A c).map_id, Category.id_comp]

end WeilConjectures
