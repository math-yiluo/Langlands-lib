/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralReductionEvaluation
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Support.IntegralSupportCounitProjection
import all WeilConjectures.SixFunctors.IntegralSystemRealization.ConstructibleReductionGood

/-! # Left exceptional mate under normalized finite reduction

Source: Zheng, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-reduction-left-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem cancel_coordinates {D : Type*} [Category D] {A B C F G : D}
    (b : B ≅ A) (e : C ≅ B) (q : F ≅ G) (v : C ⟶ F) (z : A ⟶ G)
    (h : b.inv ≫ e.inv ≫ v = z ≫ q.inv) :
    v ≫ q.hom = e.hom ≫ b.hom ≫ z := by
  have hh := congrArg (fun k ↦ e.hom ≫ b.hom ≫ k ≫ q.hom) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using hh

-- Paste the integral realization and counit squares before specializing to derived categories.
-- Keeping the paths right-associated avoids repeated normalization of the coefficient types.
private theorem reduction_comparison_pasting {C₀ C₁ : Type*} [Category C₀] [Category C₁]
    {F G : C₀ ⥤ C₁} (δ : F ≅ G) {A B C D H : C₀} (r : A ≅ B)
    {k : A ⟶ H} {b : B ⟶ C} {s : C ⟶ D} {t : D ⟶ H}
    {Z₀ Z₁ Z₂ Z₃ Z₄ Z₅ Z₆ Z₇ Z₈ : C₁} (p : Z₀ ⟶ F.obj A)
    {q : F.obj H ⟶ Z₁} {i : Z₁ ⟶ Z₂} {j : Z₂ ⟶ Z₃}
    {u₁ : G.obj D ⟶ Z₄} {u₂ : Z₄ ⟶ Z₅}
    {v₁ : G.obj C ⟶ Z₆} {v₂ : Z₆ ⟶ Z₇}
    {v : Z₇ ⟶ Z₅} {w₁ : Z₅ ⟶ Z₈} {w₂ : Z₈ ⟶ Z₃}
    (hi : r.inv ≫ k = b ≫ s ≫ t)
    (hp : G.map t ≫ δ.inv.app H ≫ q ≫ i ≫ j = u₁ ≫ u₂ ≫ w₁ ≫ w₂)
    (hm : G.map s ≫ u₁ ≫ u₂ = v₁ ≫ v₂ ≫ v) :
    p ≫ F.map k ≫ q ≫ i ≫ j =
      p ≫ δ.hom.app A ≫ G.map r.hom ≫ G.map b ≫ v₁ ≫ v₂ ≫ v ≫ w₁ ≫ w₂ := by
  have hk : k = r.hom ≫ b ≫ s ≫ t := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun z ↦ r.hom ≫ z) hi
  calc
    p ≫ F.map k ≫ q ≫ i ≫ j =
        p ≫ δ.hom.app A ≫ G.map k ≫ δ.inv.app H ≫ q ≫ i ≫ j := by
      rw [← δ.hom.naturality_assoc, Iso.hom_inv_id_app_assoc]
    _ = _ := by
      rw [hk]
      simp only [Functor.map_comp, Category.assoc]
      rw [hp, reassoc_of% hm]

private theorem counit_coordinates (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (n : ℕ)
    (N : (sequenceProperty l E T).FullSubcategory) :
    (coefficientFiniteDerivedExtension l E.carrier T n).map
        ((eqToIso R.limit).inv.app N) ≫
      (R.evaluationRealization l E T n).inv.app (R.equivalence.inverse.obj N) ≫
      (R.evaluation n ⋙ (finiteTorConstructible l E.carrier (n + 1)
        (Nat.succ_pos n) T).ι).map (R.equivalence.counit.app N) =
    ((R.calculus.reductionEvaluation n).inv.app
        ((coefficientSequenceLimit l E.carrier T).obj N.obj) ≫
      (coefficientSequenceDerivedEvaluation l E.carrier T n).map
        (R.calculus.adjunction.counit.app N.obj)) ≫
      (eqToIso (R.evaluation_eq n)).inv.app N := by
  simp only [Reconstruction.evaluationRealization, Iso.trans_inv, NatTrans.comp_app,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, whiskerLeft_app, whiskerRight_app]
  simp only [Category.assoc]
  erw [(R.calculus.reductionEvaluation n).inv.naturality_assoc]
  simp only [Functor.comp_map]
  erw [← (eqToIso (R.evaluation_eq n)).inv.naturality]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  congr 2
  apply congrArg (coefficientSequenceDerivedEvaluation l E.carrier T n).map
  apply eq_of_heq
  simpa only [eqToIso, eqToHom_app, eqToHom_map, eqToHom_comp_heq_iff,
    heq_comp_eqToHom_iff] using R.counit N

private theorem reduction_coordinates (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (n : ℕ)
    (A : finiteTorConstructibleIntegralCategory l E.carrier T)
    (N : (sequenceProperty l E T).FullSubcategory)
    (r : A ⟶ R.equivalence.inverse.obj N) :
    (R.evaluation n ⋙ (finiteTorConstructible l E.carrier (n + 1)
        (Nat.succ_pos n) T).ι).map
        (R.equivalence.functor.map r ≫ R.equivalence.counit.app N) ≫
      (eqToIso (R.evaluation_eq n)).hom.app N =
    (R.evaluationRealization l E T n).hom.app A ≫
      (coefficientFiniteDerivedExtension l E.carrier T n).map
        ((finiteTorConstructibleIntegral l E.carrier T).ι.map r) ≫
      (coefficientFiniteDerivedExtension l E.carrier T n).map
        ((eqToIso R.limit).hom.app N) ≫
      (R.calculus.reductionEvaluation n).inv.app
        ((coefficientSequenceLimit l E.carrier T).obj N.obj) ≫
      (coefficientSequenceDerivedEvaluation l E.carrier T n).map
        (R.calculus.adjunction.counit.app N.obj) := by
  let V := R.evaluation n ⋙
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) T).ι
  let F := coefficientFiniteDerivedExtension l E.carrier T n
  have hc := counit_coordinates l E T R n N
  have hc' : V.map (R.equivalence.counit.app N) ≫
      (eqToIso (R.evaluation_eq n)).hom.app N =
      (R.evaluationRealization l E T n).hom.app (R.equivalence.inverse.obj N) ≫
        F.map ((eqToIso R.limit).hom.app N) ≫
        (R.calculus.reductionEvaluation n).inv.app
          ((coefficientSequenceLimit l E.carrier T).obj N.obj) ≫
        (coefficientSequenceDerivedEvaluation l E.carrier T n).map
          (R.calculus.adjunction.counit.app N.obj) := by
    exact cancel_coordinates
      (F.mapIso ((eqToIso R.limit).app N))
      ((R.evaluationRealization l E T n).app (R.equivalence.inverse.obj N))
      ((eqToIso (R.evaluation_eq n)).app N)
      (V.map (R.equivalence.counit.app N))
      ((R.calculus.reductionEvaluation n).inv.app
          ((coefficientSequenceLimit l E.carrier T).obj N.obj) ≫
        (coefficientSequenceDerivedEvaluation l E.carrier T n).map
          (R.calculus.adjunction.counit.app N.obj)) hc
  simp only [Functor.map_comp, Category.assoc]
  rw [hc']
  exact (R.evaluationRealization l E T n).hom.naturality_assoc r _

private theorem reconstruction_counit (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (N : (sequenceProperty l E T).FullSubcategory) :
    R.calculus.reduction.map ((eqToIso R.limit).inv.app N) ≫
      (eqToIso R.reduction).inv.app (R.equivalence.inverse.obj N) ≫
      (sequenceProperty l E T).ι.map (R.equivalence.counit.app N) =
    R.calculus.adjunction.counit.app N.obj := by
  apply eq_of_heq
  simpa only [eqToIso, eqToHom_app, eqToHom_map, eqToHom_comp_heq_iff] using R.counit N

private def inputIso (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (K : finiteTorConstructibleIntegralCategory l E.carrier T) :
    (coefficientSequenceLimit l E.carrier T).obj
        (R.equivalence.functor.obj K).obj ≅ K.obj :=
  ((eqToIso R.limit).app (R.equivalence.functor.obj K)).symm ≪≫
    (finiteTorConstructibleIntegral l E.carrier T).ι.mapIso (R.equivalence.unitIso.app K).symm

private theorem input_normalized (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (K : finiteTorConstructibleIntegralCategory l E.carrier T) :
    R.calculus.reduction.map (inputIso l E T R K).hom ≫
      (eqToIso R.reduction).inv.app K =
    R.calculus.adjunction.counit.app (R.equivalence.functor.obj K).obj := by
  have h := reconstruction_counit l E T R (R.equivalence.functor.obj K)
  rw [R.equivalence.counit_app_functor] at h
  have hn := (eqToIso R.reduction).inv.naturality (R.equivalence.unitIso.inv.app K)
  dsimp only [Functor.comp_map] at hn
  dsimp only [inputIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp]
  rw [Functor.map_comp, Category.assoc]
  erw [hn]
  exact h

private theorem reductionUniq_evaluation (E : FieldStage.{u} l) (T : Scheme.{u})
    (S R : CoefficientDerivedSystemCalculus l E.carrier T)
    (K : DerivedCategory (scalarReductionSource l E.carrier T)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E.carrier T n).map
        ((S.adjunction.leftAdjointUniq R.adjunction).hom.app K) ≫
      (R.reductionEvaluation n).hom.app K = (S.reductionEvaluation n).hom.app K := by
  let V := coefficientSequenceDerivedEvaluation l E.carrier T n
  let U := coefficientFiniteDerivedRestriction l E.carrier T n
  let α := S.adjunction.leftAdjointUniq R.adjunction
  have he : (S.reductionEvaluation n).inv.app K ≫ V.map (α.hom.app K) =
      (R.reductionEvaluation n).inv.app K := by
    apply ((coefficientFiniteAdjunction l E.carrier T n).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, U.map_comp,
      ← Category.assoc, ← S.unit_projection]
    have hp := (coefficientSequenceProjection l E.carrier T n).naturality (α.hom.app K)
    dsimp only [Functor.comp_map] at hp
    rw [Category.assoc, ← hp, ← Category.assoc]
    rw [Adjunction.unit_leftAdjointUniq_hom_app, R.unit_projection]
  apply (cancel_epi ((S.reductionEvaluation n).inv.app K)).1
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
    congrArg (fun f ↦ f ≫ (R.reductionEvaluation n).hom.app K) he

private theorem sequence_good (E : FieldStage.{u} l) (T : Scheme.{u})
    (N : (sequenceProperty l E T).FullSubcategory) :
    IntegralSystemRealization.Good l E.carrier T N.obj := by
  obtain ⟨a, b, c, d, hab, hcd, h⟩ := N.property.2
  have bounds : IntegralSystemRealization.LevelBounds l E.carrier T N.obj := by
    refine ⟨a, b, c, d, hab, hcd, fun n ↦ ?_⟩
    refine ⟨(h n).1.1, ?_, (h n).2.2.2⟩
    intro i hi
    exact ⟨le_of_not_gt (fun hlt ↦ hi ((DerivedCategory.isGE_iff _ a).mp (h n).2.1 i hlt)),
      le_of_not_gt (fun hlt ↦ hi ((DerivedCategory.isLE_iff _ b).mp (h n).2.2.1 i hlt))⟩
  exact ⟨N.property.1, bounds,
    IntegralSystemRealization.origins_of_bounds l E.carrier T N.obj bounds⟩

private theorem counit_independent (E : FieldStage.{u} l) (T : Scheme.{u})
    (S R : CoefficientDerivedSystemCalculus l E.carrier T)
    (N : coefficientSequenceDerived l E.carrier T) (n : ℕ) :
    (S.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E.carrier T).obj N) ≫
        (coefficientSequenceDerivedEvaluation l E.carrier T n).map (S.adjunction.counit.app N) =
      (R.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E.carrier T).obj N) ≫
        (coefficientSequenceDerivedEvaluation l E.carrier T n).map
          (R.adjunction.counit.app N) := by
  apply ((coefficientFiniteAdjunction l E.carrier T n).homEquiv _ _).injective
  exact (S.counit_projection N n).trans (R.counit_projection N n).symm

private def ambientModels (E : FieldStage.{u} l) (D : FiniteFieldDatum.{u})
    (o : IntegralSystemRealization.Operations l E.carrier)
    (a : IntegralSystemRealization.Realizations l E.carrier D o) :
    IntegralSystemRealization.AmbientModels l E.carrier o := by
  cases a with
  | mk compositors openComparisons canonicalBridge properOpen ringedTensorCoherence comparison
      realizationModel openRealization openNormalization inputNormalization push pull shriek tensor
      supportRecursion reduction normalization ringedModels ringedOpenComparisons ringedProperOpen
      completionIso coherence compactSupport =>
    exact {
      compositors := compositors
      openComparisons := openComparisons
      canonicalBridge := canonicalBridge
      properOpen := properOpen
      ringedTensorCoherence := ringedTensorCoherence
      realizationModel := realizationModel
      openRealization := openRealization
      openNormalization := openNormalization
      ringedModels := ringedModels
      ringedOpenComparisons := ringedOpenComparisons
      ringedProperOpen := ringedProperOpen }

private theorem ambientModels_model (E : FieldStage.{u} l) (D : FiniteFieldDatum.{u})
    (o : IntegralSystemRealization.Operations l E.carrier)
    (a : IntegralSystemRealization.Realizations l E.carrier D o) :
    (ambientModels l E D o a).realizationModel = a.realizationModel := by
  cases a
  rfl

private theorem ambientModels_open (E : FieldStage.{u} l) (D : FiniteFieldDatum.{u})
    (o : IntegralSystemRealization.Operations l E.carrier)
    (a : IntegralSystemRealization.Realizations l E.carrier D o) :
    @IntegralSystemRealization.AmbientModels.openRealization _ _ _ _ _ _ _
      (ambientModels l E D o a) = @a.openRealization := by
  cases a
  rfl

private def inputRho (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (K : finiteTorConstructibleIntegralCategory l E.carrier T) :
    (R.equivalence.functor.obj K).obj ≅
      (IntegralSystemRealization.calculus l E.carrier T).reduction.obj K.obj :=
  (eqToIso R.reduction).app K ≪≫
    (R.calculus.adjunction.leftAdjointUniq
      (IntegralSystemRealization.calculus l E.carrier T).adjunction).app K.obj

private theorem inputRho_normalized (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (K : finiteTorConstructibleIntegralCategory l E.carrier T) :
    (IntegralSystemRealization.calculus l E.carrier T).reduction.map
        (inputIso l E T R K).hom ≫ (inputRho l E T R K).inv =
      (IntegralSystemRealization.calculus l E.carrier T).adjunction.counit.app
        (R.equivalence.functor.obj K).obj := by
  dsimp only [inputRho, Iso.trans_inv, Iso.app_inv]
  rw [← Category.assoc]
  erw [(R.calculus.adjunction.leftAdjointUniq
    (IntegralSystemRealization.calculus l E.carrier T).adjunction).inv.naturality]
  rw [Category.assoc, input_normalized]
  exact (IntegralSystemRealization.calculus l E.carrier T).adjunction.leftAdjointUniq_hom_app_counit
    R.calculus.adjunction _

private theorem inputRho_evaluation (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (K : finiteTorConstructibleIntegralCategory l E.carrier T)
    (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E.carrier T n).map (inputRho l E T R K).hom ≫
      ((IntegralSystemRealization.calculus l E.carrier T).reductionEvaluation n).hom.app K.obj =
    (eqToIso (R.evaluation_eq n)).inv.app (R.equivalence.functor.obj K) ≫
      (R.evaluationRealization l E T n).hom.app K := by
  simp only [inputRho, Iso.trans_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [reductionUniq_evaluation]
  simp only [Reconstruction.evaluationRealization, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Iso.inv_hom_id_app_assoc]
  rfl

private theorem evaluation_hom_normalized {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f}
    {operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l)}
    {left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s)}
    (d : Mates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ) (side : Bool)
    (R : Reconstruction l E (endpoint X Y side))
    (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n)
      (endpoint X Y side)).ι.map
        ((integralReductionEvaluation l Ω d E n side R).hom.app K) ≫
      (R.evaluationRealization l E (endpoint X Y side) n).hom.app K =
    (eqToIso (d.finiteScalar_eq (s := .integral E) E ⟨n + 1, Nat.succ_pos n⟩
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
      (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) side)).hom.app K ≫
        (PurCompactSupport.finiteReductionIso l E.carrier (endpoint X Y side) n).hom.app
          K.obj := by
  simp only [integralReductionEvaluation, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, Iso.symm_hom, Category.assoc, ObjectProperty.ι_obj,
    Iso.inv_hom_id_app, Category.comp_id]

private theorem integral_hom
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
    (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    (finiteTorConstructibleIntegral l E.carrier Y).ι.map
        ((transport.realizeF E).inv.app K) ≫ (left (.integral E)).hom.app K =
    (eqToIso (transport.reconstruction E false).limit).hom.app
        ((transport.F E).obj ((transport.reconstruction E true).equivalence.functor.obj K)) ≫
      (coefficientSequenceLimit l E.carrier Y).map
        ((eqToIso (transport.support E)).hom.app
          ((transport.reconstruction E true).equivalence.functor.obj K)) ≫
      ((transport.realizations E).realizationModel.push l E.carrier c.g).hom.app
          ((IntegralSystemRealization.Operations.shriek l E.carrier
            (transport.operations E) c.i).obj
            (((transport.reconstruction E true).equivalence.functor.obj K).obj)) ≫
        (PurCompactSupport.push (PurCompactSupport.completed l E.carrier) c.g).map
          (((transport.realizations E).openRealization c.i
              (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance)
              (((transport.reconstruction E true).equivalence.functor.obj K).obj)
              (transport.inputGood E K) (transport.openGood E K)).hom ≫
            ((PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
              c.i).mapDerivedCategory).map
              (inputIso l E X (transport.reconstruction E true) K).hom) := by
  apply eq_of_heq
  simpa only [eqToIso, eqToHom_app, eqToHom_map, heq_eqToHom_comp_iff,
    inputIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_inv,
    Functor.mapIso_hom] using transport.integral_system_normalized E K

private theorem support_hom
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
    (E : FieldStage.{u} l) (n : ℕ)
    (N : (sequenceProperty l E X).FullSubcategory) :
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).ι.map
        ((transport.evaluationF E n).hom.app N) ≫
      (left (.finite E ⟨n + 1, Nat.succ_pos n⟩)).hom.app
        (((transport.reconstruction E true).evaluation n).obj N) ≫
      (PurCompactSupport.finiteImageIso l E.carrier n c).hom.app
        (((transport.reconstruction E true).evaluation n).obj N).obj ≫
      (sfAmbientCompactSupportCandidate
        (Padic.coefficientExtensionRing l E.carrier (n + 1)) c).map
        ((eqToIso ((transport.reconstruction E true).evaluation_eq n)).hom.app N) =
    (eqToIso ((transport.reconstruction E false).evaluation_eq n)).hom.app
        ((transport.F E).obj N) ≫
      (coefficientSequenceDerivedEvaluation l E.carrier Y n).map
        ((eqToIso (transport.support E)).hom.app N) ≫
      (IntegralSystemRealization.supportEvaluation l E.carrier (transport.operations E) c n).hom.app
        N.obj := by
  apply eq_of_heq
  simpa only [eqToIso, eqToHom_app, eqToHom_map, heq_eqToHom_comp_iff] using
    transport.evaluation_support E n N

attribute [local irreducible] PurCompactSupport.finiteImageIso
  PurCompactSupport.finiteReductionIso Reconstruction.evaluationRealization
  integralReductionEvaluation inputIso inputRho
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf

-- The ambient comparison elaborates several dependent coefficient-stage identifications.
/-- The canonical finite evaluation intertwines the left exceptional scalar mate.
Source: Zheng, Lemma 5.22 and Proposition 5.26, reduction compatibility.
Proof: apply the faithful finite full inclusion and substitute the scalar equality
realizations and the definition of integralReductionEvaluation. The source and target
finite tensors are related by PurCompactSupport.finiteReductionIso, the unique
comparison preserving the scalar adjunction units. Substitute d.comparison_normalized:
the left path becomes the ordinary proper scalar mate followed by the open tensor map.
The recorded integral compact-support identification identifies its reduction with
the same proper/open mate. The transport.integral_system_normalized square identifies
that recorded identification with the reconstruction realization; transport.reductionF_eq
and transport.evaluation_support then identify the right path with the same map.
Cancel the finite left realization and the invertible scalar realizations. This uses
whole-system naturality before evaluation, never faithfulness of finite evaluations.
(blueprint: lem-sf-exceptional-integral-reduction-left-compatibility). -/
theorem integralReductionLeftCompatibility
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
    ∀ K : C.{u} l Ω X (.integral E),
      (Mates.q l Ω d (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
        (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).hom.app K ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
          ((integralReductionEvaluation l Ω d E n true
            (transport.reconstruction E true)).hom.app K) =
      (integralReductionEvaluation l Ω d E n false
        (transport.reconstruction E false)).hom.app ((operation (.integral E)).F.obj K) ≫
        ((transport.reconstruction E false).evaluation n).map
          ((transport.reductionF E).hom.app K) ≫
        (transport.evaluationF E n).hom.app
          ((transport.reconstruction E true).equivalence.functor.obj K) := by
  intro K
  let RX := transport.reconstruction E true
  let RY := transport.reconstruction E false
  let N := RX.equivalence.functor.obj K
  let NY := (transport.F E).obj N
  let o := transport.operations E
  let J := IntegralSystemRealization.Operations.shriek l E.carrier o c.i
  let P := IntegralSystemRealization.Operations.push l E.carrier o c.g
  let V := sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E.carrier (n + 1)) c
  let VX := coefficientSequenceDerivedEvaluation l E.carrier X n
  let VY := coefficientSequenceDerivedEvaluation l E.carrier Y n
  let TX := coefficientFiniteDerivedExtension l E.carrier X n
  let TY := coefficientFiniteDerivedExtension l E.carrier Y n
  let IX := (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) X).ι
  let IY := (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).ι
  let a := PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)
  let ha := Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩
  let δX := PurCompactSupport.finiteReductionIso l E.carrier X n
  let δY := PurCompactSupport.finiteReductionIso l E.carrier Y n
  let ιX := PurCompactSupport.finiteImageIso l E.carrier n c
  let ρX := inputRho l E X RX K
  let eX := integralReductionEvaluation l Ω d E n true RX
  let eY := integralReductionEvaluation l Ω d E n false RY
  let μ : coefficientSequenceLimit l E.carrier Y ⋙ TY ⟶ VY :=
    whiskerLeft (coefficientSequenceLimit l E.carrier Y) (RY.calculus.reductionEvaluation n).inv ≫
      whiskerRight RY.calculus.adjunction.counit VY
  have hgood : IntegralSystemRealization.Good l E.carrier Y (P.obj (J.obj N.obj)) := by
    exact IntegralSystemRealization.good_of_iso l E.carrier
      ((eqToIso (transport.support E)).app N) (sequence_good l E Y NY)
  have hproj := IntegralSystemRealization.integralSupportCounitProjection l E.carrier D hl o
    (ambientModels l E D o (transport.realizations E))
    (U := Over.mk (X ↘ Spec (.of D.k))) (V := Over.mk (Y ↘ Spec (.of D.k)))
    (Over.homMk f (by simp)) c
    (by change LocallyOfFiniteType (X ↘ Spec (.of D.k)) ∧
          QuasiCompact (X ↘ Spec (.of D.k))
        exact ⟨inferInstance, inferInstance⟩)
    (by change LocallyOfFiniteType (Y ↘ Spec (.of D.k)) ∧
          QuasiCompact (Y ↘ Spec (.of D.k))
        exact ⟨inferInstance, inferInstance⟩)
    (by change IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f
        exact ⟨inferInstance, inferInstance, inferInstance⟩)
    (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance)
    N.obj (transport.inputGood E K) (transport.openGood E K) hgood K.obj
    (inputIso l E X RX K) ρX (inputRho_normalized l E X RX K) n
  simp only [ambientModels_model, ambientModels_open] at hproj
  change TY.map
      (((transport.realizations E).realizationModel.push l E.carrier c.g).hom.app
        (J.obj N.obj) ≫
      (PurCompactSupport.push (PurCompactSupport.completed l E.carrier) c.g).map
        (((transport.realizations E).openRealization c.i
          (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance) N.obj
          (transport.inputGood E K) (transport.openGood E K)).hom ≫
        ((PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
          c.i).mapDerivedCategory).map (inputIso l E X RX K).hom)) ≫
      δY.inv.app ((PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c).obj
        K.obj) ≫ (PurCompactSupport.comparison a c).app K.obj ≫
      ιX.hom.app ((pbcDerivedExtend (a.map X)).obj K.obj) ≫
      V.map (δX.hom.app K.obj) =
    ((IntegralSystemRealization.calculus l E.carrier Y).reductionEvaluation n).inv.app
      ((coefficientSequenceLimit l E.carrier Y).obj (P.obj (J.obj N.obj))) ≫
      VY.map ((IntegralSystemRealization.calculus l E.carrier Y).adjunction.counit.app
        (P.obj (J.obj N.obj))) ≫
      (IntegralSystemRealization.supportEvaluation l E.carrier o c n).hom.app N.obj ≫
      V.map (VX.map ρX.hom ≫
        ((IntegralSystemRealization.calculus l E.carrier X).reductionEvaluation n).hom.app
          K.obj) at hproj
  have hx := inputRho_evaluation l E X RX K n
  have hc0 := counit_independent l E Y
    (IntegralSystemRealization.calculus l E.carrier Y) RY.calculus (P.obj (J.obj N.obj)) n
  have hproj' := hproj.trans (congrArg
    (fun z ↦ ((IntegralSystemRealization.calculus l E.carrier Y).reductionEvaluation n).inv.app
        ((coefficientSequenceLimit l E.carrier Y).obj (P.obj (J.obj N.obj))) ≫
      VY.map ((IntegralSystemRealization.calculus l E.carrier Y).adjunction.counit.app
        (P.obj (J.obj N.obj))) ≫
      (IntegralSystemRealization.supportEvaluation l E.carrier o c n).hom.app N.obj ≫
      V.map z) hx)
  have hproj'' := hproj'.trans ((reassoc_of% hc0) (
    (IntegralSystemRealization.supportEvaluation l E.carrier o c n).hom.app N.obj ≫
    V.map ((eqToIso (RX.evaluation_eq n)).inv.app N ≫
      (RX.evaluationRealization l E X n).hom.app K)))
  clear hproj hproj'
  have hproj := hproj''
  have hμ : TY.map ((coefficientSequenceLimit l E.carrier Y).map
        ((eqToIso (transport.support E)).hom.app N)) ≫ μ.app (P.obj (J.obj N.obj)) =
      μ.app NY.obj ≫ VY.map ((eqToIso (transport.support E)).hom.app N) :=
    μ.naturality ((eqToIso (transport.support E)).hom.app N)
  dsimp only [μ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hμ
  simp only [Category.assoc] at hμ
  have hi := integral_hom l Ω D hl c operation left transport E K
  have hs := support_hom l Ω D hl c operation left transport E n N
  have hc := reduction_coordinates l E Y RY n
    ((operation (.integral E)).F.obj K) NY ((transport.realizeF E).hom.app K)
  rw [← transport.reductionF_eq E K] at hc
  have hs' := congrArg (fun z ↦ z ≫ V.map
    ((eqToIso (RX.evaluation_eq n)).inv.app N ≫
      (RX.evaluationRealization l E X n).hom.app K)) hs
  simp only [Category.assoc] at hs'
  have hxCancel : V.map ((eqToIso (RX.evaluation_eq n)).hom.app N) ≫
      V.map ((eqToIso (RX.evaluation_eq n)).inv.app N ≫
        (RX.evaluationRealization l E X n).hom.app K) =
      V.map ((RX.evaluationRealization l E X n).hom.app K) := by
    rw [← V.map_comp, Iso.hom_inv_id_app_assoc]
  erw [hxCancel] at hs'
  simp only [Functor.map_comp] at hs'
  have hn := d.comparison_normalized (s := .integral E)
    (t := .finite E ⟨n + 1, Nat.succ_pos n⟩) a ha K
  have hSX := d.finiteScalar_normalized (s := .integral E) E
    ⟨n + 1, Nat.succ_pos n⟩ a ha true
  have hSY := d.finiteScalar_normalized (s := .integral E) E
    ⟨n + 1, Nat.succ_pos n⟩ a ha false
  simp only [hSX, hSY] at hn
  let py := (eqToIso (d.finiteScalar_eq (s := .integral E) E
    ⟨n + 1, Nat.succ_pos n⟩ a ha false)).hom.app ((operation (.integral E)).F.obj K)
  have hp'' := reduction_comparison_pasting δY
    ((finiteTorConstructibleIntegral l E.carrier Y).ι.mapIso ((transport.realizeF E).app K))
    py hi hproj hμ
  simp only [Functor.map_comp] at hp''
  have hr := congrArg (fun z ↦
    IY.map (eY.hom.app ((operation (.integral E)).F.obj K)) ≫ z ≫
      VY.map ((eqToIso (transport.support E)).hom.app N) ≫
      (IntegralSystemRealization.supportEvaluation l E.carrier o c n).hom.app N.obj ≫
      V.map ((eqToIso (RX.evaluation_eq n)).inv.app N ≫
        (RX.evaluationRealization l E X n).hom.app K)) hc
  simp only [Category.assoc] at hr
  erw [reassoc_of% (evaluation_hom_normalized l Ω d E n false RY
    ((operation (.integral E)).F.obj K))] at hr
  simp only [Functor.map_comp, Functor.comp_map] at hr
  apply IY.map_injective
  apply (cancel_mono ((left (.finite E ⟨n + 1, Nat.succ_pos n⟩)).hom.app
    ((RX.evaluation n).obj N) ≫ ιX.hom.app ((RX.evaluation n).obj N).obj ≫
      V.map ((RX.evaluationRealization l E X n).hom.app K))).1
  simp only [Functor.map_comp, Category.assoc]
  erw [(left (.finite E ⟨n + 1, Nat.succ_pos n⟩)).hom.naturality_assoc
    (eX.hom.app K)]
  erw [ιX.hom.naturality_assoc (IX.map (eX.hom.app K))]
  rw [← V.map_comp]
  erw [evaluation_hom_normalized l Ω d E n true RX K]
  simp only [V.map_comp]
  erw [← ιX.hom.naturality_assoc
    ((eqToIso (d.finiteScalar_eq (s := .integral E) E ⟨n + 1, Nat.succ_pos n⟩
      a ha true)).hom.app K)]
  erw [reassoc_of% hn]
  erw [hs']
  erw [hr]
  exact hp''

end WeilConjectures.ExceptionalIntegralScalar
