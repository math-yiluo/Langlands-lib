/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonReductionPresentationShifts
public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonRoosBridgeShifts
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.PoincareDuality.Integral.IntegralPullbackStrictFiniteComponent

/-! # Shift compatibility on the finite pullback generators -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible]
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  CategoryTheory.NatIso.mapHomologicalComplex CategoryTheory.NatTrans.mapHomologicalComplex
  HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  WeilConjectures.integralOperationsPullbackTowerFunctor
  WeilConjectures.integralOperationsPullbackLevel
  WeilConjectures.integralOperationsRestrict
  WeilConjectures.integralComparisonSequenceRoosFunctor
  WeilConjectures.integralOperationsPullbackComplexFunctor
  CochainComplex.HomComplex.Cocycle
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section RoosCoordinates

attribute [local implicit_reducible] integralOperationsRoos integralOperationsRoosFunctor

@[reassoc] private theorem roos_inl {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] {C D : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ D) (j : ℤ) :
    (CochainComplex.mappingCocone.inl (scalarRoosBoundary C)).v j j (by omega) ≫
        (integralOperationsRoosFunctor.map a).f j =
      (Limits.Pi.map (fun n ↦ a.app (op n))).f j ≫
        (CochainComplex.mappingCocone.inl (scalarRoosBoundary D)).v j j (by omega) := by
  exact SignedCoconeShift.coconeMap_inl _ _
    (Arrow.homMk _ _ (integralOperationsRoos_square a).symm) j

@[reassoc] private theorem roos_inr {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] {C D : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ D)
    (i j : ℤ) (h : i + 1 = j) :
    (CochainComplex.mappingCocone.inr (scalarRoosBoundary C)).1.v i j h ≫
        (integralOperationsRoosFunctor.map a).f j =
      (Limits.Pi.map (fun n ↦ a.app (op n))).f i ≫
        (CochainComplex.mappingCocone.inr (scalarRoosBoundary D)).1.v i j h := by
  exact SignedCoconeShift.coconeMap_inr _ _
    (Arrow.homMk _ _ (integralOperationsRoos_square a).symm) i j h

private theorem productIso_pi {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] {C D : ℕ → CochainComplex A ℤ} (m : ℤ)
    (e : ∀ n, C n ≅ (D n)⟦m⟧) (n : ℕ) :
    (Limits.Pi.mapIso e ≪≫
        (PreservesProduct.iso (shiftFunctor (CochainComplex A ℤ) m) D).symm).hom ≫
        (Limits.Pi.π D n)⟦m⟧' = Limits.Pi.π C n ≫ (e n).hom := by
  rw [← piComparison_comp_π (shiftFunctor (CochainComplex A ℤ) m) D n]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← PreservesProduct.iso_hom, Iso.inv_hom_id_assoc]
  exact Limits.Pi.mapIso_hom_π e n

private theorem product_shift_square {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] (m : ℤ)
    {C D Cm Dm T : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (q : C ⟶ D) (qm : Cm ⟶ Dm) (a : Cm ⟶ T)
    (p : (∏ᶜ fun n : ℕ ↦ Dm.obj (op n)) ⟶ (∏ᶜ fun n : ℕ ↦ D.obj (op n))⟦m⟧)
    (r : (∏ᶜ fun n : ℕ ↦ T.obj (op n)) ⟶ (∏ᶜ fun n : ℕ ↦ C.obj (op n))⟦m⟧)
    (s : ∀ n : ℕ, Dm.obj (op n) ⟶ (D.obj (op n))⟦m⟧)
    (t : ∀ n : ℕ, T.obj (op n) ⟶ (C.obj (op n))⟦m⟧)
    (hp : ∀ n, p ≫ (Limits.Pi.π (fun n ↦ D.obj (op n)) n)⟦m⟧' =
      Limits.Pi.π (fun n ↦ Dm.obj (op n)) n ≫ s n)
    (hr : ∀ n, r ≫ (Limits.Pi.π (fun n ↦ C.obj (op n)) n)⟦m⟧' =
      Limits.Pi.π (fun n ↦ T.obj (op n)) n ≫ t n)
    (h : ∀ n, qm.app (op n) ≫ s n = a.app (op n) ≫ t n ≫ (q.app (op n))⟦m⟧') :
    Limits.Pi.map (fun n ↦ qm.app (op n)) ≫ p =
      Limits.Pi.map (fun n ↦ a.app (op n)) ≫ r ≫
        (Limits.Pi.map (fun n ↦ q.app (op n)))⟦m⟧' := by
  apply ProductShift.productShift_hom_ext
    (fun n ↦ (evaluation ℕᵒᵖ (CochainComplex A ℤ)).obj (op n)) D m
  intro n
  simp only [Category.assoc, ← Functor.map_comp]
  erw [hp, ← Category.assoc, Limits.Pi.map_π, Category.assoc]
  erw [Limits.Pi.map_π]
  rw [(shiftFunctor (CochainComplex A ℤ) m).map_comp]
  rw [← Category.assoc _ _ ((q.app (op n))⟦m⟧'), hr]
  simp only [Category.assoc]
  rw [Limits.Pi.map_π_assoc, h]

private theorem roos_square {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] (m : ℤ)
    {C D Cm Dm T : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (q : C ⟶ D) (qm : Cm ⟶ Dm) (a : Cm ⟶ T)
    (s : integralOperationsRoosFunctor.obj Dm ⟶ (integralOperationsRoosFunctor.obj D)⟦m⟧)
    (t : integralOperationsRoosFunctor.obj T ⟶ (integralOperationsRoosFunctor.obj C)⟦m⟧)
    (p : (∏ᶜ fun n : ℕ ↦ Dm.obj (op n)) ⟶ (∏ᶜ fun n : ℕ ↦ D.obj (op n))⟦m⟧)
    (r : (∏ᶜ fun n : ℕ ↦ T.obj (op n)) ⟶ (∏ᶜ fun n : ℕ ↦ C.obj (op n))⟦m⟧)
    (hp : Limits.Pi.map (fun n ↦ qm.app (op n)) ≫ p =
      Limits.Pi.map (fun n ↦ a.app (op n)) ≫ r ≫
        (Limits.Pi.map (fun n ↦ q.app (op n)))⟦m⟧')
    (hs₁ : ∀ j : ℤ,
      (CochainComplex.mappingCocone.inl (scalarRoosBoundary Dm)).v j j (by omega) ≫ s.f j =
        p.f j ≫ (CochainComplex.mappingCocone.inl (scalarRoosBoundary D)).v
          (j + m) (j + m) (by omega))
    (hs₂ : ∀ (i j : ℤ) (h : i + 1 = j),
      (CochainComplex.mappingCocone.inr (scalarRoosBoundary Dm)).1.v i j h ≫ s.f j =
        m.negOnePow • (p.f i ≫
          (CochainComplex.mappingCocone.inr (scalarRoosBoundary D)).1.v
            (i + m) (j + m) (by omega)))
    (ht₁ : ∀ j : ℤ,
      (CochainComplex.mappingCocone.inl (scalarRoosBoundary T)).v j j (by omega) ≫ t.f j =
        r.f j ≫ (CochainComplex.mappingCocone.inl (scalarRoosBoundary C)).v
          (j + m) (j + m) (by omega))
    (ht₂ : ∀ (i j : ℤ) (h : i + 1 = j),
      (CochainComplex.mappingCocone.inr (scalarRoosBoundary T)).1.v i j h ≫ t.f j =
        m.negOnePow • (r.f i ≫
          (CochainComplex.mappingCocone.inr (scalarRoosBoundary C)).1.v
            (i + m) (j + m) (by omega))) :
    integralOperationsRoosFunctor.map qm ≫ s =
      integralOperationsRoosFunctor.map a ≫ t ≫
        (integralOperationsRoosFunctor.map q)⟦m⟧' := by
  apply HomologicalComplex.hom_ext
  intro j
  change (integralOperationsRoosFunctor.map qm).f j ≫ s.f j =
    (integralOperationsRoosFunctor.map a).f j ≫ t.f j ≫
      (integralOperationsRoosFunctor.map q).f (j + m)
  apply SignedCoconeShift.cocone_ext_from
  · rw [roos_inl_assoc, hs₁, roos_inl_assoc]
    rw [← Category.assoc _ (t.f j), ht₁]
    simp only [Category.assoc]
    rw [roos_inl q (j + m)]
    have h := congrArg (fun z ↦ z.f j) hp
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f'] at h
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
      (CochainComplex.mappingCocone.inl (scalarRoosBoundary D)).v
        (j + m) (j + m) (by omega)) h
  · rw [roos_inr_assoc, hs₂, roos_inr_assoc]
    rw [← Category.assoc _ (t.f j), ht₂]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc]
    rw [roos_inr q (j - 1 + m) (j + m) (by omega)]
    have h := congrArg (fun z ↦ z.f (j - 1)) hp
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f'] at h
    simpa only [Category.assoc] using congrArg (fun z ↦ m.negOnePow • (z ≫
      (CochainComplex.mappingCocone.inr (scalarRoosBoundary D)).1.v
        (j - 1 + m) (j + m) (by omega))) h

end RoosCoordinates

/-- The finite tensor-unit generator equation in the existing pullback normalization. -/
def IntegralComparisonPullbackGeneratorEquation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (q : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj
          C)).asFunctor ≅ (integralOperationsPullbackTowerFunctor l E f).obj P) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (C.X i).val.obj (op (n, U))),
    ((q.hom.app (op n)).f i).val.app (op ((Scheme.proEtaleBaseChange f).obj U))
      (integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E f).obj (C.X i)) n
        (op ((Scheme.proEtaleBaseChange f).obj U))
        (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
      integralOperationsPullbackGenerator l E f n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) U
        (((κ n).hom.f i).val.app (op U)
          (coefficientEvaluationSection l E Y (C.X i) n (op U) x))

/-- Finite generator normalization fixes the signed Roos shift square.

Source: Stacks 03EL, 014E and 0941; step 2 and the signed coordinate calculation
in step 4 of lem-sf-integral-pullback-realization-shifts.
(blueprint: lem-sf-integral-pullback-generator-shifts).

Proof: conjugate q shifted by m by the ordinary termwise restriction and
pullback shift isomorphisms. At coefficient level n in degree j, its value
on the pullback unit generator is the old value in degree j+m, with kappa
conjugated by exactly the finite termwise shifts. Thus it has the same
specified generator values as q_m. The inverse-image adjunction and the
universal property of sheafification show equality on every finite module;
restriction along the quotient projection detects equality. Degreewise and
levelwise extensionality identify the entire strict tower maps, including
all transitions. The induced product square commutes after each projection.
Apply the two mapping-cocone coordinate equations: the first coordinate has
this product square and the second has the same square multiplied by
(-1)^m. The two cocone inclusions jointly determine the chain map, proving
the stated equality. No localization, realization model, reduction
adjunction or K-flatness is needed for this calculation. For m=0 both
comparisons are identity; for m=1 and m=-1 the second coordinate changes
sign. Zero complexes and zero finite quotients obey the same formulas. -/
theorem integralComparisonPullbackGenerator_shift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (m : ℤ)
    (q : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj
          C)).asFunctor ≅ (integralOperationsPullbackTowerFunctor l E f).obj P)
    (qm : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj
          (C⟦m⟧))).asFunctor ≅
            (integralOperationsPullbackTowerFunctor l E f).obj (P⟦m⟧))
    (hq : IntegralComparisonPullbackGeneratorEquation l E f P C κ q)
    (hqm : IntegralComparisonPullbackGeneratorEquation l E f (P⟦m⟧) (C⟦m⟧)
      (integralComparisonShiftedFiniteIso l E Y P C κ m) qm)
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (hc : IntegralCompletedComparison.ShiftCoordinates l E f c) :
    letI := c
    letI := integralComparisonSequenceRoosShift l E X
    integralOperationsRoosFunctor.map qm.hom ≫
        ((integralOperationsPullbackComplexFunctor l E f).commShiftIso m).hom.app P =
      (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ⋙
        integralComparisonSequenceRoosFunctor l E X).commShiftIso m).hom.app C ≫
          (integralOperationsRoosFunctor.map q.hom)⟦m⟧' := by
  have hlevel (n : ℕ) (i : ℤ) :
      (qm.hom.app (op n)).f i = (q.hom.app (op n)).f (i + m) := by
    have h := congrArg (fun z ↦ z.f (i + m))
      (strictComponent_generators l E f P C κ q hq n)
    have hm := congrArg (fun z ↦ z.f i)
      (strictComponent_generators l E f (P⟦m⟧) (C⟦m⟧)
        (integralComparisonShiftedFiniteIso l E Y P C κ m) qm hqm n)
    dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatIso.mapHomologicalComplex_hom_app_f] at h hm
    simp only [integralComparisonShiftedFiniteIso, Iso.trans_hom, Iso.app_hom,
      Iso.symm_hom, Functor.mapIso_hom] at hm
    exact hm.trans h.symm
  let B := (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)
  let R := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
  let K := HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (T := ℕᵒᵖ) (V := scalarReductionSource l E X) (c := ComplexShape.up ℤ)
  let D := R.obj (B.obj C)
  let a : R.obj (B.obj (C⟦m⟧)) ⟶ D⟦m⟧ :=
    R.map ((B.commShiftIso m).hom.app C) ≫ (R.commShiftIso m).hom.app (B.obj C)
  have ha (n : ℕᵒᵖ) (i : ℤ) : (a.f i).app n = 𝟙 _ := by
    change ((coefficientSequenceRestriction l E X).map (𝟙 _)).app n ≫ 𝟙 _ = _
    rw [(coefficientSequenceRestriction l E X).map_id]
    exact Category.id_comp _
  let : ∀ n : ℕ, (RoosShift.levelFunctor K n).CommShift ℤ := fun n ↦ by
    change (((evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n)).mapHomologicalComplex
      (.up ℤ)).CommShift ℤ
    infer_instance
  let : ∀ n : ℕ, NatTrans.CommShift (RoosShift.transition K n) ℤ := fun n ↦ by
    constructor
    intro r
    apply NatTrans.ext
    funext Z
    apply HomologicalComplex.hom_ext
    intro i
    change 𝟙 _ ≫ (Z.X (i + r)).map (homOfLE (Nat.le_succ n)).op =
      (Z.X (i + r)).map (homOfLE (Nat.le_succ n)).op ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  let := RoosShift.commShift K
  let := c
  let := integralComparisonSequenceRoosShift l E X
  have hsource :
      (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ⋙
        integralComparisonSequenceRoosFunctor l E X).commShiftIso m).hom.app C =
      integralOperationsRoosFunctor.map (K.map a) ≫
        ((K ⋙ integralOperationsRoosFunctor).commShiftIso m).hom.app D := by
    dsimp only [integralComparisonSequenceRoosFunctor, integralComparisonSequenceRoosShift]
    simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, a,
      Functor.map_comp, Category.assoc]
    rfl
  have hproduct :
      Limits.Pi.map (fun n ↦ qm.hom.app (op n)) ≫
          (IntegralCompletedComparison.productShift l E f P m).hom =
        Limits.Pi.map (fun n ↦ (K.map a).app (op n)) ≫
          (ProductShift.productShiftIso (RoosShift.levelFunctor K) D m).hom ≫
            (Limits.Pi.map (fun n ↦ q.hom.app (op n)))⟦m⟧' := by
    refine product_shift_square m q.hom qm.hom (K.map a) _ _
      (fun n ↦ (IntegralCompletedComparison.levelShift l E f P m n).hom)
      (fun n ↦ ((RoosShift.levelFunctor K n).commShiftIso m).hom.app D) ?_ ?_ ?_
    · intro n
      unfold IntegralCompletedComparison.productShift
      exact productIso_pi m (fun n ↦ IntegralCompletedComparison.levelShift l E f P m n) n
    · exact ProductShift.productShiftIso_π (RoosShift.levelFunctor K) D m
    · intro n
      apply HomologicalComplex.hom_ext
      intro i
      simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
      change (qm.hom.app (op n)).f i ≫ 𝟙 _ =
        (a.f i).app (op n) ≫ 𝟙 _ ≫ (q.hom.app (op n)).f (i + m)
      erw [ha]
      erw [Category.comp_id, Category.id_comp, Category.id_comp]
      exact hlevel n i
  erw [hsource, Category.assoc]
  refine roos_square m q.hom qm.hom (K.map a) _ _ _ _ hproduct ?_ ?_ ?_ ?_
  · intro j
    have H := (hc P m).1 j
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv] at H
    erw [Category.comp_id] at H
    exact H
  · intro i j h
    have H := (hc P m).2 i j h
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv] at H
    erw [Category.comp_id] at H
    exact H
  · intro j
    have H := RoosShift.commShift_inl K D m j
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv] at H
    erw [Category.comp_id] at H
    exact H
  · intro i j h
    have H := RoosShift.commShift_inr K D m i j h
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv] at H
    erw [Category.comp_id] at H
    exact H

end WeilConjectures
