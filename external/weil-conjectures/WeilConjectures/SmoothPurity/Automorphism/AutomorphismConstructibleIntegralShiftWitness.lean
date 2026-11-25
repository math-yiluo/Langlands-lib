/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismConstructibleIntegralShiftData
import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonPullbackRealizationShifts
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! Auxiliary witness for the normalized integral shift square.
(blueprint: lem-sf-automorphism-constructible-stage-equivalence) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

-- Lift the ambient shift through the full constructible inclusion.
@[instance_reducible]
private noncomputable def restrictShift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (d : (integralDerivedPullback l E f).CommShift ℤ) :
    (constructibleIntegralPullback l E f).CommShift ℤ :=
  let := d
  Functor.CommShift.ofComp
    (F := constructibleIntegralPullback l E f) (G := (sfIntegralConstructible l E Y).ι)
    (Iso.refl ((sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E f)) ℤ

attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι in
private theorem restrictShift_hom
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (d : (integralDerivedPullback l E f).CommShift ℤ)
    (K : sfIntegralConstructibleCategory l E X) (r : ℤ) :
    HEq (((constructibleIntegralPullback l E f).commShiftIso
      (self := restrictShift l E f d) r).hom.app K).hom
      (((integralDerivedPullback l E f).commShiftIso (self := d) r).hom.app K.obj) := by
  change HEq ((sfIntegralConstructible l E Y).ι.map
    ((Functor.CommShift.OfComp.iso
      (F := constructibleIntegralPullback l E f) (G := (sfIntegralConstructible l E Y).ι)
      (Iso.refl ((sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E f)) r).hom.app K))
    (((integralDerivedPullback l E f).commShiftIso (self := d) r).hom.app K.obj)
  erw [Functor.CommShift.OfComp.map_iso_hom_app]
  simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.commShiftIso_comp_hom_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]
  erw [Category.id_comp]
  rfl

private theorem limit_tri
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    let := integralComparisonLimitShift l E X
    (coefficientSequenceLimit l E X).IsTriangulated := by
  unfold integralComparisonLimitShift coefficientSequenceLimit
    coefficientSequenceDerivedRestriction coefficientConstantTowerLimit
  infer_instance

-- The normalized realization identifies pullback with a composite of exact functors.
private theorem derived_tri
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (d : (integralDerivedPullback l E f).CommShift ℤ)
    (hc : IntegralCompletedComparison.ShiftCoordinates l E f c)
    (hd : IntegralCompletedComparison.ShiftDescent l E f c d) :
    let := d
    (integralDerivedPullback l E f).IsTriangulated := by
  let := d
  let := integralComparisonLimitShift l E Y
  let := integralComparisonLimitShift l E X
  let := integralComparisonReductionShift l E X ((C.coefficient E).system X)
  let := integralComparisonSequencePullbackShift l E f
  have := limit_tri l E Y
  have := limit_tri l E X
  have : ((C.coefficient E).system X).adjunction.CommShift ℤ :=
    ((C.coefficient E).system X).adjunction.commShift_of_rightAdjoint ℤ
  have : ((C.coefficient E).system X).reduction.IsTriangulated :=
    ((C.coefficient E).system X).adjunction.isTriangulated_leftAdjoint
  have : (integralComparisonDerivedSequencePullback l E f).IsTriangulated := by
    unfold integralComparisonDerivedSequencePullback
    infer_instance
  have : NatTrans.CommShift ((C.coefficient E).pullback f).realization.hom ℤ :=
    integralComparisonPullbackRealization_commShift l E f
      ((C.coefficient E).system X) ((C.coefficient E).roos Y)
      ((C.coefficient E).pullback f) c hc d hd
  exact (Functor.isTriangulated_iff_of_iso ((C.coefficient E).pullback f).realization).2
    inferInstance

private theorem restrict_tri
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (d : (integralDerivedPullback l E f).CommShift ℤ)
    (hc : IntegralCompletedComparison.ShiftCoordinates l E f c)
    (hd : IntegralCompletedComparison.ShiftDescent l E f c d) :
    let := restrictShift l E f d
    (constructibleIntegralPullback l E f).IsTriangulated := by
  let := d
  let := restrictShift l E f d
  have := derived_tri l E C f c d hc hd
  let e : constructibleIntegralPullback l E f ⋙ (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E f := Iso.refl _
  have : NatTrans.CommShift e.hom ℤ :=
    Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).2 inferInstance

private theorem reduced_realization_commShift
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ B) (H : A ⥤ C) (T : C ⥤ D) (L : D ⥤ B) (R : B ⥤ D)
    [F.CommShift ℤ] [H.CommShift ℤ] [T.CommShift ℤ]
    [L.CommShift ℤ] [R.CommShift ℤ]
    (e : F ⟶ H ⋙ T ⋙ L) (c : L ⋙ R ⟶ 𝟭 D)
    [NatTrans.CommShift e ℤ] [NatTrans.CommShift c ℤ] :
    NatTrans.CommShift (show F ⋙ R ⟶ H ⋙ T from
      Functor.whiskerRight e R ≫ Functor.whiskerLeft (H ⋙ T) c) ℤ := by
  let t := Functor.whiskerRight e R ≫ (Functor.associator H (T ⋙ L) R).hom ≫
    Functor.whiskerLeft H ((Functor.associator T L R).hom ≫
      Functor.whiskerLeft T c ≫ T.rightUnitor.hom)
  have ht : NatTrans.CommShift t ℤ := by dsimp [t]; infer_instance
  have he : t = (show F ⋙ R ⟶ H ⋙ T from
      Functor.whiskerRight e R ≫ Functor.whiskerLeft (H ⋙ T) c) := by
    ext X
    simp [t]
  exact he ▸ ht

-- Paste the whole-system comparisons before restricting to constructible objects.
private theorem composition_shift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l)
    (a : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y),
      (integralOperationsPullbackComplexFunctor l E g).CommShift ℤ)
    (d : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), (integralDerivedPullback l E g).CommShift ℤ)
    (ha : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y),
      IntegralCompletedComparison.ShiftCoordinates l E g (a g))
    (hd : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y),
      IntegralCompletedComparison.ShiftDescent l E g (a g) (d g))
    {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) :
    letI := restrictShift l E (h ≫ k) (d (h ≫ k))
    letI := restrictShift l E h (d h)
    letI := restrictShift l E k (d k)
    ∃ c : constructibleIntegralPullback l E (h ≫ k) ≅
        constructibleIntegralPullback l E k ⋙ constructibleIntegralPullback l E h,
      (∀ K, (c.hom.app K).hom = (integralComparisonComposition l E C h k K).hom) ∧
      NatTrans.CommShift c.hom ℤ := by
  let := d h
  let := d k
  let := d (h ≫ k)
  let := restrictShift l E (h ≫ k) (d (h ≫ k))
  let := restrictShift l E h (d h)
  let := restrictShift l E k (d k)
  let {X Y : Scheme.{u}} (g : X ⟶ Y) :
      (integralComparisonDerivedSequencePullback l E g).CommShift ℤ :=
    integralComparisonSequencePullbackShift l E g
  let (X : Scheme.{u}) : (coefficientSequenceLimit l E X).CommShift ℤ :=
    integralComparisonLimitShift l E X
  let (X : Scheme.{u}) : ((C.coefficient E).system X).reduction.CommShift ℤ :=
    integralComparisonReductionShift l E X ((C.coefficient E).system X)
  have hre {X Y : Scheme.{u}} (g : X ⟶ Y) :
      letI := d g
      NatTrans.CommShift ((C.coefficient E).pullback g).realization.hom ℤ :=
    integralComparisonPullbackRealization_commShift l E g
      ((C.coefficient E).system Y) ((C.coefficient E).roos X)
      ((C.coefficient E).pullback g) (a g) (ha g) (d g) (hd g)
  have := hre h
  have := hre k
  have := hre (h ≫ k)
  have hAdj : ((C.coefficient E).system W).adjunction.CommShift ℤ :=
    ((C.coefficient E).system W).adjunction.commShift_of_rightAdjoint ℤ
  have : NatTrans.CommShift ((C.coefficient E).system W).adjunction.counit ℤ :=
    hAdj.commShift_counit
  have : NatTrans.CommShift
      (integralComparisonPullbackCounit l E k
        ((C.coefficient E).system V) ((C.coefficient E).system W)
        ((C.coefficient E).roos W) ((C.coefficient E).pullback k)) ℤ := by
    unfold integralComparisonPullbackCounit
    exact reduced_realization_commShift _ _ _ _ _ _ _
  have : NatTrans.CommShift (integralComparisonSystemComposition l E h k).hom ℤ := by
    unfold integralComparisonSystemComposition integralComparisonDerivedSequencePullback
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    have : NatTrans.CommShift (Functor.mapDerivedCategoryNatIso
        (integralComparisonSequenceComposition l E h k)).hom ℤ := inferInstance
    have : NatTrans.CommShift ((integralComparisonSequencePullback l E k).mapDerivedCategoryCompIso
        (integralComparisonSequencePullback l E h)).inv ℤ := inferInstance
    exact NatTrans.CommShift.comp _ _ _
  let P := sfIntegralConstructible l E V
  let U := integralComparisonDerivedSequencePullback l E h
  let L := coefficientSequenceLimit l E Z
  let β : (P.ι ⋙ integralDerivedPullback l E k) ⋙ ((C.coefficient E).system W).reduction ≅
      (P.ι ⋙ ((C.coefficient E).system V).reduction) ⋙
        integralComparisonDerivedSequencePullback l E k :=
    NatIso.ofComponents (fun K ↦
      @asIso _ _ _ _ _ ((C.coefficient E).effective k K)) (fun {K J} r ↦ by
        exact (integralComparisonPullbackCounit l E k
          ((C.coefficient E).system V) ((C.coefficient E).system W)
          ((C.coefficient E).roos W) ((C.coefficient E).pullback k)).naturality r.hom)
  have : NatTrans.CommShift β.hom ℤ := by
    let t := (Functor.associator P.ι (integralDerivedPullback l E k)
      ((C.coefficient E).system W).reduction).hom ≫
      Functor.whiskerLeft P.ι (integralComparisonPullbackCounit l E k
        ((C.coefficient E).system V) ((C.coefficient E).system W)
        ((C.coefficient E).roos W) ((C.coefficient E).pullback k)) ≫
      (Functor.associator P.ι ((C.coefficient E).system V).reduction
        (integralComparisonDerivedSequencePullback l E k)).inv
    have ht : NatTrans.CommShift t ℤ := by dsimp [t]; infer_instance
    have he : β.hom = t := by ext K; simp [β, t]
    rw [he]
    exact ht
  let η : (P.ι ⋙ integralDerivedPullback l E k) ⋙ integralDerivedPullback l E h ≅
      (P.ι ⋙ ((C.coefficient E).system V).reduction) ⋙
        (integralComparisonDerivedSequencePullback l E k ⋙ (U ⋙ L)) :=
    Functor.isoWhiskerLeft (P.ι ⋙ integralDerivedPullback l E k)
        ((C.coefficient E).pullback h).realization ≪≫
      (Functor.associator (P.ι ⋙ integralDerivedPullback l E k)
        ((C.coefficient E).system W).reduction (U ⋙ L)).symm ≪≫
      Functor.isoWhiskerRight β (U ⋙ L) ≪≫
      Functor.associator (P.ι ⋙ ((C.coefficient E).system V).reduction)
        (integralComparisonDerivedSequencePullback l E k) (U ⋙ L)
  have : NatTrans.CommShift η.hom ℤ := by dsimp [η, U, L]; infer_instance
  let γ : P.ι ⋙ integralDerivedPullback l E (h ≫ k) ≅
      P.ι ⋙ (integralDerivedPullback l E k ⋙ integralDerivedPullback l E h) :=
    Functor.isoWhiskerLeft P.ι ((C.coefficient E).pullback (h ≫ k)).realization ≪≫
      (Functor.associator P.ι ((C.coefficient E).system V).reduction
        (integralComparisonDerivedSequencePullback l E (h ≫ k) ⋙ L)).symm ≪≫
      Functor.isoWhiskerLeft (P.ι ⋙ ((C.coefficient E).system V).reduction)
        (Functor.isoWhiskerRight (integralComparisonSystemComposition l E h k) L ≪≫
          Functor.associator (integralComparisonDerivedSequencePullback l E k) U L) ≪≫
      η.symm ≪≫ Functor.associator P.ι (integralDerivedPullback l E k)
        (integralDerivedPullback l E h)
  have : NatTrans.CommShift γ.hom ℤ := by dsimp [γ, U, L]; infer_instance
  let c : constructibleIntegralPullback l E (h ≫ k) ≅
      constructibleIntegralPullback l E k ⋙ constructibleIntegralPullback l E h :=
    NatIso.ofComponents (fun K ↦ (sfIntegralConstructible l E Z).isoMk (γ.app K))
      (fun {K J} r ↦ by
        apply ObjectProperty.hom_ext
        exact γ.hom.naturality r)
  have hc (K : sfIntegralConstructibleCategory l E V) :
      (c.hom.app K).hom = (integralComparisonComposition l E C h k K).hom := by
    simp [c, γ, η, β, U, L, integralComparisonComposition, integralComparisonEta]
  refine ⟨c, hc, ?_⟩
  let rj (X Y : Scheme.{u}) (g : X ⟶ Y)
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] :
      constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E g := Iso.refl _
  have hr (X Y : Scheme.{u}) (g : X ⟶ Y)
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] :
      letI := d g
      letI := restrictShift l E g (d g)
      NatTrans.CommShift (rj X Y g).hom ℤ :=
    Functor.CommShift.ofComp_compatibility (rj X Y g) ℤ
  have := hr Z V (h ≫ k)
  have := hr Z W h
  have := hr W V k
  let e₁ := rj Z V (h ≫ k)
  let e₂ := Functor.associator (constructibleIntegralPullback l E k)
      (constructibleIntegralPullback l E h) (sfIntegralConstructible l E Z).ι ≪≫
    Functor.isoWhiskerLeft (constructibleIntegralPullback l E k) (rj Z W h) ≪≫
    (Functor.associator (constructibleIntegralPullback l E k)
      (sfIntegralConstructible l E W).ι (integralDerivedPullback l E h)).symm ≪≫
    Functor.isoWhiskerRight (rj W V k) (integralDerivedPullback l E h) ≪≫
    Functor.associator P.ι (integralDerivedPullback l E k) (integralDerivedPullback l E h)
  have : NatTrans.CommShift e₁.hom ℤ := by dsimp [e₁]; infer_instance
  have : NatTrans.CommShift e₂.hom ℤ := by dsimp [e₂]; infer_instance
  have he : Functor.whiskerRight c.hom (sfIntegralConstructible l E Z).ι =
      (e₁ ≪≫ γ ≪≫ e₂.symm).hom := by
    ext K
    simp [c, e₁, e₂, rj]
  have : NatTrans.CommShift
      (Functor.whiskerRight c.hom (sfIntegralConstructible l E Z).ι) ℤ := by
    rw [he]
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight c.hom (sfIntegralConstructible l E Z).ι

-- The unchanged statement names instance binders that occur only through typeclass inference.
set_option linter.unusedVariables false in
/-- The normalized integral shift data and square shift compatibility.
Source: the canonical shift paragraph of the Weil-structures proof
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
The proof chooses the existing normalized signed shifts, restricts them through
the full constructible inclusion, and transfers exactness through the normalized
realization. The prescribed composition comparisons commute with these shifts
because their realization, reduction-counit, and sequence-composition factors do.
Pasting the two comparisons with equality transport gives the prescribed square. -/
theorem automorphismConstructibleStage_integral_shift_witness
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom)
    (b : constructibleIntegralPullback l E f ⋙
      constructibleIntegralPullback l E eY.asIso.hom ≅
      constructibleIntegralPullback l E eX.asIso.hom ⋙
        constructibleIntegralPullback l E f)
    (hb : ∀ K : sfIntegralConstructibleCategory l E X,
      (b.hom.app K).hom =
        (integralComparisonComposition l E C eY.asIso.hom f K).inv ≫
          eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) ≫
          (integralComparisonComposition l E C f eX.asIso.hom K).hom) :
    ∃ (cf : (constructibleIntegralPullback l E f).CommShift ℤ)
      (cX : (constructibleIntegralPullback l E eX.asIso.hom).CommShift ℤ)
      (cY : (constructibleIntegralPullback l E eY.asIso.hom).CommShift ℤ),
      (∃ (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
        (d : (integralDerivedPullback l E f).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E f c ∧
          IntegralCompletedComparison.ShiftDescent l E f c d ∧
          ∀ (K : sfIntegralConstructibleCategory l E X) (r : ℤ),
            HEq (((constructibleIntegralPullback l E f).commShiftIso
              (self := cf) r).hom.app K).hom
              (((integralDerivedPullback l E f).commShiftIso r).hom.app K.obj)) ∧
      (∃ (c : (integralOperationsPullbackComplexFunctor l E eX.asIso.hom).CommShift ℤ)
        (d : (integralDerivedPullback l E eX.asIso.hom).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E eX.asIso.hom c ∧
          IntegralCompletedComparison.ShiftDescent l E eX.asIso.hom c d ∧
          ∀ (K : sfIntegralConstructibleCategory l E X) (r : ℤ),
            HEq (((constructibleIntegralPullback l E eX.asIso.hom).commShiftIso
              (self := cX) r).hom.app K).hom
              (((integralDerivedPullback l E eX.asIso.hom).commShiftIso r).hom.app K.obj)) ∧
      (∃ (c : (integralOperationsPullbackComplexFunctor l E eY.asIso.hom).CommShift ℤ)
        (d : (integralDerivedPullback l E eY.asIso.hom).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E eY.asIso.hom c ∧
          IntegralCompletedComparison.ShiftDescent l E eY.asIso.hom c d ∧
          ∀ (K : sfIntegralConstructibleCategory l E Y) (r : ℤ),
            HEq (((constructibleIntegralPullback l E eY.asIso.hom).commShiftIso
              (self := cY) r).hom.app K).hom
              (((integralDerivedPullback l E eY.asIso.hom).commShiftIso r).hom.app K.obj)) ∧
      (fun [sf : (constructibleIntegralPullback l E f).CommShift ℤ]
        [sX : (constructibleIntegralPullback l E eX.asIso.hom).CommShift ℤ]
        [sY : (constructibleIntegralPullback l E eY.asIso.hom).CommShift ℤ] ↦
        (constructibleIntegralPullback l E f).IsTriangulated ∧
          (constructibleIntegralPullback l E eX.asIso.hom).IsTriangulated ∧
          (constructibleIntegralPullback l E eY.asIso.hom).IsTriangulated ∧
          NatTrans.CommShift b.hom ℤ)
        (sf := cf) (sX := cX) (sY := cY) := by
  classical
  choose a d ha hd using automorphismConstructibleStage_integral_shift_data l E
  let a' {Z W : Scheme.{u}} (g : Z ⟶ W) := a Z W g
  let d' {Z W : Scheme.{u}} (g : Z ⟶ W) := d Z W g
  have ha' {Z W : Scheme.{u}} (g : Z ⟶ W) :
      IntegralCompletedComparison.ShiftCoordinates l E g (a' g) := ha Z W g
  have hd' {Z W : Scheme.{u}} (g : Z ⟶ W) :
      IntegralCompletedComparison.ShiftDescent l E g (a' g) (d' g) := hd Z W g
  let {Z W : Scheme.{u}}
      [∀ z : Z, Invertible (l : Z.residueField z)]
      [∀ w : W, Invertible (l : W.residueField w)] (g : Z ⟶ W) :
      (constructibleIntegralPullback l E g).CommShift ℤ := restrictShift l E g (d' g)
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact ⟨a' f, d' f, ha' f, hd' f, restrictShift_hom l E f (d' f)⟩
  · exact ⟨a' eX.asIso.hom, d' eX.asIso.hom, ha' eX.asIso.hom, hd' eX.asIso.hom,
      restrictShift_hom l E eX.asIso.hom (d' eX.asIso.hom)⟩
  · exact ⟨a' eY.asIso.hom, d' eY.asIso.hom, ha' eY.asIso.hom, hd' eY.asIso.hom,
      restrictShift_hom l E eY.asIso.hom (d' eY.asIso.hom)⟩
  · refine ⟨restrict_tri l E C f (a' f) (d' f) (ha' f) (hd' f),
      restrict_tri l E C eX.asIso.hom (a' eX.asIso.hom) (d' eX.asIso.hom)
        (ha' eX.asIso.hom) (hd' eX.asIso.hom),
      restrict_tri l E C eY.asIso.hom (a' eY.asIso.hom) (d' eY.asIso.hom)
        (ha' eY.asIso.hom) (hd' eY.asIso.hom), ?_⟩
    obtain ⟨c, hc, hcs⟩ := composition_shift l E C a' d' ha' hd' eY.asIso.hom f
    obtain ⟨t, ht, hts⟩ := composition_shift l E C a' d' ha' hd' f eX.asIso.hom
    have eqshift {g g' : Y ⟶ X} (he : g = g') :
        NatTrans.CommShift
          (eqToIso (congrArg (fun g : Y ⟶ X ↦ constructibleIntegralPullback l E g) he)).hom
          ℤ := by
      cases he
      simp only [eqToIso_refl, Iso.refl_hom]
      infer_instance
    have := eqshift h
    let bs := c.symm ≪≫
      eqToIso (congrArg (fun g : Y ⟶ X ↦ constructibleIntegralPullback l E g) h) ≪≫ t
    have hbs : NatTrans.CommShift bs.hom ℤ := by
      dsimp only [bs, Iso.trans_hom, Iso.symm_hom]
      infer_instance
    have hc' (K : sfIntegralConstructibleCategory l E X) :
        (c.inv.app K).hom = (integralComparisonComposition l E C eY.asIso.hom f K).inv := by
      apply (cancel_mono (integralComparisonComposition l E C eY.asIso.hom f K).hom).1
      calc
        _ = (c.inv.app K).hom ≫ (c.hom.app K).hom := by rw [hc K]
        _ = 𝟙 _ := congrArg (fun r ↦ r.hom) (c.inv_hom_id_app K)
        _ = _ := (Iso.inv_hom_id _).symm
    have heq {g g' : Y ⟶ X} (he : g = g')
        (K : sfIntegralConstructibleCategory l E X) :
        ((eqToIso (congrArg (fun g : Y ⟶ X ↦ constructibleIntegralPullback l E g)
          he)).hom.app K).hom =
        eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) he) := by
      cases he
      rfl
    have hb' : b = bs := by
      apply Iso.ext
      apply NatTrans.ext
      funext K
      apply ObjectProperty.hom_ext
      rw [hb]
      simp only [bs, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        ObjectProperty.FullSubcategory.comp_hom, hc', ht]
      rw [heq h K]
    rw [hb']
    exact hbs

end WeilConjectures
