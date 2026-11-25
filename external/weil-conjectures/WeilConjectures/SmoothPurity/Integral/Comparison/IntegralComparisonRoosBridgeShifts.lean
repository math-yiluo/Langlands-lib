/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonCanonicalShifts
public import WeilConjectures.CategoryTheory.RoosShift.RoosCommShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift

/-! # The normalized Roos bridge and its signed shift -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u a b
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Roos applied after exact coefficient restriction. -/
def integralComparisonSequenceRoosFunctor (X : Scheme.{u}) :=
  (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ integralOperationsRoosFunctor

/-- Restriction followed by the native signed Roos shift. -/
@[instance_reducible] def integralComparisonSequenceRoosShift (X : Scheme.{u}) :
    (integralComparisonSequenceRoosFunctor l E X).CommShift ℤ := by
  unfold integralComparisonSequenceRoosFunctor
  letI : ∀ n : ℕ, (RoosShift.levelFunctor
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex
        (T := ℕᵒᵖ) (V := scalarReductionSource l E X)
        (c := ComplexShape.up ℤ)) n).CommShift ℤ := fun n => by
    change (((evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n)).mapHomologicalComplex
      (.up ℤ)).CommShift ℤ
    infer_instance
  letI : ∀ n : ℕ, NatTrans.CommShift (RoosShift.transition
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex
        (T := ℕᵒᵖ) (V := scalarReductionSource l E X)
        (c := ComplexShape.up ℤ)) n) ℤ := fun n => by
    constructor
    intro m
    apply NatTrans.ext
    funext C
    apply HomologicalComplex.hom_ext
    intro i
    change 𝟙 _ ≫ (C.X (i + m)).map (homOfLE (Nat.le_succ n)).op =
      (C.X (i + m)).map (homOfLE (Nat.le_succ n)).op ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  letI := RoosShift.commShift
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex
      (T := ℕᵒᵖ) (V := scalarReductionSource l E X) (c := ComplexShape.up ℤ))
  infer_instance

/-- The existing componentwise Roos bridge, assembled as a natural isomorphism. -/
def integralComparisonRoosBridgeComparison (X : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E X) :
    DerivedCategory.Q ⋙ coefficientSequenceLimit l E X ≅
      integralComparisonSequenceRoosFunctor l E X ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors
      (coefficientConstantTowerLimit l E X) ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)) ρ.comparison

private theorem zeroSecond_eq {A : Type*} [Category A] [Abelian A]
    {M K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (b : M ⟶ CochainComplex.mappingCocone φ) (i : ℤ)
    (hz : b.f i ≫
      (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) = 0) :
    b.f i = (b ≫ CochainComplex.mappingCocone.fst φ).f i ≫
      (CochainComplex.mappingCocone.inl φ).v i i (by omega) := by
  calc
    b.f i = b.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = b.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (by omega) +
        (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by
      erw [CochainComplex.mappingCocone.id_X]
    _ = _ := by
      simp only [Preadditive.comp_add, ← Category.assoc, hz,
        zero_comp, add_zero, HomologicalComplex.comp_f]

private abbrev towerConversion (A : Type*) [Category A] [HasZeroMorphisms A] :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (T := ℕᵒᵖ) (V := A) (c := ComplexShape.up ℤ)

@[instance_reducible] private def towerLevelShift {A : Type*} [Category A] [Abelian A] (n : ℕ) :
    (RoosShift.levelFunctor (towerConversion A) n).CommShift ℤ := by
  change (((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)).CommShift ℤ
  infer_instance

private theorem towerTransitionShift {A : Type*} [Category A] [Abelian A] (n : ℕ) :
    let := fun n ↦ towerLevelShift (A := A) n
    NatTrans.CommShift (RoosShift.transition (towerConversion A) n) ℤ := by
  let := fun n ↦ towerLevelShift (A := A) n
  constructor
  intro m
  apply NatTrans.ext
  funext C
  apply HomologicalComplex.hom_ext
  intro i
  change 𝟙 _ ≫ (C.X (i + m)).map (homOfLE (Nat.le_succ n)).op =
    (C.X (i + m)).map (homOfLE (Nat.le_succ n)).op ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

private def limitAugmentation (X : Scheme.{u}) :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
      scalarReductionSource l E X).mapHomologicalComplex (.up ℤ) ⟶
        towerConversion (scalarReductionSource l E X) ⋙ integralOperationsRoosFunctor where
  app C := integralComparisonLimitToRoos l E X C
  naturality C D f := by
    have hc := (integralComparisonLimitToRoos_existsUnique l E X C).exists.choose_spec
    have hd := (integralComparisonLimitToRoos_existsUnique l E X D).exists.choose_spec
    have hp :
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
          scalarReductionSource l E X).mapHomologicalComplex (.up ℤ)).map f ≫
          integralComparisonLimitToRoos l E X D ≫
            CochainComplex.mappingCocone.fst (scalarRoosBoundary D.asFunctor) =
        (integralComparisonLimitToRoos l E X C ≫
            CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor)) ≫
          Limits.Pi.map (fun n ↦
            ((towerConversion (scalarReductionSource l E X)).map f).app (op n)) := by
      apply Limits.Pi.hom_ext
      intro n
      erw [Category.assoc, Category.assoc, hd.1 n, Category.assoc, Limits.Pi.map_π]
      erw [← Category.assoc, hc.1 n]
      exact (NatTrans.mapHomologicalComplex
        (lim.π (C := scalarReductionSource l E X) (op n)) (.up ℤ)).naturality f
    apply HomologicalComplex.hom_ext
    intro i
    change _ ≫ (integralComparisonLimitToRoos l E X D).f i =
      (integralComparisonLimitToRoos l E X C).f i ≫ _
    erw [zeroSecond_eq _ (integralComparisonLimitToRoos l E X C) i
        (hc.2 i (i - 1) (by omega)),
      zeroSecond_eq _ (integralComparisonLimitToRoos l E X D) i
        (hd.2 i (i - 1) (by omega))]
    change _ = (_ ≫ _) ≫ (SignedCoconeShift.coconeMap
      (scalarRoosBoundary C.asFunctor) (scalarRoosBoundary D.asFunctor)
      (Arrow.homMk _ _ (integralOperationsRoos_square
        ((towerConversion (scalarReductionSource l E X)).map f)).symm)).f i
    conv_rhs => erw [Category.assoc, SignedCoconeShift.coconeMap_inl]
    let P := Limits.Pi.map (fun n ↦
      ((towerConversion (scalarReductionSource l E X)).map f).app (op n))
    let inD := (CochainComplex.mappingCocone.inl (scalarRoosBoundary D.asFunctor)).v
      i i (by omega)
    have h :
        (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
          scalarReductionSource l E X).mapHomologicalComplex (.up ℤ)).map f).f i ≫
            (integralComparisonLimitToRoos l E X D).f i ≫
              (CochainComplex.mappingCocone.fst (scalarRoosBoundary D.asFunctor)).f i =
        (integralComparisonLimitToRoos l E X C ≫
          CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor)).f i ≫ P.f i :=
      congrArg (fun a ↦ a.f i) hp
    change _ ≫ (integralComparisonLimitToRoos l E X D).f i ≫
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary D.asFunctor)).f i ≫ inD =
      (integralComparisonLimitToRoos l E X C ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor)).f i ≫ P.f i ≫ inD
    exact (congrArg (fun z ↦
        (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
          scalarReductionSource l E X).mapHomologicalComplex (.up ℤ)).map f).f i ≫ z)
        (Category.assoc _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a ↦ a ≫ inD) h).trans (Category.assoc _ _ _)))

private theorem augmentation_shift {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
    (b : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⟶
      towerConversion A ⋙ integralOperationsRoosFunctor)
    (hf : ∀ (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
      b.app C ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor) ≫
        Limits.Pi.π (fun n ↦ C.asFunctor.obj (op n)) n =
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app C)
    (hz : ∀ (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i : ℤ), (b.app C).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C.asFunctor)).v
        i (i - 1) (by omega) = 0) :
    let := fun n ↦ towerLevelShift (A := A) n
    let := fun n ↦ towerTransitionShift (A := A) n
    let := RoosShift.commShift (towerConversion A)
    NatTrans.CommShift b ℤ := by
  let := fun n ↦ towerLevelShift (A := A) n
  let := fun n ↦ towerTransitionShift (A := A) n
  let := RoosShift.commShift (towerConversion A)
  constructor
  intro m
  apply NatTrans.ext
  funext C
  apply RoosShift.chain_shift (towerConversion A) _ b hz
  apply ProductShift.productShift_hom_ext
    (RoosShift.levelFunctor (towerConversion A)) C m
  intro n
  erw [Category.assoc, ← Functor.map_comp, Category.assoc, hf C n]
  erw [Category.assoc, Category.assoc, ProductShift.productShiftIso_π]
  erw [← Category.assoc, ← Category.assoc, Category.assoc (b.app (C⟦m⟧)),
    hf (C⟦m⟧) n]
  exact NatTrans.shift_app_comm
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)) m C

private theorem limitAugmentation_shift (X : Scheme.{u}) :
    let := fun n ↦ towerLevelShift (A := scalarReductionSource l E X) n
    let := fun n ↦ towerTransitionShift (A := scalarReductionSource l E X) n
    let := RoosShift.commShift (towerConversion (scalarReductionSource l E X))
    NatTrans.CommShift (limitAugmentation l E X) ℤ := by
  apply augmentation_shift (limitAugmentation l E X)
  · intro C n
    exact (integralComparisonLimitToRoos_existsUnique l E X C).exists.choose_spec.1 n
  · intro C i
    exact (integralComparisonLimitToRoos_existsUnique l E X C).exists.choose_spec.2
      i (i - 1) (by omega)

private def unitOnComplexes {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) (DerivedCategory.quotientCompQhIso B).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) F.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom F.rightDerivedFunctor

private theorem unitOnComplexes_shift {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive] :
    NatTrans.CommShift (unitOnComplexes F) ℤ := by
  unfold unitOnComplexes
  infer_instance

private theorem unitOnComplexes_app {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (C : CochainComplex A ℤ) [C.IsKInjective] :
    (unitOnComplexes F).app C = (F.rightDerivedFunctorObjQIso C).inv := by
  simp only [unitOnComplexes, Functor.rightDerivedFunctorObjQIso,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  dsimp only [Iso.trans, Iso.symm, asIso, Functor.mapIso]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
  rfl

private theorem unitOnComplexes_app_isIso {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (C : CochainComplex A ℤ) [C.IsKInjective] :
    IsIso ((unitOnComplexes F).app C) := by
  rw [unitOnComplexes_app]
  infer_instance

private theorem shift_of_resolutions {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] {F G : C ⥤ D}
    [F.CommShift ℤ] [G.CommShift ℤ] (e : F ≅ G)
    (h : ∀ (X : C) (m : ℤ), ∃ (Y : C) (f : X ⟶ Y), IsIso (F.map f) ∧
      (F.commShiftIso m).hom.app Y ≫ (e.hom.app Y)⟦m⟧' =
        e.hom.app (Y⟦m⟧) ≫ (G.commShiftIso m).hom.app Y) :
    NatTrans.CommShift e.hom ℤ := by
  constructor
  intro m
  apply NatTrans.ext
  funext X
  obtain ⟨Y, f, hf, hY⟩ := h X m
  have : IsIso (G.map f) := by
    have he : G.map f = e.inv.app X ≫ F.map f ≫ e.hom.app Y := by
      erw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
    erw [he]
    infer_instance
  dsimp
  erw [← cancel_mono ((G.map f)⟦m⟧'), Category.assoc, ← Functor.map_comp,
    ← e.hom.naturality, Functor.map_comp, ← Functor.commShiftIso_hom_naturality_assoc,
    hY, Category.assoc, ← Functor.commShiftIso_hom_naturality, e.hom.naturality_assoc]

private theorem normalizedDerivedComparison_shift {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (G : CochainComplex A ℤ ⥤ DerivedCategory B) [G.CommShift ℤ]
    (e : DerivedCategory.Q ⋙ F.rightDerivedFunctor ≅ G)
    (b : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ G)
    [NatTrans.CommShift b ℤ]
    (hn : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      (unitOnComplexes F).app I ≫ e.hom.app I = b.app I) :
    NatTrans.CommShift e.hom ℤ := by
  let η := unitOnComplexes F
  have : NatTrans.CommShift η ℤ := unitOnComplexes_shift F
  apply shift_of_resolutions e
  intro C m
  obtain ⟨I, hI, f, hf, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have := hI
  have := hf
  refine ⟨I, f, ?_, ?_⟩
  · change IsIso (F.rightDerivedFunctor.map (DerivedCategory.Q.map f))
    infer_instance
  · have hi : IsIso (η.app (I⟦m⟧)) := unitOnComplexes_app_isIso F _
    let L := F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
    apply (cancel_epi (η.app (I⟦m⟧))).mp
    calc
      _ = (L.commShiftIso m).hom.app I ≫ (b.app I)⟦m⟧' := by
        erw [← Category.assoc, ← NatTrans.shift_app_comm η m I, Category.assoc,
          ← Functor.map_comp, hn I]
      _ = b.app (I⟦m⟧) ≫ (G.commShiftIso m).hom.app I :=
        NatTrans.shift_app_comm b m I
      _ = _ := by
        have h := congrArg (fun z ↦ z ≫ (G.commShiftIso m).hom.app I)
          (hn (I⟦m⟧)).symm
        exact h.trans (Category.assoc _ _ _)

@[instance_reducible] private def towerLimitShift (X : Scheme.{u}) :
    (coefficientConstantTowerLimit l E X).CommShift ℤ := by
  unfold coefficientConstantTowerLimit
  infer_instance

attribute [local instance] towerLimitShift

private def comparisonForShift (X : Scheme.{u}) (ρ : IntegralComparisonRoosModel l E X) :
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E X ≅
      (towerConversion (scalarReductionSource l E X) ⋙ integralOperationsRoosFunctor) ⋙
        DerivedCategory.Q :=
  ρ.comparison ≪≫ (Functor.associator
    (towerConversion (scalarReductionSource l E X)) integralOperationsRoosFunctor
    DerivedCategory.Q).symm

private theorem normalizedComparison_app (X : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E X)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) [I.IsKInjective] :
    (unitOnComplexes (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
      scalarReductionSource l E X)).app I ≫
        (comparisonForShift l E X ρ).hom.app I =
      (Functor.whiskerRight (limitAugmentation l E X) DerivedCategory.Q).app I := by
  simp only [comparisonForShift, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Category.comp_id]
  erw [unitOnComplexes_app, ρ.computes I, Iso.inv_hom_id_assoc]
  rfl

private theorem normalizedComparison_shift (X : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E X) :
    let := fun n ↦ towerLevelShift (A := scalarReductionSource l E X) n
    let := fun n ↦ towerTransitionShift (A := scalarReductionSource l E X) n
    let := RoosShift.commShift (towerConversion (scalarReductionSource l E X))
    NatTrans.CommShift (comparisonForShift l E X ρ).hom ℤ := by
  let := fun n ↦ towerLevelShift (A := scalarReductionSource l E X) n
  let := fun n ↦ towerTransitionShift (A := scalarReductionSource l E X) n
  let := RoosShift.commShift (towerConversion (scalarReductionSource l E X))
  let b := Functor.whiskerRight (limitAugmentation l E X) DerivedCategory.Q
  have : NatTrans.CommShift b ℤ := by
    have := limitAugmentation_shift l E X
    infer_instance
  exact normalizedDerivedComparison_shift _ _ (comparisonForShift l E X ρ) b
    (fun I _ ↦ normalizedComparison_app l E X ρ I)

/-- The normalized total-limit comparison has the native signed Roos shift.

Source: Stacks 014E and 0941; step 3 of
lem-sf-integral-pullback-realization-shifts.
(blueprint: lem-sf-integral-roos-bridge-shifts).

Proof: on a simultaneous K-injective tower I use rho.computes to express
rho as the canonical right-derived limit comparison followed by the
limit-to-Roos map. The latter has first coordinate the compatible limit
tuple and second coordinate zero, by integralComparisonLimitToRoos's
unique defining property. The native Roos shift multiplies the second
coordinate by (-1)^m and leaves the first coordinate unchanged after
termwise reindexing. Hence the two coordinates prove that the ordinary
limit-to-Roos map commutes with shifts. The canonical right-derived shift
has its defining replacement square on I and I[m], so the composite has
the desired square there. Choose a K-injective replacement of an arbitrary
tower; its localization is invertible and its shift is again a replacement.
Naturality of rho and cancellation transport the square back to that tower.
Finally exact restriction and its mapDerivedCategoryFactors both commute
with their termwise shifts, so whiskering and composition give the displayed
natural-transformation square. This argument uses no exactness of arbitrary
products. Zero shift, negative shifts, zero towers and the empty scheme
use exactly the same two coordinate equations. -/
theorem integralComparisonRoosBridge_commShift (X : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E X) :
    letI := integralComparisonLimitShift l E X
    letI := integralComparisonSequenceRoosShift l E X
    NatTrans.CommShift (integralComparisonRoosBridgeComparison l E X ρ).hom ℤ := by
  let := integralComparisonLimitShift l E X
  let := integralComparisonSequenceRoosShift l E X
  let := fun n ↦ towerLevelShift (A := scalarReductionSource l E X) n
  let := fun n ↦ towerTransitionShift (A := scalarReductionSource l E X) n
  let := RoosShift.commShift (towerConversion (scalarReductionSource l E X))
  have := normalizedComparison_shift l E X ρ
  let R := coefficientSequenceRestriction l E X
  let T := R.mapHomologicalComplex (.up ℤ)
  let H := towerConversion (scalarReductionSource l E X) ⋙ integralOperationsRoosFunctor
  let e := (Functor.associator DerivedCategory.Q R.mapDerivedCategory
      (coefficientConstantTowerLimit l E X)).symm ≪≫
    Functor.isoWhiskerRight R.mapDerivedCategoryFactors (coefficientConstantTowerLimit l E X) ≪≫
    Functor.associator T DerivedCategory.Q (coefficientConstantTowerLimit l E X) ≪≫
    Functor.isoWhiskerLeft T (comparisonForShift l E X ρ) ≪≫
    (Functor.associator T H DerivedCategory.Q).symm
  have he : (integralComparisonRoosBridgeComparison l E X ρ).hom = e.hom := by
    apply NatTrans.ext
    funext C
    dsimp only [e]
    erw [integralComparisonRoosBridgeComparison, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [comparisonForShift, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id]
    rfl
  have hs : NatTrans.CommShift e.hom ℤ := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
    infer_instance
  erw [he]
  exact hs

end WeilConjectures
