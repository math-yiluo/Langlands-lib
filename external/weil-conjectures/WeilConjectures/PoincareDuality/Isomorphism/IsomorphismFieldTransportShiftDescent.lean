/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismFieldTransportClauses
import WeilConjectures.CategoryTheory.StageSystem.Functor
import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismPullbackScalarShift
import WeilConjectures.SixFunctors.Supporting.SpecifiedPullbackComparisonAlpha

/-! # Shift descent for normalized isomorphism transport

The private generic pair-shift construction follows the proved calculation in
`SfFrameworkCommonStageDescent` (SHEAF group Q19). It uses only coherent pair
functor descent and the published stage inclusions and their shift comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option linter.privateModule false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
namespace WeilConjectures
open CategoryTheory.Pretriangulated
open GeneralAlgebraicallyClosedCoefficients (inclusion)

attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback

section PairTransformations
universe w a b a' b'
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type a} [∀ i, Category.{b} (C i)]
  {D : Type a'} [Category.{b'} D]

private def pairNatTrans (U : StageSystem C) (J K : U.PairCategory ⥤ D)
    (τ : ∀ i, U.ι i ⋙ J ⟶ U.ι i ⋙ K)
    (comm : ∀ {i j : I} (h : i ≤ j) (X : C i),
      J.map ((U.transIso h).hom.app X) ≫ (τ i).app X =
        (τ j).app ((U.T h).obj X) ≫ K.map ((U.transIso h).hom.app X)) : J ⟶ K where
  app X := (τ X.stage).app X.obj
  naturality {X Y} f := by
    have comm_inv {i j : I} (h : i ≤ j) (Z : C i) :
        J.map ((U.transIso h).inv.app Z) ≫ (τ j).app ((U.T h).obj Z) =
          (τ i).app Z ≫ K.map ((U.transIso h).inv.app Z) := by
      rw [← cancel_mono (K.map ((U.transIso h).hom.app Z)), Category.assoc,
        ← comm, ← J.map_comp_assoc]
      simp
    induction f using StageSystem.PairCategory.hom_induction with
    | h n hX hY u =>
      rw [StageSystem.mkHom_eq_isoToStage, J.map_comp, J.map_comp, K.map_comp, K.map_comp]
      simp only [Category.assoc]
      change J.map ((U.transIso hX).inv.app X.obj) ≫
          J.map ((U.ι n).map u) ≫ J.map ((U.transIso hY).hom.app Y.obj) ≫
          (τ Y.stage).app Y.obj =
        (τ X.stage).app X.obj ≫
          (K.map ((U.transIso hX).inv.app X.obj) ≫
            K.map ((U.ι n).map u) ≫ K.map ((U.transIso hY).hom.app Y.obj))
      have hn := (τ n).naturality u
      dsimp only [Functor.comp_map] at hn
      rw [comm, reassoc_of% hn, reassoc_of% (comm_inv hX X.obj)]

private theorem pairFunctor_transIso
    {D' : I → Type a'} [∀ i, Category.{b'} (D' i)]
    {U : StageSystem C} {W : StageSystem D'} (F : U.Morphism W)
    {i j : I} (h : i ≤ j) (X : C i) :
    F.functor.map ((U.transIso h).hom.app X) =
      (W.ι j).map ((F.β h).inv.app X) ≫
        (W.transIso h).hom.app ((F.Φ i).obj X) := by
  rw [StageSystem.transIso_hom_app_eq, F.functor_map_mkHom,
    StageSystem.ι_map_eq le_rfl, StageSystem.transIso_hom_app_eq,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  change (F.β le_rfl).hom.app ((U.T h).obj X) ≫
      (F.Φ j).map ((U.assoc h le_rfl).hom.app X) ≫ (F.β h).inv.app X =
    (W.T le_rfl).map ((F.β h).inv.app X) ≫
      (W.assoc h le_rfl).hom.app ((F.Φ i).obj X)
  rw [← cancel_epi ((W.T le_rfl).map ((F.β h).hom.app X))]
  rw [reassoc_of% (F.coh h le_rfl X)]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  change (W.assoc h le_rfl).hom.app ((F.Φ i).obj X) ≫ 𝟙 _ =
    (W.T le_rfl).map (𝟙 ((W.T h).obj ((F.Φ i).obj X))) ≫
      (W.assoc h le_rfl).hom.app ((F.Φ i).obj X)
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

section PairShift
variable {D' : I → Type a'} [∀ i, Category.{b'} (D' i)]
  {U : StageSystem C} {W : StageSystem D'}
  [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D' i) ℤ]
  [HasShift U.PairCategory ℤ] [HasShift W.PairCategory ℤ]
  [∀ i, (U.ι i).CommShift ℤ] [∀ i, (W.ι i).CommShift ℤ]
  (F : U.Morphism W) [∀ i, (F.Φ i).CommShift ℤ]

private def pairStageShiftIso (n : ℤ) (i : I) :
    U.ι i ⋙ (shiftFunctor U.PairCategory n ⋙ F.functor) ≅
      U.ι i ⋙ (F.functor ⋙ shiftFunctor W.PairCategory n) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((U.ι i).commShiftIso n).symm F.functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (F.ιCompFunctorIso i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((F.Φ i).commShiftIso n) (W.ι i) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((W.ι i).commShiftIso n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.ιCompFunctorIso i).symm _ ≪≫
    Functor.associator _ _ _

private theorem pairStageShiftIso_hom_app (n : ℤ) (i : I) (X : C i) :
    (pairStageShiftIso F n i).hom.app X =
      F.functor.map (((U.ι i).commShiftIso n).inv.app X) ≫
        (W.ι i).map (((F.Φ i).commShiftIso n).hom.app X) ≫
          ((W.ι i).commShiftIso n).hom.app ((F.Φ i).obj X) := by
  simp [pairStageShiftIso]

variable [∀ {i j : I} (h : i ≤ j), (U.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (W.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (U.transIso h).hom ℤ]
  [∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (W.transIso h).hom ℤ]

private theorem pairStageShiftIso_comm
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)
    (n : ℤ) {i j : I} (h : i ≤ j) (X : C i) :
    (shiftFunctor U.PairCategory n ⋙ F.functor).map ((U.transIso h).hom.app X) ≫
        (pairStageShiftIso F n i).hom.app X =
      (pairStageShiftIso F n j).hom.app ((U.T h).obj X) ≫
        (F.functor ⋙ shiftFunctor W.PairCategory n).map ((U.transIso h).hom.app X) := by
  have := hβ h
  have hb := NatTrans.shift_app_comm (F.β h).inv n X
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at hb
  have hk :
      (F.Φ j).map (((U.T h).commShiftIso n).inv.app X) ≫
        (F.β h).inv.app (X⟦n⟧) ≫
          (W.T h).map (((F.Φ i).commShiftIso n).hom.app X) ≫
            ((W.T h).commShiftIso n).hom.app ((F.Φ i).obj X) =
      ((F.Φ j).commShiftIso n).hom.app ((U.T h).obj X) ≫
        ((F.β h).inv.app X)⟦n⟧' := by
    erw [← hb]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have ht := (W.transIso h).hom.naturality (((F.Φ i).commShiftIso n).hom.app X)
  dsimp only [Functor.comp_map] at ht
  have hs := NatTrans.shift_app_comm (W.transIso h).hom n ((F.Φ i).obj X)
  have hw := ((W.ι j).commShiftIso n).hom.naturality ((F.β h).inv.app X)
  dsimp only [Functor.comp_map] at hw
  simp only [Functor.comp_map, pairStageShiftIso_hom_app]
  simp only [StageSystem.ι_obj, Functor.comp_obj, StageSystem.Morphism.functor_obj]
  erw [NatTrans.shift_app (U.transIso h).hom n X]
  simp only [Functor.commShiftIso_comp_inv_app, Functor.comp_obj,
    Functor.map_comp, Category.assoc]
  rw [← F.functor.map_comp_assoc (((U.ι i).commShiftIso n).hom.app X)]
  simp only [Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [pairFunctor_transIso, pairFunctor_transIso, F.functor_map_ι]
  simp only [Category.assoc]
  erw [cancel_epi, ← reassoc_of% ht, ← hs]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  erw [hk]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hw]

private def pairShiftIso
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ) (n : ℤ) :
    shiftFunctor U.PairCategory n ⋙ F.functor ≅
      F.functor ⋙ shiftFunctor W.PairCategory n :=
  NatIso.ofComponents (fun X ↦ (pairStageShiftIso F n X.stage).app X.obj)
    (fun f ↦ (pairNatTrans U _ _ (fun i ↦ (pairStageShiftIso F n i).hom)
      (pairStageShiftIso_comm F hβ n)).naturality f)

private theorem pairShiftIso_hom_app
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)
    (n : ℤ) (X : U.PairCategory) :
    (pairShiftIso F hβ n).hom.app X =
      F.functor.map (((U.ι X.stage).commShiftIso n).inv.app X.obj) ≫
        (W.ι X.stage).map (((F.Φ X.stage).commShiftIso n).hom.app X.obj) ≫
          ((W.ι X.stage).commShiftIso n).hom.app ((F.Φ X.stage).obj X.obj) := by
  exact pairStageShiftIso_hom_app F n X.stage X.obj

@[instance_reducible] private def pairCommShift
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ) :
    F.functor.CommShift ℤ where
  commShiftIso := pairShiftIso F hβ
  commShiftIso_zero := by
    ext X
    rw [pairShiftIso_hom_app, Functor.CommShift.isoZero_hom_app]
    simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
      Functor.CommShift.isoZero_inv_app, Functor.map_comp, F.functor_map_ι, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    change F.functor.map ((shiftFunctorZero U.PairCategory ℤ).hom.app X) ≫
        (W.ι X.stage).map ((F.Φ X.stage).map (𝟙 X.obj) ≫
          𝟙 ((F.Φ X.stage).obj X.obj)) ≫
        (shiftFunctorZero W.PairCategory ℤ).inv.app (F.functor.obj X) = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.id_comp]
  commShiftIso_add n m := by
    ext X
    rw [Functor.CommShift.isoAdd_hom_app, pairShiftIso_hom_app F hβ (n + m) X,
      pairShiftIso_hom_app F hβ n X]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (pairShiftIso F hβ m).hom.naturality
      (((U.ι X.stage).commShiftIso n).inv.app X.obj)
    dsimp only [Functor.comp_map, Functor.comp_obj, StageSystem.ι_obj] at hn
    rw [← reassoc_of% hn]
    rw [pairShiftIso_hom_app]
    simp only [Category.assoc]
    have hw := (((W.ι X.stage).commShiftIso m).hom.naturality
      (((F.Φ X.stage).commShiftIso n).hom.app X.obj))
    dsimp only [Functor.comp_map] at hw
    erw [← reassoc_of% hw]
    simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
      Functor.CommShift.isoAdd_inv_app, Functor.map_comp, F.functor_map_ι, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    congr 2
    dsimp only [Functor.comp_obj]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem pairRestrictionShift
    (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ) (i : I) :
    letI := pairCommShift F hβ
    NatTrans.CommShift (F.ιCompFunctorIso i).hom ℤ := by
  let _ := pairCommShift F hβ
  constructor
  intro n
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, StageSystem.Morphism.ιCompFunctorIso_hom_app,
    Category.assoc]
  change F.functor.map (((U.ι i).commShiftIso n).hom.app X) ≫
      (pairShiftIso F hβ n).hom.app ⟨i, X⟩ ≫
        (shiftFunctor W.PairCategory n).map (𝟙 (F.functor.obj ⟨i, X⟩)) =
      𝟙 _ ≫ (W.ι i).map (((F.Φ i).commShiftIso n).hom.app X) ≫
        ((W.ι i).commShiftIso n).hom.app ((F.Φ i).obj X)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp,
    pairShiftIso_hom_app]
  simp only [← F.functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end PairShift

end PairTransformations

private theorem eqToIso_shift
    {A B : Type*} [Category* A] [Category* B] [HasShift A ℤ] [HasShift B ℤ]
    {F G : A ⥤ B} (h : F = G) (q : G.CommShift ℤ) :
    @NatTrans.CommShift _ _ _ _ _ _ (eqToIso h).hom ℤ _ _ _
      (cast (congrArg (fun H : A ⥤ B ↦ H.CommShift ℤ) h.symm) q) q := by
  cases h
  constructor
  intro n
  ext K
  simp

section StageShifts
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
  (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
  (S : ∀ E : Index l Ω,
    IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY)

private theorem lambda_inverse_formula (E : Index l Ω)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
    HEq ((S E).lambda.symm.hom.app K)
      (inverseImagePullbackComparisonDerived l (Coefficient.{u} l Ω E) g hX hY K.obj) := by
  have h : (S E).lambda.app K =
      pullbackIdentityLambda l (Coefficient.{u} l Ω E) g hX hY K :=
    Iso.ext (eq_of_heq ((S E).lambda_formula K))
  have hi := congrArg Iso.inv h
  simpa only [Iso.symm_hom, Iso.app_inv, pullbackIdentityLambda, Iso.symm_inv, asIso_hom] using
    heq_of_eq hi

private theorem normalized_scalar_shift (E L : Index l Ω) (h : E ≤ L) :
    (fun [rE : (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ]
      [rL : (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
      letI := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
      letI := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω Y E L h
      NatTrans.CommShift (commonStagePullbackTransition l Ω g h).hom ℤ)
      (rE := (S E).rationalShift) (rL := (S L).rationalShift) := by
  let : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ :=
    (S E).integralShift
  let : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ :=
    (S L).integralShift
  let : (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ :=
    (S E).rationalShift
  let : (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ :=
    (S L).rationalShift
  let := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
  let := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω Y E L h
  let := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h
  let := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h
  have hsE : NatTrans.CommShift (S E).lambda.hom ℤ := (S E).lambda_shift
  have hsL : NatTrans.CommShift (S L).lambda.hom ℤ := (S L).lambda_shift
  have hsE' : NatTrans.CommShift (S E).lambda.symm.hom ℤ := inferInstance
  have hsL' : NatTrans.CommShift (S L).lambda.symm.hom ℤ := inferInstance
  let α : constructibleIntegralPullback l (Coefficient.{u} l Ω E) g ⋙
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ≅
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ⋙
      constructibleIntegralPullback l (Coefficient.{u} l Ω L) g :=
    NatIso.ofComponents (integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g)
      (fun {K J} f ↦ by
        apply ObjectProperty.hom_ext
        exact (specifiedPullbackComparisonAlpha l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h)
          g K.obj K.property).choose_spec.2 J.obj J.property _ f.hom)
  have hs := (isomorphismPullbackScalarShift l Ω g hX hY E L h
    (S E).integralShift (S E).rationalShift (S E).lambda.symm
    (lambda_inverse_formula l Ω g hX hY S E) hsE' (S E).rational_shift_formula
    (S L).integralShift (S L).rationalShift (S L).lambda.symm
    (lambda_inverse_formula l Ω g hX hY S L) hsL' (S L).rational_shift_formula
    α (fun _ ↦ rfl)).2
  let : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h
  let : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h
  have hraw : NatTrans.CommShift
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g).hom ℤ := by
    simpa only [isomorphismCoefficientInclusion] using hs
  have htX : NatTrans.CommShift (operationStageTransitionIso l Ω X E L h).hom ℤ :=
    eqToIso_shift ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω X).exists.choose_spec.1 E L h)
      (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h)
  have htY : NatTrans.CommShift (operationStageTransitionIso l Ω Y E L h).hom ℤ :=
    eqToIso_shift ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω Y).exists.choose_spec.1 E L h)
      (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h)
  dsimp only [commonStagePullbackTransition, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

end StageShifts

/-- The prescribed finite shifts descend and commute with a normalized inclusion comparison.
Source: current blueprint sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md, inverse automorphism paragraph;
step 1 and the shift part of step 3 of the common-stage transport argument.
(blueprint: lem-pod-isomorphism-field-transport-shift-descent).

Proof: invert the supplied lambda comparisons. Their component normalization is
exactly inverseImagePullbackComparisonDerived, and the lambda shift square also
holds for the inverse comparison. Apply isomorphismPullbackScalarShift to these
comparisons and the given integral and rational shifts. This shows that the
normalized rational scalar comparisons commute with the supplied shifts. The
published stage transitions and their shifts are transports of those scalar
functors and shifts along equality, so their transition identifications also
commute with shifts. Descend each finite shift at the object's own field.
On an arbitrary representative, the two scalar shift equations and finite
naturality give naturality of the descended comparison. Descend the finite zero
and addition equations to obtain CommShift. Both restrictions to a finite stage
have its finite shift component, so the identity-normalized inclusion comparison
commutes with shifts. All such comparisons agree componentwise by hc. No inverse
family, equivalence, triangle preservation, or dimension hypothesis is needed.
-/
theorem isomorphismFieldTransportShiftDescent
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY)
    (c : ∀ E : Index l Ω,
      inclusion (Y := Y) E ⋙ commonStageDerivedPullback l Ω g ≅
        rationalDerivedPullback l (Coefficient.{u} l Ω E) g ⋙ inclusion (Y := X) E)
    (hc : ∀ (E : Index l Ω)
      (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      HEq ((c E).hom.app K) (𝟙 (commonStagePullbackObject l Ω g
        ((inclusion (Y := Y) E).obj K)))) :
    ∃ q : (commonStageDerivedPullback l Ω g).CommShift ℤ,
      ∀ E : Index l Ω,
        @NatTrans.CommShift _ _ _ _ _ _ (c E).hom ℤ _ _ _
          (@Functor.CommShift.comp _ _ _ _ _ _
            (inclusion (Y := Y) E) (commonStageDerivedPullback l Ω g) ℤ _ _ _ _
            (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
              (l := l) (Ω := Ω) (Y := Y) E) q)
          (@Functor.CommShift.comp _ _ _ _ _ _
            (rationalDerivedPullback l (Coefficient.{u} l Ω E) g) (inclusion (Y := X) E)
            ℤ _ _ _ _ (S E).rationalShift
            (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
              (l := l) (Ω := Ω) (Y := X) E)) := by
  obtain ⟨hcoh, hM⟩ := commonStagePullbackNormalizedDescent l Ω g
  let M : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X) :=
    ⟨fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) g,
      commonStagePullbackTransition l Ω g, hcoh⟩
  let : ∀ E : Index l Ω,
      (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ :=
    fun E ↦ (S E).rationalShift
  have hs : ∀ {E L : Index l Ω} (h : E ≤ L), NatTrans.CommShift (M.β h).hom ℤ :=
    fun {_ _} h ↦ normalized_scalar_shift l Ω g hX hY S _ _ h
  have D : ∃ q : (commonStageDerivedPullback l Ω g).CommShift ℤ,
      ∃ c₀ : ∀ E : Index l Ω,
        inclusion (Y := Y) E ⋙ commonStageDerivedPullback l Ω g ≅
          rationalDerivedPullback l (Coefficient.{u} l Ω E) g ⋙ inclusion (Y := X) E,
        (∀ (E : Index l Ω)
          (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
          HEq ((c₀ E).hom.app K) (𝟙 (commonStagePullbackObject l Ω g
            ((inclusion (Y := Y) E).obj K)))) ∧
        (∀ E : Index l Ω,
          @NatTrans.CommShift _ _ _ _ _ _ (c₀ E).hom ℤ _ _ _
            (@Functor.CommShift.comp _ _ _ _ _ _
              (inclusion (Y := Y) E) (commonStageDerivedPullback l Ω g) ℤ _ _ _ _
              (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
                (l := l) (Ω := Ω) (Y := Y) E) q)
            (@Functor.CommShift.comp _ _ _ _ _ _
              (rationalDerivedPullback l (Coefficient.{u} l Ω E) g) (inclusion (Y := X) E)
              ℤ _ _ _ _ (S E).rationalShift
              (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
                (l := l) (Ω := Ω) (Y := X) E))) := by
    rw [hM]
    let q := pairCommShift M hs
    refine ⟨q, fun E ↦ M.ιCompFunctorIso E, fun E K ↦ HEq.rfl, ?_⟩
    exact fun E ↦ pairRestrictionShift M hs E
  obtain ⟨q, c₀, hc₀, hq⟩ := D
  have he : c = c₀ := by
    funext E
    apply Iso.ext
    ext K
    exact eq_of_heq ((hc E K).trans (hc₀ E K).symm)
  subst c
  exact ⟨q, hq⟩

end WeilConjectures
