/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftIntegral
public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Shift

/-! # Shift compatibility of the integral pullback scalar comparison

The ordinary-to-completed scalar comparison on integral constructible objects commutes with
the normalized integral transition shifts (`sfIntegralOrdinaryScalarComparison_commShift`).
Conjugating the ordinary scalar/pullback comparison by these comparisons gives the ambient
form `integralPullbackScalarAmbientIso` of the integral pullback scalar comparison, which
therefore commutes with shifts. Since the inclusion of constructible objects is fully
faithful, the coefficient transition of the integral pullback scalar comparison commutes
with the supplied integral pullback shifts (`integralPullbackScalarComparison_commShift`).

This is the integral step of the proof of `rationalPullbackTransitionShift`.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph.
(blueprint: lem-sf-rational-pullback-transition-shift).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
attribute [local irreducible] constructibleIntegralPullback rationalDerivedPullback

/-- The ordinary-to-completed comparison on integral constructible objects, in
functor form. -/
noncomputable def sfIntegralOrdinaryScalarComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :
    (sfIntegralConstructible l E W).ι ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι W ⋙ (sfIntegralConstructible l L W).ι :=
  sfIntegralOrdinaryComparison l E L ι W

/-- The ordinary-to-completed comparison is the normalized scalar completion map. -/
theorem sfIntegralOrdinaryScalarComparison_hom_app (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) (K : sfIntegralConstructibleCategory l E W) :
    (sfIntegralOrdinaryScalarComparison l E L ι W).hom.app K =
      (scalarCompletion l E L ι W).app K.obj := by
  let χ := scalarCompletion l E L ι W
  let (J : sfIntegralConstructibleCategory l E W) : IsIso (χ.app J.obj) :=
    (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.2 J.obj J.property.1
  let e : (sfIntegralConstructible l E W).ι ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (sfIntegralConstructible l E W).ι ⋙ integralScalarExtension l E L ι W :=
    NatIso.ofComponents (fun J ↦ asIso (χ.app J.obj)) (fun f ↦ χ.naturality f.hom)
  have he : e = sfIntegralOrdinaryComparison l E L ι W := by
    apply (sfIntegralOrdinaryComparison_existsUnique l E L ι W).unique
    · intro P hP
      exact (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.1 P
    · exact (sfIntegralOrdinaryComparison_existsUnique l E L ι W).exists.choose_spec
  exact (congrArg (fun a ↦ a.hom.app K) he).symm

/-- The ordinary-to-completed comparison commutes with the ordinary derived scalar shift
and the normalized integral transition shift. -/
theorem sfIntegralOrdinaryScalarComparison_commShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (W : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L) :
    letI : (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω W E L h
    NatTrans.CommShift (sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).hom ℤ := by
  constructor
  intro n
  ext K
  have hn := (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
    l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) W).exists.choose_spec n K
  have hn' := eq_of_heq hn
  change _ = (sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).inv.app (K⟦n⟧) ≫
      (((sfIntegralConstructible l (Coefficient.{u} l Ω E) W).ι ⋙
        integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) W).commShiftIso n).hom.app K ≫
      (shiftFunctor (DerivedCategory (integralTowerModules l (Coefficient.{u} l Ω L) W)) n).map
        ((sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) W).hom.app K) at hn'
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc, ObjectProperty.ι_map]
  change _ = (sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).hom.app (K⟦n⟧) ≫ _
  rw [← Category.assoc, hn']
  rw [Iso.hom_inv_id_app_assoc]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]

attribute [local semireducible] constructibleIntegralPullback

/-- The ambient component of the integral pullback scalar comparison. -/
theorem integralPullbackScalarComparison_hom_hom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E X) :
    (integralPullbackScalarComparison l E L ι f K).hom.hom =
      (scalarCompletionIso l E L ι Y ((integralDerivedPullback l E f).obj K.obj)
        ((constructibleIntegralPullback l E f).obj K).property.1).inv ≫
        (scalarPullbackOrdinary l E L ι f).hom.app K.obj ≫
        (integralDerivedPullback l L f).map ((scalarCompletion l E L ι X).app K.obj) :=
  rfl

/-- The integral pullback scalar comparison is the ordinary comparison conjugated by the
ordinary-to-completed scalar comparisons. -/
theorem integralPullbackScalarComparison_hom_hom_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E X) :
    (sfIntegralOrdinaryScalarComparison l E L ι Y).inv.app
        ((constructibleIntegralPullback l E f).obj K) ≫
      (scalarPullbackOrdinary l E L ι f).hom.app ((sfIntegralConstructible l E X).ι.obj K) ≫
      (integralDerivedPullback l L f).map
        ((sfIntegralOrdinaryScalarComparison l E L ι X).hom.app K) =
    (integralPullbackScalarComparison l E L ι f K).hom.hom := by
  have hY := sfIntegralOrdinaryScalarComparison_hom_app l E L ι Y
    ((constructibleIntegralPullback l E f).obj K)
  have hYi : (sfIntegralOrdinaryScalarComparison l E L ι Y).inv.app
      ((constructibleIntegralPullback l E f).obj K) =
      (scalarCompletionIso l E L ι Y ((integralDerivedPullback l E f).obj K.obj)
        ((constructibleIntegralPullback l E f).obj K).property.1).inv := by
    rw [← Iso.app_inv]
    apply Iso.inv_ext
    rw [Iso.app_hom, hY]
    exact (scalarCompletionIso l E L ι Y ((integralDerivedPullback l E f).obj K.obj)
      ((constructibleIntegralPullback l E f).obj K).property.1).hom_inv_id
  rw [sfIntegralOrdinaryScalarComparison_hom_app, hYi, integralPullbackScalarComparison_hom_hom]
  rfl

/-- The constructible integral pullback is the restriction of the ambient integral
derived pullback. -/
noncomputable def constructibleIntegralPullbackCompι (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralPullback l E f ⋙ (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E f :=
  ObjectProperty.liftCompιIso _ _ _

/-- The restriction comparison has identity components. -/
theorem constructibleIntegralPullbackCompι_hom_app (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (K : sfIntegralConstructibleCategory l E X) :
    (constructibleIntegralPullbackCompι l E f).hom.app K = 𝟙 _ :=
  rfl

/-- The restriction comparison has identity inverse components. -/
theorem constructibleIntegralPullbackCompι_inv_app (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (K : sfIntegralConstructibleCategory l E X) :
    (constructibleIntegralPullbackCompι l E f).inv.app K = 𝟙 _ :=
  rfl

/-- The restriction comparison commutes with shifts whose components are the ambient ones. -/
theorem constructibleIntegralPullbackCompι_commShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [(constructibleIntegralPullback l E f).CommShift ℤ]
    [(integralDerivedPullback l E f).CommShift ℤ]
    (hs : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℤ),
        HEq (((constructibleIntegralPullback l E f).commShiftIso n).hom.app K).hom
          (((integralDerivedPullback l E f).commShiftIso n).hom.app K.obj)) :
    NatTrans.CommShift (constructibleIntegralPullbackCompι l E f).hom ℤ :=
  ObjectProperty.liftCompιIso_hom_commShift_of_heq _ _ _ (fun K n ↦ (hs K n).trans (by
    rw [Functor.commShiftIso_comp_hom_app]
    exact (Functor.map_comp_heq_of_heq_id _ _ _ (ObjectProperty.obj_shift_eq _ n K)
      ((heq_of_eq (ObjectProperty.ι_commShiftIso_hom_app _ n K)).trans
        (eqToHom_heq_id_cod _ _ _))).symm))

/-- The ambient form of the integral pullback scalar comparison: the ordinary
scalar/pullback comparison conjugated by the ordinary-to-completed comparisons. -/
noncomputable def integralPullbackScalarAmbientIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (constructibleIntegralPullback l E f ⋙ sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y) ⋙ (sfIntegralConstructible l L Y).ι ≅
      (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι X ⋙ constructibleIntegralPullback l L f) ⋙ (sfIntegralConstructible l L Y).ι :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntegralOrdinaryScalarComparison l E L ι Y).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constructibleIntegralPullbackCompι l E f) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarPullbackOrdinary l E L ι f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfIntegralOrdinaryScalarComparison l E L ι X) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (constructibleIntegralPullbackCompι l L f).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The components of the ambient comparison are those of the integral pullback scalar
comparison. -/
theorem integralPullbackScalarAmbientIso_hom_app (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E X) :
    (integralPullbackScalarAmbientIso l E L ι f).hom.app K =
      (integralPullbackScalarComparison l E L ι f K).hom.hom := by
  simp only [integralPullbackScalarAmbientIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
  have h1 : (integralOrdinaryDerivedScalar l E L ι Y).map
      ((constructibleIntegralPullbackCompι l E f).hom.app K) = 𝟙 _ :=
    (integralOrdinaryDerivedScalar l E L ι Y).map_id _
  rw [h1, constructibleIntegralPullbackCompι_inv_app]
  erw [Category.id_comp, Category.comp_id]
  exact integralPullbackScalarComparison_hom_hom_eq l E L ι f K

/-- The ambient comparison commutes with shifts once the ordinary scalar/pullback
comparison does. -/
theorem integralPullbackScalarAmbientIso_commShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Index l Ω) (h : E ≤ L)
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    [(integralDerivedPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [(integralDerivedPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    (hsE : ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω E) f).commShiftIso n).hom.app K.obj))
    (hsL : ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω L) f).commShiftIso n).hom.app K.obj))
    (hS : NatTrans.CommShift (scalarPullbackOrdinary l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom ℤ) :
    letI := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h
    letI := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h
    NatTrans.CommShift (integralPullbackScalarAmbientIso l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom ℤ := by
  let := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h
  let := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h
  have : NatTrans.CommShift (sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X).hom ℤ :=
    sfIntegralOrdinaryScalarComparison_commShift l Ω X E L h
  have : NatTrans.CommShift (sfIntegralOrdinaryScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).hom ℤ :=
    sfIntegralOrdinaryScalarComparison_commShift l Ω Y E L h
  have : NatTrans.CommShift
      (constructibleIntegralPullbackCompι l (Coefficient.{u} l Ω E) f).hom ℤ :=
    constructibleIntegralPullbackCompι_commShift l _ f hsE
  have : NatTrans.CommShift
      (constructibleIntegralPullbackCompι l (Coefficient.{u} l Ω L) f).hom ℤ :=
    constructibleIntegralPullbackCompι_commShift l _ f hsL
  simp only [integralPullbackScalarAmbientIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- The coefficient transition of the integral pullback scalar comparison commutes with the
supplied integral pullback shifts and the normalized integral transition shifts.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph
(blueprint: lem-sf-framework-theta-shift-compatibility). -/
theorem integralPullbackScalarComparison_commShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Index l Ω) (h : E ≤ L)
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    (hE : ∃ (c : (integralOperationsPullbackComplexFunctor l
          (Coefficient.{u} l Ω E) f).CommShift ℤ)
        (d : (integralDerivedPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ),
      IntegralCompletedComparison.ShiftCoordinates l (Coefficient.{u} l Ω E) f c ∧
      IntegralCompletedComparison.ShiftDescent l (Coefficient.{u} l Ω E) f c d ∧
      ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω E) f).commShiftIso
            (self := d) n).hom.app K.obj))
    (hL : ∃ (c : (integralOperationsPullbackComplexFunctor l
          (Coefficient.{u} l Ω L) f).CommShift ℤ)
        (d : (integralDerivedPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ),
      IntegralCompletedComparison.ShiftCoordinates l (Coefficient.{u} l Ω L) f c ∧
      IntegralCompletedComparison.ShiftDescent l (Coefficient.{u} l Ω L) f c d ∧
      ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω L) f).commShiftIso
            (self := d) n).hom.app K.obj)) :
    letI := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h
    letI := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h
    ∃ α : constructibleIntegralPullback l (Coefficient.{u} l Ω E) f ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ⋙
        constructibleIntegralPullback l (Coefficient.{u} l Ω L) f,
      (∀ K, α.app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f K) ∧
      NatTrans.CommShift α.hom ℤ := by
  obtain ⟨cE, dE, hcE, hdE, hsE⟩ := hE
  obtain ⟨cL, dL, hcL, hdL, hsL⟩ := hL
  let := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h
  let := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h
  let := dE
  let := dL
  have hδ := integralPullbackScalarAmbientIso_commShift l Ω f E L h hsE hsL
    (scalarPullbackOrdinary_commShift l _ _ _ f cE dE hcE hdE cL dL hcL hdL)
  let hI := (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).fullyFaithfulι.whiskeringRight
    (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X)
  let α : constructibleIntegralPullback l (Coefficient.{u} l Ω E) f ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ⋙
        constructibleIntegralPullback l (Coefficient.{u} l Ω L) f :=
    hI.preimageIso (integralPullbackScalarAmbientIso l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f)
  have hwα : Functor.whiskerRight α.hom (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι =
      (integralPullbackScalarAmbientIso l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom :=
    hI.map_preimage _
  refine ⟨α, fun K ↦ ?_, ?_⟩
  · apply Iso.ext
    apply ObjectProperty.hom_ext
    exact (NatTrans.congr_app hwα K).trans
      (integralPullbackScalarAmbientIso_hom_app l _ _ _ f K)
  · have : NatTrans.CommShift (Functor.whiskerRight α.hom
        (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι) ℤ := by
      rw [hwα]
      exact hδ
    exact NatTrans.CommShift.of_whiskerRight α.hom
      (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι

end WeilConjectures
