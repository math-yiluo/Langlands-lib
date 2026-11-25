/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Automorphism.AutomorphismConstructibleStageCore
import WeilConjectures.SmoothPurity.Rational.RationalPullbackShiftLocalization
import all WeilConjectures.SmoothPurity.Sf.SfRationalScalarExactOfIntegral
import WeilConjectures.SmoothPurity.Integral.IntegralDerivedPullbackLinear

/-! # Rational localization of automorphism square shifts

Source: current blueprint, Weil-structures paragraph of the open-closed triangle.
(blueprint: lem-sf-automorphism-rational-shift-descent).
The finite and integral constructions are re-exported from the stage core.
This module proves the rational localization step before common-stage descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v r s u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped TensorProduct
local instance (priority := 5000) instEssentiallySmallProEt_automorphismRationalShiftDescent
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] sfIntrinsicModuleEquivalence
  HasDerivedCategory.standard integralDerivedPullback scalarReductionExistence
  scalarReductionDerivedExistence completedIntegralCoefficientSheafUnrestricted

set_option allowUnsafeReducibility true in
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

set_option allowUnsafeReducibility true in
attribute [local irreducible] constructibleIntegralPullback
  rationalDerivedPullback commonStageDerivedPullback

private theorem map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem dependent_app_heq {A : Sort*} {B : A → Sort*}
    (f : (a : A) → B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

private theorem localization_shift_map (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) {J J' : sfIntegralConstructibleCategory l E W} (f : J ⟶ J') :
    HEq (((sfRationalConstructibleLocalization l E W).map f)⟦(1 : ℤ)⟧')
      ((sfRationalConstructibleLocalization l E W).map (f⟦(1 : ℤ)⟧')) := by
  have hshift := (sfRationalTriangulationDatum l E W).choose_spec.choose_spec.1
  refine (Functor.hcongr_hom hshift
    ((sfRationalConstructibleLocalization l E W).map f)).trans ?_
  apply heq_of_eq
  change ScalarLocalization.mapHom _ _ _ (shiftFunctor _ (1 : ℤ)) _ _ (1 ⊗ₜ f) = _
  simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul]
  rfl

private theorem localization_shift_obj (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (J : sfRationalConstructibleCategory l E W) :
    J⟦(1 : ℤ)⟧ = (sfRationalConstructibleLocalization l E W).obj (J.obj⟦(1 : ℤ)⟧) :=
  Functor.congr_obj (sfRationalTriangulationDatum l E W).choose_spec.choose_spec.1 J

private theorem rational_obj
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E X) :
    (rationalDerivedPullback l E f).obj K =
      (sfRationalConstructibleLocalization l E Y).obj
        ((constructibleIntegralPullback l E f).obj K.obj) := by
  simpa only [rationalDerivedPullback, sfRationalConstructibleLocalization,
    ScalarLocalization.localization] using
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K

private theorem rational_map
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {K M : sfIntegralConstructibleCategory l E X} (a : K ⟶ M) :
    HEq ((rationalDerivedPullback l E f).map
      ((sfRationalConstructibleLocalization l E X).map a))
      ((sfRationalConstructibleLocalization l E Y).map
        ((constructibleIntegralPullback l E f).map a)) := by
  unfold rationalDerivedPullback
  have hm := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K M a 1
  dsimp only [sfRationalConstructibleLocalization, ScalarLocalization.localization] at hm ⊢
  with_unfolding_all exact hm

private theorem rational_composite_obj
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfRationalConstructibleCategory l E X) :
    (rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E g).obj K =
      (sfRationalConstructibleLocalization l E Z).obj
        ((constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E g).obj
          K.obj) :=
  (congrArg (rationalDerivedPullback l E g).obj (rational_obj l E f K)).trans
    (rational_obj l E g _)

private theorem rational_composite_shift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [(constructibleIntegralPullback l E f).CommShift ℤ]
    [(constructibleIntegralPullback l E g).CommShift ℤ]
    [(rationalDerivedPullback l E f).CommShift ℤ]
    [(rationalDerivedPullback l E g).CommShift ℤ]
    (hf : ∀ K : sfRationalConstructibleCategory l E X,
      HEq (((rationalDerivedPullback l E f).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l E Y).map
          (((constructibleIntegralPullback l E f).commShiftIso (1 : ℤ)).hom.app K.obj)))
    (hg : ∀ K : sfRationalConstructibleCategory l E Y,
      HEq (((rationalDerivedPullback l E g).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l E Z).map
          (((constructibleIntegralPullback l E g).commShiftIso (1 : ℤ)).hom.app K.obj)))
    (K : sfRationalConstructibleCategory l E X) :
    HEq (((rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E g).commShiftIso
      (1 : ℤ)).hom.app K)
      ((sfRationalConstructibleLocalization l E Z).map
        (((constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E g).commShiftIso
          (1 : ℤ)).hom.app K.obj)) := by
  let A := constructibleIntegralPullback l E f
  let B := constructibleIntegralPullback l E g
  let Ar := rationalDerivedPullback l E f
  let Br := rationalDerivedPullback l E g
  let Q (W : Scheme.{u}) := sfRationalConstructibleLocalization l E W
  have cX := localization_shift_obj l E X
  have cY := localization_shift_obj l E Y
  have cZ := localization_shift_obj l E Z
  have oA := rational_obj l E f K
  have srcA := (congrArg Ar.obj (cX K)).trans (rational_obj l E f _)
  have tgtA := (cY (Ar.obj K)).trans
    (congrArg (Q Y).obj (congrArg (fun J ↦ J.obj⟦(1 : ℤ)⟧) oA))
  have hm := (map_heq Br srcA tgtA (hf K)).trans
    (rational_map l E g ((A.commShiftIso (1 : ℤ)).hom.app K.obj))
  have hn := (dependent_app_heq
    (fun J ↦ (Br.commShiftIso (1 : ℤ)).hom.app J) oA).trans (hg _)
  have src := (congrArg (Ar ⋙ Br).obj (cX K)).trans (rational_composite_obj l E f g _)
  have mid := (congrArg Br.obj tgtA).trans (rational_obj l E g _)
  have tgt := (congrArg (shiftFunctor _ (1 : ℤ)).obj
    (rational_composite_obj l E f g K)).trans (cZ _)
  dsimp only [Q, sfRationalConstructibleLocalization, ScalarLocalization.localization,
    Functor.comp_obj] at srcA tgtA src mid tgt
  simpa only [A, B, Ar, Br, sfRationalConstructibleLocalization,
    ScalarLocalization.localization, Functor.commShiftIso_comp_hom_app, Functor.map_comp] using
    (heq_comp src mid tgt hm hn)

private theorem rational_square_shift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom)
    [(constructibleIntegralPullback l E f).CommShift ℤ]
    [(constructibleIntegralPullback l E eX.asIso.hom).CommShift ℤ]
    [(constructibleIntegralPullback l E eY.asIso.hom).CommShift ℤ]
    [(rationalDerivedPullback l E f).CommShift ℤ]
    [(rationalDerivedPullback l E eX.asIso.hom).CommShift ℤ]
    [(rationalDerivedPullback l E eY.asIso.hom).CommShift ℤ]
    (hf : ∀ K : sfRationalConstructibleCategory l E X,
      HEq (((rationalDerivedPullback l E f).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l E Y).map
          (((constructibleIntegralPullback l E f).commShiftIso (1 : ℤ)).hom.app K.obj)))
    (hx : ∀ K : sfRationalConstructibleCategory l E X,
      HEq (((rationalDerivedPullback l E eX.asIso.hom).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l E X).map
          (((constructibleIntegralPullback l E eX.asIso.hom).commShiftIso (1 : ℤ)).hom.app K.obj)))
    (hy : ∀ K : sfRationalConstructibleCategory l E Y,
      HEq (((rationalDerivedPullback l E eY.asIso.hom).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l E Y).map
          (((constructibleIntegralPullback l E eY.asIso.hom).commShiftIso (1 : ℤ)).hom.app K.obj)))
    [NatTrans.CommShift (automorphismStageIntegralSquare l E C f eX eY h).hom ℤ] :
    NatTrans.CommShift (automorphismStageRationalSquare l E C f eX eY h).hom ℤ := by
  apply commShift_of_one
  constructor
  ext K
  let A := constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E eY.asIso.hom
  let B := constructibleIntegralPullback l E eX.asIso.hom ⋙ constructibleIntegralPullback l E f
  let Ar := rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E eY.asIso.hom
  let Br := rationalDerivedPullback l E eX.asIso.hom ⋙ rationalDerivedPullback l E f
  let Q := sfRationalConstructibleLocalization l E Y
  let α := automorphismStageIntegralSquare l E C f eX eY h
  let β := automorphismStageRationalSquare l E C f eX eY h
  have oA := rational_composite_obj l E f eY.asIso.hom
  have oB := rational_composite_obj l E eX.asIso.hom f
  have cx := localization_shift_obj l E X
  have cy := localization_shift_obj l E Y
  have hb (J : sfRationalConstructibleCategory l E X) :
      HEq (β.hom.app J) (Q.map (α.hom.app J.obj)) :=
    (automorphismStageRationalSquare_existsUnique l E C f eX eY h).exists.choose_spec J
  have hn := (dependent_app_heq β.hom.app (cx K)).trans (hb _)
  have hm := (map_heq (shiftFunctor _ (1 : ℤ)) (oA K) (oB K) (hb K)).trans
    (localization_shift_map l E Y (α.hom.app K.obj))
  have srcA := (congrArg Ar.obj (cx K)).trans (oA _)
  have srcB := (congrArg Br.obj (cx K)).trans (oB _)
  have tgtA := (congrArg (shiftFunctor _ (1 : ℤ)).obj (oA K)).trans (cy _)
  have tgtB := (congrArg (shiftFunctor _ (1 : ℤ)).obj (oB K)).trans (cy _)
  dsimp only [sfRationalConstructibleLocalization, ScalarLocalization.localization,
    Functor.comp_obj] at srcA srcB tgtA tgtB
  have hl := heq_comp srcA tgtA tgtB (rational_composite_shift l E f eY.asIso.hom hf hy K) hm
  have hr := heq_comp srcA srcB tgtB hn (rational_composite_shift l E eX.asIso.hom f hx hf K)
  have he := congrArg Q.map (NatTrans.shift_app_comm α.hom (1 : ℤ) K.obj)
  simp only [Functor.map_comp] at he
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact eq_of_heq (hl.trans ((heq_of_eq he).trans hr.symm))

/-- Rational localization of the three normalized integral pullbacks preserves their square.
Source: current blueprint, Weil-structures paragraph, rationalization step.
(blueprint: lem-sf-automorphism-rational-shift-descent).
Proof: take the signed integral shift witness, localize each exact linear pullback,
and apply rational localization to the integral square equation at shift one.
The integer shift coherence laws extend that equation to every integer. -/
theorem automorphismRationalShiftDescent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.asIso.hom ≫ f = f ≫ eX.asIso.hom) :
      ∃ (cf : (rationalDerivedPullback l E f).CommShift ℤ)
        (cX : (rationalDerivedPullback l E eX.asIso.hom).CommShift ℤ)
        (cY : (rationalDerivedPullback l E eY.asIso.hom).CommShift ℤ),
        automorphismStageRationalShiftNormalization l E f cf ∧
        automorphismStageRationalShiftNormalization l E eX.asIso.hom cX ∧
        automorphismStageRationalShiftNormalization l E eY.asIso.hom cY ∧
        (fun [sf : (rationalDerivedPullback l E f).CommShift ℤ]
          [sX : (rationalDerivedPullback l E eX.asIso.hom).CommShift ℤ]
          [sY : (rationalDerivedPullback l E eY.asIso.hom).CommShift ℤ] ↦
          (rationalDerivedPullback l E f).IsTriangulated ∧
            (rationalDerivedPullback l E eX.asIso.hom).IsTriangulated ∧
            (rationalDerivedPullback l E eY.asIso.hom).IsTriangulated ∧
            NatTrans.CommShift (automorphismStageRationalSquare l E C f eX eY h).hom ℤ)
          (sf := cf) (sX := cX) (sY := cY) := by
  classical
  obtain ⟨sf, sx, sy, nf, nx, ny, he⟩ :=
    (automorphismConstructibleStage_integral_shifts l E C f eX eY h).2
  let := sf
  let := sx
  let := sy
  let := he.1
  let := he.2.1
  let := he.2.2.1
  let := he.2.2.2
  have hlin {U V : Scheme.{u}} (g : U ⟶ V)
      [∀ u : U, Invertible (l : U.residueField u)]
      [∀ v : V, Invertible (l : V.residueField v)] :
      (constructibleIntegralPullback l E g).Linear
        (Padic.coefficientExtensionIntegers l E) := by
    let := (integralDerivedPullback_linear l E g).2
    let P := sfIntegralConstructible l E U
    let Q := sfIntegralConstructible l E V
    let : (Q.ι ⋙ integralDerivedPullback l E g).Linear
        (Padic.coefficientExtensionIntegers l E) := inferInstance
    constructor
    intro K M a c
    apply P.ι.map_injective
    rw [P.ι.map_smul]
    with_unfolding_all change (Q.ι ⋙ integralDerivedPullback l E g).map (c • a) =
      c • (Q.ι ⋙ integralDerivedPullback l E g).map a
    exact (Q.ι ⋙ integralDerivedPullback l E g).map_smul c a
  let := hlin f
  let := hlin eX.asIso.hom
  let := hlin eY.asIso.hom
  obtain ⟨rf, ef, hf, bf, nbf, sbf⟩ := rationalPullbackShiftLocalization l E f
  obtain ⟨rx, ex, hx, bx, nbx, sbx⟩ := rationalPullbackShiftLocalization l E eX.asIso.hom
  obtain ⟨ry, ey, hy, by_, nby, sby⟩ := rationalPullbackShiftLocalization l E eY.asIso.hom
  let := rf
  let := rx
  let := ry
  refine ⟨rf, rx, ry, ⟨sf, nf, hf, bf, nbf, sbf⟩,
    ⟨sx, nx, hx, bx, nbx, sbx⟩, ⟨sy, ny, hy, by_, nby, sby⟩,
    ef, ex, ey, ?_⟩
  exact rational_square_shift l E C f eX eY h
    hf hx hy

end WeilConjectures
