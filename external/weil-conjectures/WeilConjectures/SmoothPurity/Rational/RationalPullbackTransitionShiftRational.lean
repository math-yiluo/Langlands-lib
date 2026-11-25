/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
public import WeilConjectures.Mathlib.CategoryTheory.EqToHom
import all WeilConjectures.SmoothPurity.Sf.SfRationalScalarExactOfIntegral
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-! # Shift compatibility of the rational pullback scalar comparison

A functor on rational constructible objects which reproduces an integral model on objects
and morphisms is identified with it by an identity-component comparison
(`CategoryTheory.NatIso.ofObjEqOfMapHEq`); this comparison commutes with shifts once the
degree-one shifts agree (`rationalOfObjEqOfMapHEq_commShift`). Since every rational
constructible object is a localization, the rational pullback scalar comparison commutes with
the normalized rational shifts once its integral model does
(`rationalPullbackScalarComparison_commShift`).

This is the rational step of the proof of `rationalPullbackTransitionShift`.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph.
(blueprint: lem-sf-rational-pullback-transition-shift).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
attribute [local irreducible] constructibleIntegralPullback rationalDerivedPullback

/-- The identity-component comparison commutes with shifts once the degree-one shift
of the localized functor is the localization of the integral one. -/
theorem ofObjEqOfMapHEq_commShift {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D'] [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ]
    [HasShift D' ℤ] (Q : C ⥤ C') (Q' : D ⥤ D') (T : C ⥤ D) (F : C' ⥤ D')
    [Q.CommShift ℤ] [Q'.CommShift ℤ] [T.CommShift ℤ] [F.CommShift ℤ]
    (hF : ∀ X, F.obj (Q.obj X) = Q'.obj (T.obj X))
    (hm : ∀ {X Y : C} (f : X ⟶ Y), HEq (F.map (Q.map f)) (Q'.map (T.map f)))
    (hQ : ∀ X, Q.obj (X⟦(1 : ℤ)⟧) = (Q.obj X)⟦(1 : ℤ)⟧)
    (hQ' : ∀ X, Q'.obj (X⟦(1 : ℤ)⟧) = (Q'.obj X)⟦(1 : ℤ)⟧)
    (nQ : ∀ X, HEq ((Q.commShiftIso (1 : ℤ)).hom.app X) (𝟙 (Q.obj (X⟦(1 : ℤ)⟧))))
    (nQ' : ∀ X, HEq ((Q'.commShiftIso (1 : ℤ)).hom.app X) (𝟙 (Q'.obj (X⟦(1 : ℤ)⟧))))
    (nF : ∀ X, HEq ((F.commShiftIso (1 : ℤ)).hom.app (Q.obj X))
      (Q'.map ((T.commShiftIso (1 : ℤ)).hom.app X))) :
    NatTrans.CommShift (NatIso.ofObjEqOfMapHEq (F := Q ⋙ F) (G := T ⋙ Q') hF hm).hom ℤ :=
  commShift_of_one _
    (localized_comparison_core Q Q' T F hF _ (fun _ ↦ rfl) hQ hQ' nQ nQ' nF)

/-- The rationalization of a shift-compatible integral functor: the identity-component
comparison with a rational functor normalized at shift one commutes with all shifts. -/
theorem rationalOfObjEqOfMapHEq_commShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (E' : Type u) [Field E'] [Algebra ℚ_[l] E'] [FiniteDimensional ℚ_[l] E']
    (W W' : Scheme.{u})
    (T : sfIntegralConstructibleCategory l E W ⥤ sfIntegralConstructibleCategory l E' W')
    (F : sfRationalConstructibleCategory l E W ⥤ sfRationalConstructibleCategory l E' W')
    [T.CommShift ℤ] [F.CommShift ℤ]
    (hF : ∀ X, F.obj ((sfRationalConstructibleLocalization l E W).obj X) =
      (sfRationalConstructibleLocalization l E' W').obj (T.obj X))
    (hm : ∀ {X Y} (f : X ⟶ Y), HEq (F.map ((sfRationalConstructibleLocalization l E W).map f))
      ((sfRationalConstructibleLocalization l E' W').map (T.map f)))
    (nF : ∀ X, HEq ((F.commShiftIso (1 : ℤ)).hom.app
        ((sfRationalConstructibleLocalization l E W).obj X))
      ((sfRationalConstructibleLocalization l E' W').map
        ((T.commShiftIso (1 : ℤ)).hom.app X))) :
    NatTrans.CommShift (NatIso.ofObjEqOfMapHEq (F := sfRationalConstructibleLocalization l E W ⋙ F)
      (G := T ⋙ sfRationalConstructibleLocalization l E' W') hF hm).hom ℤ :=
  ofObjEqOfMapHEq_commShift _ _ T F hF hm
    (fun X ↦ (Functor.congr_obj (sfRationalTriangulationDatum l E W).choose_spec.choose_spec.1
      ((sfRationalConstructibleLocalization l E W).obj X)).symm)
    (fun X ↦ (Functor.congr_obj (sfRationalTriangulationDatum l E' W').choose_spec.choose_spec.1
      ((sfRationalConstructibleLocalization l E' W').obj X)).symm)
    ((sfRationalTriangulationDatum l E W).choose_spec.choose_spec.2
      |>.choose_spec.choose_spec.1)
    ((sfRationalTriangulationDatum l E' W').choose_spec.choose_spec.2
      |>.choose_spec.choose_spec.1)
    nF

/-- The whiskered comparison `Q ◁ β` factors through the identity-component comparisons
once `β` reproduces `α` on localized objects. -/
private theorem whiskerLeft_hom_eq_ofObjEqOfMapHEq
    {IX IY ILX ILY RX RY RLX RLY : Type*} [Category* IX] [Category* IY] [Category* ILX]
    [Category* ILY] [Category* RX] [Category* RY] [Category* RLX] [Category* RLY]
    (QX : IX ⥤ RX) (QY : IY ⥤ RY) (QLX : ILX ⥤ RLX) (QLY : ILY ⥤ RLY)
    (A : IX ⥤ IY) (B : ILX ⥤ ILY) (Ar : RX ⥤ RY) (Br : RLX ⥤ RLY)
    (SX : IX ⥤ ILX) (SY : IY ⥤ ILY) (TX : RX ⥤ RLX) (TY : RY ⥤ RLY)
    (α : A ⋙ SY ≅ SX ⋙ B) (β : Ar ⋙ TY ≅ TX ⋙ Br)
    (oA : ∀ J, Ar.obj (QX.obj J) = QY.obj (A.obj J))
    (mA : ∀ {J J' : IX} (a : J ⟶ J'), HEq (Ar.map (QX.map a)) (QY.map (A.map a)))
    (oB : ∀ J, Br.obj (QLX.obj J) = QLY.obj (B.obj J))
    (mB : ∀ {J J' : ILX} (a : J ⟶ J'), HEq (Br.map (QLX.map a)) (QLY.map (B.map a)))
    (oTX : ∀ J, TX.obj (QX.obj J) = QLX.obj (SX.obj J))
    (mTX : ∀ {J J' : IX} (a : J ⟶ J'), HEq (TX.map (QX.map a)) (QLX.map (SX.map a)))
    (oTY : ∀ J, TY.obj (QY.obj J) = QLY.obj (SY.obj J))
    (mTY : ∀ {J J' : IY} (a : J ⟶ J'), HEq (TY.map (QY.map a)) (QLY.map (SY.map a)))
    (hb : ∀ K, HEq (β.hom.app (QX.obj K)) (QLY.map (α.hom.app K))) :
    Functor.whiskerLeft QX β.hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (NatIso.ofObjEqOfMapHEq (F := QX ⋙ Ar) (G := A ⋙ QY) oA mA).hom
          TY ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft A
          (NatIso.ofObjEqOfMapHEq (F := QY ⋙ TY) (G := SY ⋙ QLY) oTY mTY).hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α.hom QLY ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft SX
          (NatIso.ofObjEqOfMapHEq (F := QLX ⋙ Br) (G := B ⋙ QLY) oB mB).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (NatIso.ofObjEqOfMapHEq (F := QX ⋙ TX) (G := SX ⋙ QLX) oTX mTX).inv
          Br ≫
        (Functor.associator _ _ _).hom := by
  ext K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id, NatIso.ofObjEqOfMapHEq_hom_app,
    NatIso.ofObjEqOfMapHEq_inv_app]
  exact eq_of_heq ((hb K).trans
    (map_eqToHom_conj_heq TY Br _ _ (QLY.map (α.hom.app K)) _ _).symm)

/-- The whiskered comparison `Q ◁ β` commutes with shifts once the identity-component
comparisons and `α` do, provided `β` reproduces `α` on localized objects. -/
private theorem whiskerLeft_commShift_of_ofObjEqOfMapHEq
    {IX IY ILX ILY RX RY RLX RLY : Type*} [Category* IX] [Category* IY] [Category* ILX]
    [Category* ILY] [Category* RX] [Category* RY] [Category* RLX] [Category* RLY]
    [HasShift IX ℤ] [HasShift IY ℤ] [HasShift ILX ℤ] [HasShift ILY ℤ] [HasShift RX ℤ]
    [HasShift RY ℤ] [HasShift RLX ℤ] [HasShift RLY ℤ]
    (QX : IX ⥤ RX) (QY : IY ⥤ RY) (QLX : ILX ⥤ RLX) (QLY : ILY ⥤ RLY)
    (A : IX ⥤ IY) (B : ILX ⥤ ILY) (Ar : RX ⥤ RY) (Br : RLX ⥤ RLY)
    (SX : IX ⥤ ILX) (SY : IY ⥤ ILY) (TX : RX ⥤ RLX) (TY : RY ⥤ RLY)
    [QX.CommShift ℤ] [QY.CommShift ℤ] [QLX.CommShift ℤ] [QLY.CommShift ℤ] [A.CommShift ℤ]
    [B.CommShift ℤ] [Ar.CommShift ℤ] [Br.CommShift ℤ] [SX.CommShift ℤ] [SY.CommShift ℤ]
    [TX.CommShift ℤ] [TY.CommShift ℤ]
    (α : A ⋙ SY ≅ SX ⋙ B) (β : Ar ⋙ TY ≅ TX ⋙ Br) [NatTrans.CommShift α.hom ℤ]
    (oA : ∀ J, Ar.obj (QX.obj J) = QY.obj (A.obj J))
    (mA : ∀ {J J' : IX} (a : J ⟶ J'), HEq (Ar.map (QX.map a)) (QY.map (A.map a)))
    (oB : ∀ J, Br.obj (QLX.obj J) = QLY.obj (B.obj J))
    (mB : ∀ {J J' : ILX} (a : J ⟶ J'), HEq (Br.map (QLX.map a)) (QLY.map (B.map a)))
    (oTX : ∀ J, TX.obj (QX.obj J) = QLX.obj (SX.obj J))
    (mTX : ∀ {J J' : IX} (a : J ⟶ J'), HEq (TX.map (QX.map a)) (QLX.map (SX.map a)))
    (oTY : ∀ J, TY.obj (QY.obj J) = QLY.obj (SY.obj J))
    (mTY : ∀ {J J' : IY} (a : J ⟶ J'), HEq (TY.map (QY.map a)) (QLY.map (SY.map a)))
    [NatTrans.CommShift (NatIso.ofObjEqOfMapHEq (F := QX ⋙ Ar) (G := A ⋙ QY) oA mA).hom ℤ]
    [NatTrans.CommShift (NatIso.ofObjEqOfMapHEq (F := QLX ⋙ Br) (G := B ⋙ QLY) oB mB).hom ℤ]
    [NatTrans.CommShift (NatIso.ofObjEqOfMapHEq (F := QX ⋙ TX) (G := SX ⋙ QLX) oTX mTX).hom ℤ]
    [NatTrans.CommShift (NatIso.ofObjEqOfMapHEq (F := QY ⋙ TY) (G := SY ⋙ QLY) oTY mTY).hom ℤ]
    (hb : ∀ K, HEq (β.hom.app (QX.obj K)) (QLY.map (α.hom.app K))) :
    NatTrans.CommShift (Functor.whiskerLeft QX β.hom) ℤ := by
  rw [whiskerLeft_hom_eq_ofObjEqOfMapHEq QX QY QLX QLY A B Ar Br SX SY TX TY α β oA mA oB mB
    oTX mTX oTY mTY hb]
  infer_instance

attribute [local irreducible] rationalPullbackScalarComparison

-- Prove the comparison for finite coefficient fields before specializing to their small models.
set_option backward.isDefEq.respectTransparency true in
private theorem rationalPullbackScalarComparison_commShift_of_finiteCoefficients
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [(constructibleIntegralPullback l E f).CommShift ℤ]
    [(constructibleIntegralPullback l L f).CommShift ℤ]
    [(rationalDerivedPullback l E f).CommShift ℤ]
    [(rationalDerivedPullback l L f).CommShift ℤ]
    [iX : (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).CommShift ℤ]
    [iY : (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).CommShift ℤ]
    [tX : (sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L
      ι).CommShift ℤ]
    [tY : (sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L
      ι).CommShift ℤ]
    (ntX : ∀ K : sfRationalConstructibleCategory l E X,
      HEq (((sfRationalScalarExtension l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L
        ι).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l L X).map
          (((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (ntY : ∀ K : sfRationalConstructibleCategory l E Y,
      HEq (((sfRationalScalarExtension l E Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L
        ι).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l L Y).map
          (((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (nE : ∀ K : sfRationalConstructibleCategory l E X,
      HEq (((rationalDerivedPullback l E f).commShiftIso
        (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l E Y).map
          (((constructibleIntegralPullback l E f).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (nL : ∀ K : sfRationalConstructibleCategory l L X,
      HEq (((rationalDerivedPullback l L f).commShiftIso
        (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l L Y).map
          (((constructibleIntegralPullback l L f).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (α : constructibleIntegralPullback l E f ⋙
        sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι Y ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X ⋙
        constructibleIntegralPullback l L f)
    (hα : ∀ K, α.app K = integralPullbackScalarComparison l E
      L ι f K)
    (hs : NatTrans.CommShift α.hom ℤ) :
    @NatTrans.CommShift _ _ _ _ _ _ (rationalPullbackScalarComparison l E
        L ι f).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ tY)
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ tX _) := by
  let A := constructibleIntegralPullback l E f
  let B := constructibleIntegralPullback l L f
  let Ar := rationalDerivedPullback l E f
  let Br := rationalDerivedPullback l L f
  let S (W : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let T (W : Scheme.{u}) := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L
    ι
  let Q (W : Scheme.{u}) := sfRationalConstructibleLocalization l E W
  let QL (W : Scheme.{u}) := sfRationalConstructibleLocalization l L W
  have oA (J : sfIntegralConstructibleCategory l E X) :
      Ar.obj ((Q X).obj J) = (Q Y).obj (A.obj J) := by
    simpa only [Ar, A, Q, rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1
        ((Q X).obj J)
  have oB (J : sfIntegralConstructibleCategory l L X) :
      Br.obj ((QL X).obj J) = (QL Y).obj (B.obj J) := by
    simpa only [Br, B, QL, rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l L f).exists.choose_spec.2.1
        ((QL X).obj J)
  have oT (W : Scheme.{u}) (J : sfIntegralConstructibleCategory l E W) :
      (T W).obj ((Q W).obj J) = (QL W).obj ((S W).obj J) := by
    simpa only [T, S, QL, Q,
      sfRationalScalarExtension, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (sfRationalScalarExtension_existsUnique l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L
      ι).exists.choose_spec.2.1 ((Q W).obj J)
  have mA {J J' : sfIntegralConstructibleCategory l E X}
      (a : J ⟶ J') : HEq (Ar.map ((Q X).map a)) ((Q Y).map (A.map a)) := by
    simp only [Ar, A, Q, sfRationalConstructibleLocalization, ScalarLocalization.localization]
    delta rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l
      E f).exists.choose_spec.2.2 J J' a 1
  have mB {J J' : sfIntegralConstructibleCategory l L X}
      (a : J ⟶ J') : HEq (Br.map ((QL X).map a)) ((QL Y).map (B.map a)) := by
    simp only [Br, B, QL, sfRationalConstructibleLocalization, ScalarLocalization.localization]
    delta rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l
      L f).exists.choose_spec.2.2 J J' a 1
  have mT (W : Scheme.{u}) {J J' : sfIntegralConstructibleCategory l E W}
      (a : J ⟶ J') : HEq ((T W).map ((Q W).map a)) ((QL W).map ((S W).map a)) := by
    have hh := sfRationalScalarExtension_map_tmul l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L
      ι J J' a 1
    simp only [T, Q, QL, S,
      sfRationalConstructibleLocalization, ScalarLocalization.localization, map_one] at hh ⊢
    convert hh using 1
    rfl
  let eA := NatIso.ofObjEqOfMapHEq (F := Q X ⋙ Ar) (G := A ⋙ Q Y) oA mA
  let eB := NatIso.ofObjEqOfMapHEq (F := QL X ⋙ Br) (G := B ⋙ QL Y) oB mB
  let eTX := NatIso.ofObjEqOfMapHEq (F := Q X ⋙ T X) (G := S X ⋙ QL X) (oT X) (mT X)
  let eTY := NatIso.ofObjEqOfMapHEq (F := Q Y ⋙ T Y) (G := S Y ⋙ QL Y) (oT Y) (mT Y)
  have : NatTrans.CommShift eA.hom ℤ :=
    rationalOfObjEqOfMapHEq_commShift l E E
      X Y A Ar oA mA (fun J ↦ nE ((Q X).obj J))
  have : NatTrans.CommShift eB.hom ℤ :=
    rationalOfObjEqOfMapHEq_commShift l L L
      X Y B Br oB mB (fun J ↦ nL ((QL X).obj J))
  have : NatTrans.CommShift eTX.hom ℤ :=
    rationalOfObjEqOfMapHEq_commShift l E L
      X X (S X) (T X) (oT X) (mT X)
      (fun J ↦ ntX ((Q X).obj J))
  have : NatTrans.CommShift eTY.hom ℤ :=
    rationalOfObjEqOfMapHEq_commShift l E L
      Y Y (S Y) (T Y) (oT Y) (mT Y)
      (fun J ↦ ntY ((Q Y).obj J))
  let β := rationalPullbackScalarComparison l E
    L ι f
  have : NatTrans.CommShift (Functor.whiskerLeft (Q X) β.hom) ℤ := by
    refine whiskerLeft_commShift_of_ofObjEqOfMapHEq (Q X) (Q Y) (QL X) (QL Y) A B Ar Br (S X)
      (S Y) (T X) (T Y) α β oA mA oB mB (oT X) (mT X) (oT Y) (mT Y) fun K ↦ ?_
    have hb : HEq (β.hom.app ((Q X).obj K)) ((QL Y).map (integralPullbackScalarComparison l
        E L ι
        f K).hom) := by
      dsimp only [β]
      delta rationalPullbackScalarComparison
      exact (rationalPullbackScalarComparison_existsUnique l E
        L ι f).exists.choose_spec
        ((Q X).obj K)
    exact hb.trans (heq_of_eq (congrArg (QL Y).map (congrArg Iso.hom (hα K)).symm))
  refine NatTrans.CommShift.of_whiskerLeft β.hom (Q X) fun K ↦ ?_
  obtain ⟨J, rfl⟩ : ∃ J, (Q X).obj J = K := ⟨K.obj, rfl⟩
  exact ⟨J, 𝟙 _, inferInstance⟩

/-- The rational pullback scalar comparison commutes with the normalized rational shifts,
given the shift compatibility of its integral model.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph
(blueprint: lem-sf-rational-pullback-transition-shift). -/
theorem rationalPullbackScalarComparison_commShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Index l Ω) (h : E ≤ L)
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [(constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    [(rationalDerivedPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [(rationalDerivedPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    [iX : (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h).CommShift ℤ]
    [iY : (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h).CommShift ℤ]
    [tX : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).CommShift ℤ]
    [tY : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).CommShift ℤ]
    (ntX : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X,
      HEq (((sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h)).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).map
          (((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (ntY : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y,
      HEq (((sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h)).commShiftIso (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
          (((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (nE : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X,
      HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).commShiftIso
        (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
          (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (nL : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) X,
      HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω L) f).commShiftIso
        (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
          (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (α : constructibleIntegralPullback l (Coefficient.{u} l Ω E) f ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ⋙
        constructibleIntegralPullback l (Coefficient.{u} l Ω L) f)
    (hα : ∀ K, α.app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f K)
    (hs : NatTrans.CommShift α.hom ℤ) :
    @NatTrans.CommShift _ _ _ _ _ _ (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ tY)
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ tX _) := by
  exact rationalPullbackScalarComparison_commShift_of_finiteCoefficients
    (iX := iX) (iY := iY) (tX := tX) (tY := tY)
    l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) f ntX ntY nE nL α hα hs

end WeilConjectures
