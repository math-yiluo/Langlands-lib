/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalPullbackStageCoherence
public import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs

/-! # Normalization of the restriction tensor mixed square

Proved helper for restriction tensor representative stage transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory Stage transition

set_option allowUnsafeReducibility true in
attribute [local reducible] stageSystem

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5

namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  ScalarLocalization.category ScalarLocalization.composition
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue sfRationalScalarComp
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.normalizedAssociator
  AlgebraicallyClosedCoefficients.coefficientInclusion
  ObjectProperty.FullSubcategory.category sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  sfRationalScalarExtension
  rationalPullbackScalarComparison rationalTensorScalarComparison

private theorem mixed_square_transport
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (R : C ⥤ D) (R' : E ⥤ F) (S S₀ : C ⥤ E) (T T₀ : D ⥤ F)
    (eS : S = S₀) (eT : T = T₀)
    (U : C × C ⥤ C) (V : D × D ⥤ D)
    (U' : E × E ⥤ E) (V' : F × F ⥤ F)
    (b : R ⋙ T₀ ≅ S₀ ⋙ R')
    (t : U ⋙ S₀ ≅ S₀.prod S₀ ⋙ U') (q : V ⋙ T₀ ≅ T₀.prod T₀ ⋙ V')
    (mu : U ⋙ R ≅ R.prod R ⋙ V) (nu : U' ⋙ R' ≅ R'.prod R' ⋙ V')
    (square : ∀ M N,
      T₀.map (mu.hom.app (M, N)) ≫ q.hom.app (R.obj M, R.obj N) ≫
          V'.map (Prod.mkHom (b.hom.app M) (b.hom.app N)) =
        b.hom.app (U.obj (M, N)) ≫ R'.map (t.hom.app (M, N)) ≫
          nu.hom.app (S₀.obj M, S₀.obj N)) :
    let b' := Functor.isoWhiskerLeft R (eqToIso eT) ≪≫ b ≪≫
      Functor.isoWhiskerRight (eqToIso eS).symm R'
    let t' := Functor.isoWhiskerLeft U (eqToIso eS) ≪≫ t ≪≫
      Functor.isoWhiskerRight (NatIso.prod (eqToIso eS).symm (eqToIso eS).symm) U'
    let q' := Functor.isoWhiskerLeft V (eqToIso eT) ≪≫ q ≪≫
      Functor.isoWhiskerRight (NatIso.prod (eqToIso eT).symm (eqToIso eT).symm) V'
    ∀ M N,
      T.map (mu.hom.app (M, N)) ≫ q'.hom.app (R.obj M, R.obj N) ≫
          V'.map (Prod.mkHom (b'.hom.app M) (b'.hom.app N)) =
        b'.hom.app (U.obj (M, N)) ≫ R'.map (t'.hom.app (M, N)) ≫
          nu.hom.app (S.obj M, S.obj N) := by
  subst S₀ T₀
  have hS : NatIso.prod (Iso.refl S) (Iso.refl S) = Iso.refl (S.prod S) := rfl
  have hT : NatIso.prod (Iso.refl T) (Iso.refl T) = Iso.refl (T.prod T) := rfl
  simpa only [eqToIso_refl, Functor.isoWhiskerLeft_refl, Iso.refl_symm,
    Functor.isoWhiskerRight_refl, hS, hT, Iso.refl_trans, Iso.trans_refl]
    using square

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The given scalar mixed square holds for the normalized stage comparisons.

Source: lemma-section-normal-bundle--1, common-stage subargument, steps 3–5.
Proof: The stage system transition is equal to the specified scalar extension functor.
Substitute these two functor equalities in the mixed square. The conjugating eqToIso
isomorphisms are then reflexive, so whiskering and composition with them cancel.
The resulting square is the square of the normalized stage comparisons.
(blueprint: lem-pur-restriction-tensor-normalized-square). -/
theorem restrictionTensorNormalizedSquare
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    let R := fun E : Index l Ω ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f
    let T := fun (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (E : Index l Ω) ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) W
    let b := fun (E L : Index l Ω) (h : E ≤ L) ↦
      rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f
    let theta := fun (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (E L : Index l Ω) (h : E ≤ L) ↦
      rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W
    let SX := stageSystem l Ω X
    let SY := stageSystem l Ω Y
    let p := fun {E K : Index l Ω} (h : E ≤ K) ↦
      rationalPullbackStageComparison l Ω f h
    let t := fun (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      {E K : Index l Ω} (h : E ≤ K) ↦ rationalTensorStageComparison l Ω W h
    ∀ (mu : ∀ E : Index l Ω, T X E ⋙ R E ≅ (R E).prod (R E) ⋙ T Y E),
      (∀ (E L : Index l Ω) (h : E ≤ L) (M N : Stage l Ω X E),
        (transition l Ω Y E L h).map ((mu E).hom.app (M, N)) ≫
          (theta Y E L h).hom.app ((R E).obj M, (R E).obj N) ≫
          (T Y L).map (Prod.mkHom ((b E L h).hom.app M) ((b E L h).hom.app N)) =
        (b E L h).hom.app ((T X E).obj (M, N)) ≫
          (R L).map ((theta X E L h).hom.app (M, N)) ≫
          (mu L).hom.app ((transition l Ω X E L h).obj M,
            (transition l Ω X E L h).obj N)) →
      ∀ (E K : Index l Ω) (k : E ≤ K) (M N : Stage l Ω X E),
        (SY.T k).map ((mu E).hom.app (M, N)) ≫
            (t Y k).hom.app ((R E).obj M, (R E).obj N) ≫
            (T Y K).map (Prod.mkHom ((p k).hom.app M) ((p k).hom.app N)) =
          (p k).hom.app ((T X E).obj (M, N)) ≫
            (R K).map ((t X k).hom.app (M, N)) ≫
            (mu K).hom.app ((SX.T k).obj M, (SX.T k).obj N) := by
  intro R T b theta SX SY p t mu mixed E K k
  have eX : SX.T k = transition l Ω X E K k := by
    simpa only [SX, stageSystem] using
      (stageSystem_existsUnique l Ω X).exists.choose_spec.1 E K k
  have eY : SY.T k = transition l Ω Y E K k := by
    simpa only [SY, stageSystem] using
      (stageSystem_existsUnique l Ω Y).exists.choose_spec.1 E K k
  simpa only [R, T, b, theta, p, t, rationalPullbackStageComparison,
    rationalTensorStageComparison,
    SX, SY, stageSystem] using mixed_square_transport (R E) (R K)
    (SX.T k) (transition l Ω X E K k) (SY.T k) (transition l Ω Y E K k)
    eX eY
    (T X E) (T Y E) (T X K) (T Y K)
    (b E K k) (theta X E K k) (theta Y E K k) (mu E) (mu K) (mixed E K k)

end WeilConjectures
