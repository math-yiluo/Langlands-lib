/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismCoefficientInclusions
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismPullbackScalarIntegralShift
import WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftRational

/-! # A step of coherent isomorphism pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open TensorProduct
namespace WeilConjectures
attribute [local irreducible] rationalDerivedPullback
  integralDerivedPullback sfRationalTriangulationDatum sfRationalScalarExtension
  rationalPullbackScalarComparison sfIntegralScalarComp sfIntegralScalarUnit
open AlgebraicallyClosedCoefficients
  (Index Coefficient coefficientInclusion coefficientInclusion_laws)

private theorem commShiftCore_neg
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (n : ℤ) (h : NatTrans.CommShiftCore τ n) :
    NatTrans.CommShiftCore τ (-n) := by
  constructor
  ext X
  apply (shiftFunctor D n).map_injective
  have hz : NatTrans.CommShiftCore τ (-n + n) := by
    simpa only [neg_add_cancel] using NatTrans.CommShiftCore.zero (τ := τ) ℤ
  have hs := hz.shift_app_comm τ X
  simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
    Category.assoc] at hs
  rw [← NatTrans.naturality_assoc] at hs
  have hD := (shiftFunctorAdd D (-n) n).inv.naturality (τ.app X)
  dsimp only [Functor.comp_map] at hD
  rw [← hD] at hs
  apply (cancel_epi (F.map ((shiftFunctorAdd C (-n) n).hom.app X) ≫
    (F.commShiftIso n).hom.app (X⟦-n⟧))).mp
  apply (cancel_mono ((shiftFunctorAdd D (-n) n).inv.app (G.obj X))).mp
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Functor.comp_obj, Category.assoc, h.shift_app_comm_assoc τ] using hs

private theorem commShift_of_one
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (h : NatTrans.CommShiftCore τ (1 : ℤ)) :
    NatTrans.CommShift τ ℤ := by
  apply NatTrans.CommShift.of_core
  have hn := commShiftCore_neg τ 1 h
  intro n
  induction n using Int.induction_on with
  | zero => exact NatTrans.CommShiftCore.zero (τ := τ) ℤ
  | @succ n ih => exact ih.add h
  | @pred n ih => simpa only [sub_eq_add_neg] using ih.add hn

private theorem map_heq {C D : Type*} [Category* C] [Category* D]
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

/-- The specified scalar comparison preserves the normalized integral and rational shifts.
Source: current blueprint sec-poincare-duality/sk-thm-frobenius,
prop-constructible-truncations.proof.md, final automorphism sentence;
steps 4, 5 and 7 of lem-pod-isomorphism-pullback-texact-coefficients.
(blueprint: lem-pod-isomorphism-pullback-scalar-shift).

Proof: identify each ordinary-to-completed scalar comparison with scalarCompletionIso
using its normalization. Its shift equation is exactly the defining normalization of
the integral scalar transition. The derived sectionwise inverse-image tensor comparison
preserves the termwise shifts. The published inverse-image scalar compatibility square
expresses the specified alpha as the conjugate of these shift-compatible maps through
eE and eL. Whisker with the fully faithful constructible inclusion and cancel to get
the integral shift square. The specified rational comparison has components Q_L(alpha).
The given degree-one normalizations of rational pullback and the corresponding fixed
normalization of rational scalar extension transfer the integral shift square through
localization. Its degree-one equation implies the equations for every integer shift:
iterate for positive shifts and use inverses for negative shifts. No new comparison or
shift is selected, and all morphisms in the raw rationalized categories are retained. -/
theorem isomorphismPullbackScalarShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (E L : Index l Ω) (h : E ≤ L)
    (sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ)
    (rE : (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ)
    (eE : (sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ⋙ inverseImageIntegralDerived
      l (Coefficient.{u} l Ω E) g ≅
      (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g) ⋙ (sfIntegralConstructible l
      (Coefficient.{u} l Ω E) X).ι)
    (heE : ∀ K, HEq (eE.hom.app K)
      (inverseImagePullbackComparisonDerived l (Coefficient.{u} l Ω E) g hX hY K.obj))
    (hsE : (fun [_s : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ] ↦
      NatTrans.CommShift eE.hom ℤ) (_s := sE))
    (hrE : ∀ K, HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω E) g).commShiftIso (self
      := rE) (1 : ℤ)).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).obj K))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).map
      (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).commShiftIso (self := sE) (1
      : ℤ)).hom.app K)))
    (sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ)
    (rL : (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ)
    (eL : (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι ⋙ inverseImageIntegralDerived
      l (Coefficient.{u} l Ω L) g ≅
      (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g) ⋙ (sfIntegralConstructible l
      (Coefficient.{u} l Ω L) X).ι)
    (heL : ∀ K, HEq (eL.hom.app K)
      (inverseImagePullbackComparisonDerived l (Coefficient.{u} l Ω L) g hX hY K.obj))
    (hsL : (fun [_s : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
      NatTrans.CommShift eL.hom ℤ) (_s := sL))
    (hrL : ∀ K, HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω L) g).commShiftIso (self
      := rL) (1 : ℤ)).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).obj K))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).map
      (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).commShiftIso (self := sL) (1
      : ℤ)).hom.app K)))
    (α : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g) ⋙
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h) ≅
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h) ⋙
      (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g))
    (hα : ∀ K, α.app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g K) :
    (fun [_sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ]
      [_sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
      NatTrans.CommShift α.hom ℤ) (_sE := sE) (_sL := sL) ∧
    (fun [_rE : (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ]
      [_rL : (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
      @NatTrans.CommShift _ _ _ _ _ _
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (isomorphismCoefficientInclusion l Ω E L h) g).hom ℤ _ _ _
        (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ _
          (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h))
        (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
          (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h) _))
      (_rE := rE) (_rL := rL) := by
  dsimp only [isomorphismCoefficientInclusion,
    GeneralAlgebraicallyClosedCoefficients.stageShift,
    GeneralAlgebraicallyClosedCoefficients.stageCategory] at hα ⊢
  let := sE
  let := sL
  let := rE
  let := rL
  let (W : Scheme.{u}) : (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω W E L h
  have ha : NatTrans.CommShift α.hom ℤ :=
    isomorphismPullbackScalarIntegralShift l Ω g hX hY E L h sE eE heE hsE
      sL eL heL hsL α (by simpa only [isomorphismCoefficientInclusion] using hα)
  refine ⟨ha, ?_⟩
  let : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h
  let : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)).CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h
  change NatTrans.CommShift
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g).hom ℤ
  exact rationalPullbackScalarComparison_commShift
    (iX := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h)
    (iY := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h)
    (tX := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h)
    (tY := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h)
    l Ω g E L h
    (GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
      l Ω Y E L h).exists.choose_spec
    (GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
      l Ω X E L h).exists.choose_spec
    (fun K ↦ hrE K.obj) (fun K ↦ hrL K.obj) α hα ha

end WeilConjectures
