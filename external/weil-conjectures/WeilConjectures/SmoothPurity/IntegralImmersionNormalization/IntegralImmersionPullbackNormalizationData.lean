/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.IntegralPullbackCompletedComparison
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
public import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackComparison

/-! # Normalized integral immersion pullback

Comparison data (blueprint: def-sf-integral-immersion-pullback-normalization-data).

Source: main-20261015 smooth-purity localization, integral and rational paragraphs;
Stacks proetale.tex, Tags 09AA and 099N(2),(5), and sites-cohomology.tex, Tag 0941
(blueprint: lem-sf-integral-immersion-pullback-normalization).

All three functors below have the recorded completed-coefficient derived categories
as source and target. Only the strict construction is transported through the existing
finite-projection-normalized coefficient isomorphism. Ordinary pullback is exact
termwise module inverse image in these same coefficient presentations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.IntegralImmersionNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Inverse coefficient transport along the existing normalized completed-ring iso.
Source: Stacks 099N, coefficient identification
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev back (T : Scheme.{u}) :=
  pbcDerivedRestrict (ImmersionCompletedPullback.completedRingIso l E T).hom

/-- The scalar restriction round trip is identity on every module section.
Source: Stacks 03DA; coefficient identification in the localization proof
(blueprint: lem-sf-integral-immersion-pullback-normalization).
Proof: both coefficient restrictions leave underlying sections and maps unchanged.
Their composite action is the original action by the inverse identities of the ring
iso. The sectionwise identity and its inverse define the natural iso; the equation
on all sections determines every component, hence proves uniqueness. -/
theorem moduleRoundTrip_exists (T : Scheme.{u}) :
    ∃! e : pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).hom ⋙
        pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).inv ≅
          𝟭 (scalarReductionSource.{u, u} l E T),
      ∀ (M : scalarReductionSource.{u, u} l E T) (V : T.ProEtᵒᵖ) (x : M.val.obj V),
        ((e.hom.app M).val.app V) x = x := by
  let e := ImmersionCompletedPullback.completedRingIso l E T
  have hV (V : T.ProEtᵒᵖ) :
      RingHom.id _ = (e.hom.hom.app V).hom.comp (e.inv.hom.app V).hom := by
    exact congrArg (fun f ↦ (f.hom.app V).hom) e.inv_hom_id.symm
  let eM (M : scalarReductionSource.{u, u} l E T) :
      (pbcRestrict e.inv).obj ((pbcRestrict e.hom).obj M) ≅ M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        (ModuleCat.restrictScalarsComp'App (e.inv.hom.app V).hom
          (e.hom.hom.app V).hom (RingHom.id _) (hV V) (M.val.obj V)).symm ≪≫
            ModuleCat.restrictScalarsId'App _ rfl (M.val.obj V))
        (fun {V W} f ↦ by ext x; rfl))
  let η : pbcRestrict e.hom ⋙ pbcRestrict e.inv ≅ 𝟭 _ :=
    NatIso.ofComponents eM (fun f ↦ by ext V x; rfl)
  refine ⟨η, ?_, ?_⟩
  · intro M V x
    rfl
  · intro η' hη'
    apply Iso.ext
    ext M V x
    exact hη' M V x

/-- The unique identity-on-sections coefficient restriction round trip.
Source: Stacks 03DA
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def moduleRoundTrip (T : Scheme.{u}) := (moduleRoundTrip_exists l E T).exists.choose

/-- Descent of that identity-on-sections comparison, using exact restriction.
Source: Stacks 015F, 03DA
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def roundTrip (T : Scheme.{u}) :
    back l E T ⋙ ImmersionCompletedPullback.transport l E T ≅
      𝟭 (DerivedCategory (scalarReductionSource.{u, u} l E T)) :=
  (Functor.mapDerivedCategoryCompIso
    (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).hom)
    (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E T).inv)) ≪≫
      Functor.mapDerivedCategoryNatIso (moduleRoundTrip l E T) ≪≫
        Functor.mapDerivedCategoryIdIso _

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The canonical completed coefficient isomorphism, in the recorded integral presentation.
Source: Stacks 098T; the finite-projection-normalized coefficient transport
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def coefficientIso :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E X) ≅
      completedIntegralCommRingSheafUnrestricted l E Y :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).mapIso
      (ImmersionCompletedPullback.completedRingIso l E X).symm ≪≫
    (pbcIntegralDatum l E).integralRingIso g ≪≫
      ImmersionCompletedPullback.completedRingIso l E Y

/-- The finite coefficient comparison with the same prescribed quotient identifications.
Source: Stacks 098T
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def finiteCoefficientIso (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (integralCoefficientCommRingSheaf l E X n) ≅
      integralCoefficientCommRingSheaf l E Y n :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).mapIso
      (ImmersionCompletedPullback.finiteRingIso l E X n).symm ≪≫
    (pbcIntegralDatum l E).finiteRingIso g n ≪≫
      ImmersionCompletedPullback.finiteRingIso l E Y n

/-- The coefficient identifications keep constants, projections and the entire quotient
system, in its existing function-sheaf presentation. Source: Stacks 098T and 097N
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def CoefficientNormalization : Prop :=
  (∀ (V : X.ProEt) (r : Padic.coefficientExtensionIntegers l E),
    (((((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _)
      (coefficientIso l E g).hom).hom.app (op V)).hom
        (integralScalarConstant l E X (op V) r)) =
      integralScalarConstant l E Y (op ((proEtaleBaseChange g).obj V)) r) ∧
  (∀ n : ℕ, (coefficientIso l E g).hom ≫
      completedIntegralCommRingProjectionUnrestricted l E Y n =
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (completedIntegralCommRingProjectionUnrestricted l E X n) ≫
        (finiteCoefficientIso l E g n).hom) ∧
  ∀ (b a : ℕᵒᵖ) (h : b ⟶ a),
    ((pbcIntegralDatum l E).finiteRingIso g b.unop).hom ≫
        (reductionCoefficientSystem Y (pbcIntegralDatum l E)).map h =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        ((reductionCoefficientSystem X (pbcIntegralDatum l E)).map h) ≫
          ((pbcIntegralDatum l E).finiteRingIso g a.unop).hom

/-- Ordinary module inverse image with the specified coefficient identification.
The two restrictions only identify the existing completed-ring presentations.
Source: Stacks 03D2; localization integral paragraph
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev ordinaryModule :=
  pbcRestrict (ImmersionCompletedPullback.completedRingIso l E X).hom ⋙
    ImmersionCompletedPullback.modulePull l E g ⋙
      pbcRestrict (ImmersionCompletedPullback.completedRingIso l E Y).inv

/-- Ordinary pullback with its canonical termwise derived shift comparison.
Source: Stacks 015F, 03D2
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev ordinary := (ordinaryModule l E g).mapDerivedCategory

/-- The original strict quotient-tower completed pullback, in the recorded integral
coefficient category. Source: Stacks 099N(5)
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
abbrev completed := back l E X ⋙
  pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ⋙
    ImmersionCompletedPullback.transport l E Y

/-- The counit-normalized comparison with ordinary termwise inverse image.
Source: Stacks 015F and the recorded immersion comparison
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def ordinaryPresentation :
    back l E X ⋙ pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
        ImmersionCompletedPullback.transport l E Y ≅ ordinary l E g :=
  isoWhiskerLeft (back l E X)
    (isoWhiskerRight (ImmersionCompletedPullback.derivedIso l E g)
      (ImmersionCompletedPullback.transport l E Y)) ≪≫
    isoWhiskerLeft (back l E X)
      (Functor.mapDerivedCategoryCompIso (ImmersionCompletedPullback.modulePull l E g)
        (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E Y).inv)) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (pbcRestrict (ImmersionCompletedPullback.completedRingIso l E X).hom)
      (ImmersionCompletedPullback.modulePull l E g ⋙
        pbcRestrict (ImmersionCompletedPullback.completedRingIso l E Y).inv))

/-- The actual completion comparison, built from the published strict quotient unit.
Source: Stacks 099N(2),(5)
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def completionComparison : ordinary l E g ⟶ completed l E g :=
  (ordinaryPresentation l E g).inv ≫
    whiskerLeft (back l E X)
      (whiskerRight (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g)
        (ImmersionCompletedPullback.transport l E Y))

/-- The actual finite projection of strict pullback, transported to integral coefficients.
Source: Stacks 0941 and 099N(5)
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def finiteProjection (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :=
  (ImmersionCompletedPullback.transport l E Y).map
    (ImmersionCompletedPullback.actualCompletedProjection l E g ((back l E X).obj K) n)

/-- A fixed interval for every positive reduction, including empty intervals.
Source: localization integral paragraph
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
def HasReductionInterval (T : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T)) (a b : ℤ) : Prop :=
  ∀ n : ℕ, proEtaleCohomologicalSupport
    ((scalarReductionDerivedExtension.{u, u} l E T n).obj K) ⊆ Set.Icc a b

/-- The normalized comparisons and their exact, scalar-linear constructible restrictions.
The integral comparison contains its representative projection and canonical signed-shift
normalization. The displayed gamma is required to be exactly its transport to the original
strict construction. Thus no arbitrary isomorphism or arbitrary shift is substituted.
Source: localization integral/rational paragraphs; Stacks 09AA, 099N, 0941 and 015F
(blueprint: lem-sf-integral-immersion-pullback-normalization). -/
structure Comparison where
  coefficients : CoefficientNormalization l E g
  integralComparison : IntegralCompletedComparison.Comparison l E g
  complete_back : ∀ K : sfIntegralConstructibleCategory l E X,
    IntegralCompletedComparison.Complete l E ((back l E X).obj K.obj)
  gamma : (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g ≅
    (sfIntegralConstructible l E X).ι ⋙ completed l E g
  gamma_normalization : ∀ K : sfIntegralConstructibleCategory l E X,
    gamma.hom.app K =
      (integralDerivedPullback l E g).map ((roundTrip l E X).inv.app K.obj) ≫
      (integralComparison.gamma ((back l E X).obj K.obj) (complete_back K)).hom ≫
      (ImmersionCompletedPullback.transport l E Y).map
        ((IntegralCompletedComparison.towerIso l E g).inv.app
          ⟨(back l E X).obj K.obj,
            integralComparison.intrinsic ((back l E X).obj K.obj) (complete_back K)⟩)
  c : (sfIntegralConstructible l E X).ι ⋙ ordinary l E g ≅
    (sfIntegralConstructible l E X).ι ⋙ completed l E g
  c_hom : c.hom = whiskerLeft (sfIntegralConstructible l E X).ι
    (completionComparison l E g)
  completion_projections : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    c.hom.app K ≫ finiteProjection l E g K.obj n =
      (ordinaryPresentation l E g).inv.app K.obj ≫
        (ImmersionCompletedPullback.transport l E Y).map
          ((ImmersionCompletedPullback.reductionUnit l E Y n).app
            ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj
              ((back l E X).obj K.obj)))
  completion_transitions : ∀ (K : sfIntegralConstructibleCategory l E X)
      (b a : ℕ) (h : a ≤ b),
    finiteProjection l E g K.obj b ≫
      (ImmersionCompletedPullback.transport l E Y).map
        (ImmersionCompletedPullback.reductionTransition l E Y b a h
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj
            ((back l E X).obj K.obj))) = finiteProjection l E g K.obj a
  completedShift : (completed l E g).CommShift ℤ
  gamma_shifts :
    (fun [_si : (integralDerivedPullback l E g).CommShift ℤ]
      [_sc : (completed l E g).CommShift ℤ] ↦ NatTrans.CommShift gamma.hom ℤ)
      (_si := integralComparison.derivedShift) (_sc := completedShift)
  completion_shifts :
    (fun [_sc : (completed l E g).CommShift ℤ] ↦
      NatTrans.CommShift c.hom ℤ) (_sc := completedShift)
  composite_shifts :
    (fun [_si : (integralDerivedPullback l E g).CommShift ℤ] ↦
      NatTrans.CommShift (gamma ≪≫ c.symm).hom ℤ)
        (_si := integralComparison.derivedShift)
  ordinary_exact : ((sfIntegralConstructible l E X).ι ⋙ ordinary l E g).IsTriangulated
  integral_exact :
    (fun [_si : (integralDerivedPullback l E g).CommShift ℤ] ↦
      ((sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g).IsTriangulated)
      (_si := integralComparison.derivedShift)
  completed_exact :
    (fun [_sc : (completed l E g).CommShift ℤ] ↦
      ((sfIntegralConstructible l E X).ι ⋙ completed l E g).IsTriangulated)
      (_sc := completedShift)
  ordinary_linear : Functor.Linear (Padic.coefficientExtensionIntegers l E)
    ((sfIntegralConstructible l E X).ι ⋙ ordinary l E g)
  integral_linear : Functor.Linear (Padic.coefficientExtensionIntegers l E)
    ((sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E g)
  completed_linear : Functor.Linear (Padic.coefficientExtensionIntegers l E)
    ((sfIntegralConstructible l E X).ι ⋙ completed l E g)
  constructible : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y ((ordinary l E g).obj K.obj) ∧
    sfIntegralConstructible l E Y ((completed l E g).obj K.obj) ∧
    sfIntegralConstructible l E Y ((integralDerivedPullback l E g).obj K.obj)
  interval : ∀ (K : sfIntegralConstructibleCategory l E X) (a b : ℤ),
    HasReductionInterval l E X K.obj a b →
      HasReductionInterval l E Y ((integralDerivedPullback l E g).obj K.obj) a b

end WeilConjectures.IntegralImmersionNormalization
