/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Right.RightDerivedMateIndependence
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Normalized right-derived evaluation of strict integral systems

(blueprint: lem-weil-integral-system-evaluation-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures.FrobeniusExchange
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
private abbrev rs (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
private abbrev qs (n : ℕ) : rs l E (n + 1) ⟶ rs l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift
attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheafTransition ProEtale.VaryingRing.coefficientTransition
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  integralComparisonSequencePullback integralCoefficientSheaf
attribute [local irreducible] constantSheaf Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor
attribute [local instance] ProEtale.VaryingRing.pullAdditive
private theorem finitePush_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n+1)) =
      ProEtale.StrictTower.moduleDirectImage (rs l E n) f := by
  unfold proEtaleConstantModuleDirectImage ProEtale.StrictTower.moduleDirectImage
  congr 1
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have hb := ((proEtaleSheafAdjunction f CommRingCat.{u+1}).homEquiv _ _).apply_symm_apply
    (proEtaleConstantDirectImageMap f CommRingCat.{u+1} (rs l E n))
  exact (congrArg (fun t ↦ (forget₂ CommRingCat.{u+1} RingCat.{u+1}).map
    (t.hom.app U)) hb).symm
section Invariance
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  {L Q : B ⥤ A} {R : A ⥤ B} {L' Q' : D ⥤ C} {R' : C ⥤ D}
  (G : B ⥤ D) (H : A ⥤ C)
  [L.Additive] [qAdditive : Q.Additive] [R.Additive]
  [L'.Additive] [Q'.Additive] [R'.Additive] [gAdditive : G.Additive] [hAdditive : H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [qLimits : PreservesFiniteLimits Q] [qColimits : PreservesFiniteColimits Q]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
  [gLimits : PreservesFiniteLimits G] [gColimits : PreservesFiniteColimits G]
  [hLimits : PreservesFiniteLimits H] [hColimits : PreservesFiniteColimits H]
private theorem derivedMate_isIso_of_rightEqualities
    {T : A ⥤ B} [tAdditive : T.Additive] {S : C ⥤ D} [S.Additive]
    {G' : B ⥤ D} {H' : A ⥤ C} [gnAdditive : G'.Additive] [hnAdditive : H'.Additive]
    [gnLimits : PreservesFiniteLimits G'] [gnColimits : PreservesFiniteColimits G']
    [hnLimits : PreservesFiniteLimits H'] [hnColimits : PreservesFiniteColimits H']
    (a : L ⊣ R) (b : L' ⊣ R') (c : Q ⊣ T) (d : Q' ⊣ S)
    (θ : G ⋙ L' ≅ L ⋙ H) (ψ : G' ⋙ Q' ≅ Q ⋙ H')
    (hT : R = T) (hR : R' = S) (hG : G = G') (hH : H = H')
    (ha : IsIso (mateEquiv a b θ.hom))
    (hb : IsIso (mateEquiv c d ψ.hom))
    (hi : IsIso (mateEquiv c.mapDerivedCategoryRightDerivedAdjunction
      d.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso ψ).hom)) :
    IsIso (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso θ).hom) := by
  subst T
  subst S
  subst G'
  subst H'
  exact rightDerivedMate_isIso_of_ordinaryMate_isIso G H a b c d θ ψ ha hb hi
end Invariance
private theorem varyingModuleEvalMate (R : ℕ → CommRingCat.{u + 1})
    (q : ∀ n, R (n + 1) ⟶ R n) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv (ProEtale.VaryingRing.moduleAdj R q f)
      (proEtaleRingModuleAdjunction f (ProEtale.VaryingRing.coefficients R Y n)
        (ProEtale.VaryingRing.coefficients R X n)
        (ProEtale.StrictTower.constantRingIso (R n) f))
      (ProEtale.VaryingRing.moduleEvalG R q f n).inv) =
        (ProEtale.VaryingRing.moduleEvalP R q f n).hom := by
  let a := ProEtale.VaryingRing.moduleAdj R q f
  let b := proEtaleRingModuleAdjunction f (ProEtale.VaryingRing.coefficients R Y n)
    (ProEtale.VaryingRing.coefficients R X n)
    (ProEtale.StrictTower.constantRingIso (R n) f)
  have hh := ProEtale.VaryingRing.inverseMateEqOfUnit a b
    (ProEtale.VaryingRing.eval R q Y n) (ProEtale.VaryingRing.eval R q X n)
    (ProEtale.VaryingRing.moduleEvalP R q f n).hom
    (ProEtale.VaryingRing.moduleEvalG R q f n)
    (ProEtale.VaryingRing.moduleEvalG_existsUnique R q f n).choose_spec.1
  have he : (mateEquiv a b).symm
      (TwoSquare.mk _ _ _ _ (ProEtale.VaryingRing.moduleEvalP R q f n).hom) =
      TwoSquare.mk _ _ _ _ (ProEtale.VaryingRing.moduleEvalG R q f n).inv := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    exact congr_app hh M
  have he' := congrArg (mateEquiv a b) he
  rw [Equiv.apply_symm_apply] at he'
  exact (he').symm

private theorem varyingDerivedMateIso (R : ℕ → CommRingCat.{u + 1})
    (q : ∀ n, R (n + 1) ⟶ R n) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (mateEquiv
      (ProEtale.VaryingRing.moduleAdj R q f).mapDerivedCategoryRightDerivedAdjunction
      (proEtaleRingModuleAdjunction f (ProEtale.VaryingRing.coefficients R Y n)
        (ProEtale.VaryingRing.coefficients R X n)
        (ProEtale.StrictTower.constantRingIso (R n) f)).mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso
        (ProEtale.VaryingRing.moduleEvalG R q f n).symm).hom) := by
  rw [ProEtale.VaryingRing.square_symm]
  exact ProEtale.VaryingRing.evalPMate_isIso R q f n

/-- Transfer the reference mate in its native module categories, before specializing the tower.
This keeps comparisons of the coefficient presentations out of the derived construction. -/
private theorem varyingEvaluationMate_isIso (R : ℕ → CommRingCat.{u + 1})
    (q : ∀ n, R (n + 1) ⟶ R n) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    {L : ProEtale.VaryingRing.Modules R q Y ⥤ ProEtale.VaryingRing.Modules R q X}
    {T : ProEtale.VaryingRing.Modules R q X ⥤ ProEtale.VaryingRing.Modules R q Y}
    {L' : ProEtale.StrictTower.Modules (R n) Y ⥤ ProEtale.StrictTower.Modules (R n) X}
    {S : ProEtale.StrictTower.Modules (R n) X ⥤ ProEtale.StrictTower.Modules (R n) Y}
    (G : ProEtale.VaryingRing.Modules R q Y ⥤ ProEtale.StrictTower.Modules (R n) Y)
    (H : ProEtale.VaryingRing.Modules R q X ⥤ ProEtale.StrictTower.Modules (R n) X)
    [lAdditive : L.Additive] [tAdditive : T.Additive]
    [lnAdditive : L'.Additive] [sAdditive : S.Additive]
    [gAdditive : G.Additive] [hAdditive : H.Additive]
    [lLimits : PreservesFiniteLimits L] [lColimits : PreservesFiniteColimits L]
    [lnLimits : PreservesFiniteLimits L'] [lnColimits : PreservesFiniteColimits L']
    [gLimits : PreservesFiniteLimits G] [gColimits : PreservesFiniteColimits G]
    [hLimits : PreservesFiniteLimits H] [hColimits : PreservesFiniteColimits H]
    [sourceResolutions : Abelian.HasKInjectiveResolutions (ProEtale.VaryingRing.Modules R q X)]
    (a : L ⊣ T) (b : L' ⊣ S) (θ : G ⋙ L' ≅ L ⋙ H)
    (hT : T = ProEtale.VaryingRing.push R q f)
    (hS : S = ProEtale.StrictTower.moduleDirectImage (R n) f)
    (hG : G = ProEtale.VaryingRing.eval R q Y n)
    (hH : H = ProEtale.VaryingRing.eval R q X n)
    (hθ : IsIso (mateEquiv a b θ.hom)) :
    IsIso (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso θ).hom) := by
  have hq := ProEtale.VaryingRing.pull_exact R q f
  have hY := SemilinearSections.evaluation_exact (ProEt.topology Y)
    (ProEtale.VaryingRing.coefficients R Y) (ProEtale.VaryingRing.coefficientTransition R q Y) n
  have hX := SemilinearSections.evaluation_exact (ProEt.topology X)
    (ProEtale.VaryingRing.coefficients R X) (ProEtale.VaryingRing.coefficientTransition R q X) n
  have hb := ProEtale.VaryingRing.moduleEvalP_hom_isIso R q f n
  rw [← varyingModuleEvalMate R q f n] at hb
  exact derivedMate_isIso_of_rightEqualities G H
    (Q := ProEtale.VaryingRing.pull R q f)
    (G' := ProEtale.VaryingRing.eval R q Y n)
    (H' := ProEtale.VaryingRing.eval R q X n)
    (qAdditive := hq.1) (qLimits := hq.2.1) (qColimits := hq.2.2)
    (gnAdditive := hY.1) (gnLimits := hY.2.1) (gnColimits := hY.2.2)
    (hnAdditive := hX.1) (hnLimits := hX.2.1) (hnColimits := hX.2.2)
    a b (ProEtale.VaryingRing.moduleAdj R q f)
    (proEtaleRingModuleAdjunction f (ProEtale.VaryingRing.coefficients R Y n)
      (ProEtale.VaryingRing.coefficients R X n) (ProEtale.StrictTower.constantRingIso (R n) f))
    θ (ProEtale.VaryingRing.moduleEvalG R q f n).symm hT hS hG hH hθ hb
    (varyingDerivedMateIso R q f n)

/-- An ordinary invertible evaluation mate for strict integral systems has an
invertible canonical right-derived mate for the actual integral pullback models.
Source: Zheng 4.10; Stacks Tags 070I, 070K and 07A7
(blueprint: lem-weil-integral-system-evaluation-normalization).

Identify the finite direct-image functor with the varying-ring direct image by the
ring-sheaf adjunction inverse equation. The varying-ring ordinary and derived
comparison mates are invertible. The general cochain-normalization argument then
transfers derived invertibility to the given ordinary invertible mate. -/
theorem integralSystemEvaluationMate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (a : integralComparisonSequencePullback l E f ⊣
      integralComparisonSequenceDirectImage l E f)
    (b : sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f ⊣
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)))
    (θ : coefficientSequenceEvaluation l E Y n ⋙
        sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f ≅
      integralComparisonSequencePullback l E f ⋙ coefficientSequenceEvaluation l E X n)
    (hθ : IsIso (mateEquiv a b θ.hom)) :
    letI := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteLimits
      (Padic.coefficientExtensionRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteColimits
      (Padic.coefficientExtensionRing l E (n + 1)) f
    letI := coefficientSequenceEvaluation_additiveInstance l E X n
    letI := coefficientSequenceEvaluation_additiveInstance l E Y n
    letI := coefficientSequenceEvaluation_limits l E X n
    letI := coefficientSequenceEvaluation_limits l E Y n
    letI := coefficientSequenceEvaluation_colimits l E X n
    letI := coefficientSequenceEvaluation_colimits l E Y n
    IsIso (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      ((Functor.mapDerivedCategoryCompIso
        (coefficientSequenceEvaluation l E Y n)
        (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f) ≪≫
        Functor.mapDerivedCategoryNatIso θ ≪≫
        (Functor.mapDerivedCategoryCompIso
          (integralComparisonSequencePullback l E f)
          (coefficientSequenceEvaluation l E X n)).symm).hom)) := by
  let : Abelian.HasKInjectiveResolutions (normalizedDVRModules l E X n) :=
    proEtaleRingModules_hasKInjectiveResolutions X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))
  apply varyingEvaluationMate_isIso (rs l E) (qs l E) f n
    (lAdditive := integralComparisonSequencePullbackAdditive l E f)
    (tAdditive := inferInstanceAs (integralComparisonSequenceDirectImage l E f).Additive)
    (lnAdditive := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f)
    (sAdditive := proEtaleConstantModuleDirectImage_additive f
      (Padic.coefficientExtensionRing l E (n + 1)))
    (gAdditive := coefficientSequenceEvaluation_additiveInstance l E Y n)
    (hAdditive := coefficientSequenceEvaluation_additiveInstance l E X n)
    (lLimits := integralComparisonSequencePullbackLimits l E f)
    (lColimits := integralComparisonSequencePullbackColimits l E f)
    (lnLimits := sfIntrinsicPullback_preservesFiniteLimits
      (Padic.coefficientExtensionRing l E (n + 1)) f)
    (lnColimits := sfIntrinsicPullback_preservesFiniteColimits
      (Padic.coefficientExtensionRing l E (n + 1)) f)
    (gLimits := coefficientSequenceEvaluation_limits l E Y n)
    (gColimits := coefficientSequenceEvaluation_colimits l E Y n)
    (hLimits := coefficientSequenceEvaluation_limits l E X n)
    (hColimits := coefficientSequenceEvaluation_colimits l E X n)
    (sourceResolutions := inferInstanceAs
      (Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)))
    (coefficientSequenceEvaluation l E Y n) (coefficientSequenceEvaluation l E X n)
    a b θ (by rfl) (finitePush_eq l E f n) (by rfl) (by rfl) hθ
end WeilConjectures.FrobeniusExchange
