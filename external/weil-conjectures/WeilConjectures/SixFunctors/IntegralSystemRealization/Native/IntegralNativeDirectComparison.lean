/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
import WeilConjectures.SixFunctors.IntegralSystemRealization.NativeComparison.IntegralNativeDerivedComparison
import WeilConjectures.SmoothPurity.Compact.CompactSupportOrdinaryDirectEvaluationSections
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # Normalized comparison with the native system operation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Identity on sections identifies the two ordinary sequence direct images.
Source: Stacks 03D2, 0941
(blueprint: lem-sf-integral-native-direct-comparison). -/
def integralNativeOrdinaryDirectIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDirect l E f ≅
      ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f := by
  apply SheafOfModules.pushforwardCongr
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  unfold pullbackTensorSequenceRing pullbackTensorSequenceRingMap
  rfl

/-- Localize ordinary inverse-image uniqueness to the whole native system category.
Source: Stacks 03D2, 0941
(blueprint: lem-sf-integral-native-direct-comparison). -/
def integralNativePullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull l E f ≅ ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f :=
  letI := ProEtale.VaryingRing.pullAdditive (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  letI := ProEtale.VaryingRing.pullLimits (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  letI := ProEtale.VaryingRing.pullColimits (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) f
  Functor.mapDerivedCategoryNatIso
    (((pullbackTensorSequenceAdjunction l E f).ofNatIsoRight
      (integralNativeOrdinaryDirectIso l E f)).leftAdjointUniq
        (ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f))

/-- The derived direct-image comparison is the conjugate of the exact inverse-image one.
Source: Stacks 03D2, 0941; Zheng 4.10
(blueprint: lem-sf-integral-native-direct-comparison). -/
def integralNativeDirectIso {X Y : Scheme.{u}} (f : X ⟶ Y) (d : Direct l E f) :
    d.direct ≅ ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f :=
  conjugateIsoEquiv d.adj
    (ProEtale.VaryingRing.adj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) f) (integralNativePullIso l E f).symm

private theorem ordinary_direct_square {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E X) :
    (coefficientSequenceEvaluation l E Y n).map
        ((integralNativeOrdinaryDirectIso l E f).hom.app M) ≫
      (compactSupportOrdinaryDirectEvaluation l E f n).hom.app M =
        (pullbackTensorSequenceDirectEvaluation l E f n).hom.app M := by
  ext V x
  have h₁ := compactSupportOrdinaryDirectEvaluation_sections l E f n M V x
  have h₂ := (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose_spec
    M V.unop x
  exact eq_of_heq (h₁.trans h₂.symm)

/-- Compare total derived direct images on whole systems, with their finite evaluations.
Source: Stacks 03D2, 0941, 0D6E; Zheng 4.1 and 4.10; blueprint
fix-prop-coherence, coefficient comparisons of adjunction units and counits
(blueprint: lem-sf-integral-native-direct-comparison).

Proof: identify the two ordinary sequence-site direct images by identity on sections.
Their scalar maps agree by the specified constant-section ring-map normalizations.
Take ordinary left-adjoint uniqueness and localize this exact inverse-image comparison.
Conjugation under d.adj and the native derived adjunction gives alpha between their
right adjoints. This uses the normalized inverse-image factorization in Direct, so
alpha is also the universal right-derived comparison of the ordinary section map.
Compare evaluation of inverse image on complexes: both comparisons are localizations
of the adjoint of the identity ordinary direct-image evaluation square. The whole
cochain normalization of pullbackTensorDerivedEvaluation fixes this comparison.
Take its right-adjoint mate. Native evalP is precisely that mate, followed by the
right-derived constant-module coordinate change compactSupportDirectModel. The unit
and counit equations of ed identify ed.evaluation with the same mate under d.adj.
Naturality of adjoint conjugation therefore gives the displayed equality, on all
derived inputs. Every construction takes place on the sequence site before evaluation,
so quotient transitions are retained and no faithfulness of finite evaluations is used.
Zero inputs and n=0 satisfy the same unit/counit equations; neither properness nor a
constructibility assumption is needed for this comparison of the two presentations. -/
theorem integralNativeDirectComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : Direct l E f) (ed : DirectEvaluation l E d) :
    ∀ (M : System l E X) (n : ℕ),
      letI := proEtaleConstantModuleDirectImage_additive f
        (Padic.coefficientExtensionRing l E (n + 1))
      (coefficientSequenceDerivedEvaluation l E Y n).map
          ((integralNativeDirectIso l E f d).hom.app M) ≫
          (ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) f n ≪≫
            Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
              (compactSupportDirectModel f
                (Padic.coefficientExtensionRing l E (n + 1))))).hom.app M =
        (ed.evaluation n).hom.app M := by
  intro M n
  let R := compactSupportSystemLevel l E
  let q := compactSupportSystemQuotient l E
  let := ProEtale.StrictTower.modulePullback_additive (R n) f
  let := ProEtale.StrictTower.modulePullback_finiteLimits (R n) f
  let := ProEtale.StrictTower.modulePullback_finiteColimits (R n) f
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let := proEtaleConstantModuleDirectImage_additive f (finiteCoefficientRing l E (n + 1))
  let p := integralNativePullIso l E f
  let s := Functor.mapDerivedCategoryNatIso (NativeComparison.nativeFinitePullIso l E f n)
  let e := pullbackTensorDerivedEvaluation l E f n
  let e' := ProEtale.VaryingRing.evalG R q f n
  have he : Functor.isoWhiskerRight p (coefficientSequenceDerivedEvaluation l E X n) ≪≫ e' =
      e ≪≫ Functor.isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E Y n) s.symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    exact NativeComparison.derived_pull_square l E f n (integralNativeOrdinaryDirectIso l E f)
      (ordinary_direct_square l E f n) N
  have ht (N : System l E Y) : s.hom.app
      ((coefficientSequenceDerivedEvaluation l E Y n).obj N) ≫ e.inv.app N =
    e'.inv.app N ≫ (coefficientSequenceDerivedEvaluation l E X n).map (p.inv.app N) := by
    have hi := congrArg (fun z ↦ z.inv.app N) he
    exact hi.symm
  have hm : (mateEquiv d.adj (finiteAdj l E f n)
      (TwoSquare.mk _ _ _ _ e.inv)) = (ed.evaluation n).hom := by
    apply NatTrans.ext
    funext N
    apply ((finiteAdj l E f n).homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    rw [mateEquiv_counit, ← ed.counit n N, Iso.inv_hom_id_app_assoc]
  have h := NativeComparison.transport_mates d.adj (ProEtale.VaryingRing.adj R q f)
    (finiteAdj l E f n) (ProEtale.VaryingRing.levelAdj R f n) p s.symm
    (TwoSquare.mk _ _ _ _ e.inv) (TwoSquare.mk _ _ _ _ e'.inv) ht M
  have hs := NativeComparison.finite_derived_conjugate l E f n
  change (mateEquiv d.adj (finiteAdj l E f n)
      (TwoSquare.mk _ _ _ _ e.inv)).app M ≫
      (conjugateEquiv (finiteAdj l E f n) (ProEtale.VaryingRing.levelAdj R f n)
        s.hom).app ((coefficientSequenceDerivedEvaluation l E X n).obj M) =
    (coefficientSequenceDerivedEvaluation l E Y n).map
      ((integralNativeDirectIso l E f d).hom.app M) ≫
        (ProEtale.VaryingRing.evalP R q f n).hom.app M at h
  rw [hm, hs] at h
  have hh := congrArg (fun z ↦ z ≫
    (Functor.rightDerivedFunctorNatIso (compactSupportDirectModel f
      (finiteCoefficientRing l E (n + 1)))).hom.app
        ((coefficientSequenceDerivedEvaluation l E X n).obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

end WeilConjectures.IntegralSystemRealization
