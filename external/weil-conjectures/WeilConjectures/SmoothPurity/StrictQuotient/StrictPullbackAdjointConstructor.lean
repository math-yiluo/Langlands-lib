/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
import all WeilConjectures.SmoothPurity.StrictQuotient.StrictScalarPullbackComparison
import all WeilConjectures.SmoothPurity.StrictQuotient.StrictPullbackEvaluationConstructor
import all WeilConjectures.SmoothPurity.StrictQuotient.StrictTensorOrdinaryAdjunct

/-! # Constructor laws for ordinary strict quotient adjuncts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  WeilConjectures.coefficientFiniteQuotientExistence
  WeilConjectures.coefficientFiniteQuotientExtension
  WeilConjectures.coefficientFiniteQuotientUnitSection
  WeilConjectures.normalizedDVRQuotient
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] directEvaluation pullbackEvaluation
attribute [local irreducible] constantSheaf coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  Scheme.coefficientProEtaleDirectRingMap

private theorem evaluation_section_eq (W : Scheme.{t})
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    coefficientEvaluationSection l E W M n U x = x := rfl

private theorem transition_raw {W : Scheme.{t}} (K : Complex l E W)
    {m n : ℕ} (hmn : n ≤ m) (k : ℤ) (U : W.ProEtᵒᵖ)
    (x : (K.X k).val.obj (op (m, U.unop))) :
    coefficientRestrictionSection (normalizedDVRQuotient l E W hmn)
      ((level l E K n).X k) U (((transition l E K hmn).f k).val.app U x) =
      horizontal l E (K.X k) hmn U.unop x := by
  simpa only [evaluation_section_eq] using transition_section l E K hmn k U x

private theorem finitePull_map_generator {V W : Scheme.{t}} (g : V ⟶ W) (n : ℕ)
    {M N : normalizedDVRModules l E W n} (f : M ⟶ N) (U : W.ProEt)
    (x : M.val.obj (op U)) :
    ((integralOperationsLevelPullback l E g n).map f).val.app
        (op ((Scheme.proEtaleBaseChange g).obj U))
        (integralOperationsPullbackGenerator l E g n M U x) =
      integralOperationsPullbackGenerator l E g n N U (f.val.app (op U) x) := by
  have h := sheaf_hom_congr ((finiteAdjunction l E g n).unit.naturality f) (op U) x
  exact h.symm

private theorem pushforward_iso_inverse_apply.{r, c, v, d, w}
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    {J : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J JD]
    {R : Sheaf JD RingCat.{r}} {S : Sheaf J RingCat.{r}}
    {φ : S ⟶ (F.sheafPushforwardContinuous RingCat J JD).obj R}
    (M : SheafOfModules.{r} R) {N : SheafOfModules.{r} S}
    (e : (SheafOfModules.pushforward φ).obj M ≅ N)
    (U : Cᵒᵖ) (x : M.val.obj (F.op.obj U)) :
    e.inv.val.app U (e.hom.val.app U x) = x :=
  congrArg (fun f ↦ f.val.app U x) e.hom_inv_id

private theorem pullbackEvaluation_inv_generator {V W : Scheme.{t}} (g : V ⟶ W)
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((pullbackEvaluation l E g n).inv.app M).val.app
        (op ((Scheme.proEtaleBaseChange g).obj U))
        (integralOperationsPullbackGenerator l E g n
          ((coefficientSequenceEvaluation l E W n).obj M) U x) =
      integralComparisonSequenceGenerator l E g M n U x := by
  have h := congrArg (((pullbackEvaluation l E g n).inv.app M).val.app
      (op ((Scheme.proEtaleBaseChange g).obj U)))
    (pullbackEvaluation_generator l E g M n U x)
  have hi := pushforward_iso_inverse_apply.{max u (t + 1), t + 1, t, t + 1, t}
    (F := Prod.sectR n V.ProEt)
    (φ := eqToHom (coefficientSequenceEvaluationRing_eq l E V n).symm)
    ((integralComparisonSequencePullback l E g).obj M)
    ((pullbackEvaluation l E g n).app M)
    (op ((Scheme.proEtaleBaseChange g).obj U))
    (integralComparisonSequenceGenerator l E g M n U x)
  exact h.symm.trans hi

private theorem pullbackEvaluation_hom_ext {V W : Scheme.{t}} (g : V ⟶ W)
    (M : coefficientSequenceModules l E W) (n : ℕ)
    {N : normalizedDVRModules l E V n}
    {a b : (coefficientSequenceEvaluation l E V n).obj
      ((integralComparisonSequencePullback l E g).obj M) ⟶ N}
    (h : ∀ (U : W.ProEt) (x : M.val.obj (op (n, U))),
      a.val.app (op ((Scheme.proEtaleBaseChange g).obj U))
          (integralComparisonSequenceGenerator l E g M n U x) =
        b.val.app (op ((Scheme.proEtaleBaseChange g).obj U))
          (integralComparisonSequenceGenerator l E g M n U x)) : a = b := by
  apply (cancel_epi ((pullbackEvaluation l E g n).inv.app M)).1
  apply ((finiteAdjunction l E g n).homEquiv _ _).injective
  ext U x
  change a.val.app ((Scheme.proEtaleBaseChange g).op.obj U)
      (((pullbackEvaluation l E g n).inv.app M).val.app
        ((Scheme.proEtaleBaseChange g).op.obj U)
        (integralOperationsPullbackGenerator l E g n
          ((coefficientSequenceEvaluation l E W n).obj M) U.unop x)) =
    b.val.app ((Scheme.proEtaleBaseChange g).op.obj U)
      (((pullbackEvaluation l E g n).inv.app M).val.app
        ((Scheme.proEtaleBaseChange g).op.obj U)
        (integralOperationsPullbackGenerator l E g n
          ((coefficientSequenceEvaluation l E W n).obj M) U.unop x))
  erw [pullbackEvaluation_inv_generator]
  exact h U.unop x

private theorem scalarPullback_hom_ext {V W : Scheme.{t}} (g : V ⟶ W)
    (M : coefficientSequenceModules l E W)
    (SV : CoefficientDerivedSystemTensors l E V)
    (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m)
    {N : normalizedDVRModules l E V n}
    {a b : (coefficientFiniteQuotientExtension l E V hmn).obj
      ((coefficientSequenceEvaluation l E V m).obj
        ((integralComparisonSequencePullback l E g).obj M)) ⟶ N}
    (h : ∀ (U : W.ProEt) (x : M.val.obj (op (m, U))),
      a.val.app (op ((Scheme.proEtaleBaseChange g).obj U))
          (coefficientFiniteQuotientUnitSection l E V hmn
            ((coefficientSequenceEvaluation l E V m).obj
              ((integralComparisonSequencePullback l E g).obj M))
            (op ((Scheme.proEtaleBaseChange g).obj U))
            (integralComparisonSequenceGenerator l E g M m U x)) =
        b.val.app (op ((Scheme.proEtaleBaseChange g).obj U))
          (coefficientFiniteQuotientUnitSection l E V hmn
            ((coefficientSequenceEvaluation l E V m).obj
              ((integralComparisonSequencePullback l E g).obj M))
            (op ((Scheme.proEtaleBaseChange g).obj U))
            (integralComparisonSequenceGenerator l E g M m U x))) : a = b := by
  apply ((DV.ordinaryAdjunction hmn).homEquiv _ _).injective
  apply pullbackEvaluation_hom_ext l E g M m
  intro U x
  apply scalar_restriction_section_injective (normalizedDVRQuotient l E V hmn) N
    (op ((Scheme.proEtaleBaseChange g).obj U))
  erw [normalized_homEquiv_apply (normalizedDVRQuotient l E V hmn)
      (coefficientFiniteQuotientExtension l E V hmn) (DV.ordinaryAdjunction hmn)
      (coefficientFiniteQuotientUnitSection l E V hmn) (DV.ordinary_unit hmn),
    normalized_homEquiv_apply (normalizedDVRQuotient l E V hmn)
      (coefficientFiniteQuotientExtension l E V hmn) (DV.ordinaryAdjunction hmn)
      (coefficientFiniteQuotientUnitSection l E V hmn) (DV.ordinary_unit hmn)]
  exact h U x

private theorem pullbackAdjointEquation {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W) (SW : CoefficientDerivedSystemTensors l E W)
    (DW : CoefficientFiniteQuotientCalculus l E W SW)
    (SV : CoefficientDerivedSystemTensors l E V)
    (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m) :
    PullbackAdjointEquation l E g K SW DW SV DV hmn := by
  obtain ⟨χ, hχ⟩ := strictScalarPullbackComparison l E g K SW DW SV DV hmn
  refine ⟨pullbackComplexEvaluation l E g K m, pullbackComplexEvaluation l E g K n,
    χ, ?_, ?_, ?_, ?_⟩
  · intro k U x
    exact pullbackEvaluation_generator l E g (K.X k) m U x
  · intro k U x
    exact pullbackEvaluation_generator l E g (K.X k) n U x
  · exact hχ
  · apply HomologicalComplex.Hom.ext
    funext k
    apply scalarPullback_hom_ext l E g (K.X k) SV DV hmn
    intro U x
    have hχx := hχ k U (coefficientEvaluationSection l E W (K.X k) m (op U) x)
    simp only [evaluation_section_eq] at hχx
    have hf := finitePull_map_generator l E g n
      ((ordinaryAlpha l E K SW DW hmn).f k) U
      (coefficientFiniteQuotientUnitSection l E W hmn ((level l E K m).X k) (op U)
        (coefficientEvaluationSection l E W (K.X k) m (op U) x))
    simp only [evaluation_section_eq] at hf
    have hw := ordinary_on_unit l E K SW DW hmn k (op U)
      (coefficientEvaluationSection l E W (K.X k) m (op U) x)
    simp only [evaluation_section_eq] at hw
    have hv := ordinary_on_unit l E (pull l E g K) SV DV hmn k
      (op ((Scheme.proEtaleBaseChange g).obj U))
      (coefficientEvaluationSection l E V ((pull l E g K).X k) m
        (op ((Scheme.proEtaleBaseChange g).obj U))
        (integralComparisonSequenceGenerator l E g (K.X k) m U x))
    simp only [evaluation_section_eq] at hv
    have hW := hw.trans (transition_raw l E K hmn k (op U) x)
    have hV := hv.trans (transition_raw l E (pull l E g K) hmn k
      (op ((Scheme.proEtaleBaseChange g).obj U))
      (integralComparisonSequenceGenerator l E g (K.X k) m U x))
    have hV' := hV.trans (pullbackTransitions l E g K hmn k U x)
    have hs := scalar_map_unit l E V SV DV hmn
      ((pullbackEvaluation l E g m).hom.app (K.X k))
      (op ((Scheme.proEtaleBaseChange g).obj U))
      (coefficientEvaluationSection l E V ((pull l E g K).X k) m
        (op ((Scheme.proEtaleBaseChange g).obj U))
        (integralComparisonSequenceGenerator l E g (K.X k) m U x))
    simp only [evaluation_section_eq] at hs
    have hem := pullbackEvaluation_generator l E g (K.X k) m U x
    have h1 := hs.trans (congrArg
      (coefficientFiniteQuotientUnitSection l E V hmn
        ((integralOperationsLevelPullback l E g m).obj
          ((coefficientSequenceEvaluation l E W m).obj (K.X k)))
        (op ((Scheme.proEtaleBaseChange g).obj U))) hem)
    have h3 := (congrArg
      ((χ.hom.f k).val.app (op ((Scheme.proEtaleBaseChange g).obj U))) h1).trans hχx
    have h4 := congrArg
      (((integralOperationsLevelPullback l E g n).map
        ((ordinaryAlpha l E K SW DW hmn).f k)).val.app
        (op ((Scheme.proEtaleBaseChange g).obj U))) h3
    change ((integralOperationsLevelPullback l E g n).map
        ((ordinaryAlpha l E K SW DW hmn).f k)).val.app
        (op ((Scheme.proEtaleBaseChange g).obj U))
        ((χ.hom.f k).val.app (op ((Scheme.proEtaleBaseChange g).obj U))
          (((coefficientFiniteQuotientExtension l E V hmn).map
            ((pullbackEvaluation l E g m).hom.app (K.X k))).val.app
            (op ((Scheme.proEtaleBaseChange g).obj U))
            (coefficientFiniteQuotientUnitSection l E V hmn
              ((coefficientSequenceEvaluation l E V m).obj
                ((integralComparisonSequencePullback l E g).obj (K.X k)))
              (op ((Scheme.proEtaleBaseChange g).obj U))
              (integralComparisonSequenceGenerator l E g (K.X k) m U x)))) =
      ((pullbackEvaluation l E g n).hom.app (K.X k)).val.app
        (op ((Scheme.proEtaleBaseChange g).obj U))
        (((ordinaryAlpha l E (pull l E g K) SV DV hmn).f k).val.app
          (op ((Scheme.proEtaleBaseChange g).obj U))
          (coefficientFiniteQuotientUnitSection l E V hmn
            ((coefficientSequenceEvaluation l E V m).obj
              ((integralComparisonSequencePullback l E g).obj (K.X k)))
            (op ((Scheme.proEtaleBaseChange g).obj U))
            (integralComparisonSequenceGenerator l E g (K.X k) m U x)))
    have hl := congrArg
      (integralOperationsPullbackGenerator l E g n ((level l E K n).X k) U) hW
    have hen := pullbackEvaluation_generator l E g (K.X k) n U
      (horizontal l E (K.X k) hmn U x)
    have hr := congrArg (((pullbackEvaluation l E g n).hom.app (K.X k)).val.app
      (op ((Scheme.proEtaleBaseChange g).obj U))) hV'
    exact (h4.trans hf).trans (hl.trans (hen.symm.trans hr.symm))

/-- Exact geometric inverse image on the strict sequence site evaluates to the
specified finite pullback and respects its actual quotient adjuncts.
Source: Stacks Project, sites-cohomology.tex, Tags 0G7E and 07A6;
sites-modules.tex, Tag 03EL; pullback step of
lem-pur-quotient-operation-adjoint-factorizations.
(blueprint: lem-pur-strict-pullback-adjoint-constructor).

Proof: the unit defining integralComparisonSequenceGenerator is a morphism of
sequence module sheaves, so its naturality for the horizontal site arrow gives
PullbackTransitions. Evaluation of the sequence inverse image and finite inverse
image are left adjoint to the same evaluated direct image. The resulting comparison
is fixed by their units; it sends the sequence unit generator to the finite unit
generator, giving PullbackModel. The constant-ring inverse-image comparison is an
isomorphism, so finite pullback is exact. Exact localization therefore computes
every universal left derived pair on every complex, giving PullbackComputes.
For two levels, base change of scalars commutes with this inverse image. The
ordinary scalar comparison sends the insertion of one followed by the mth
inverse-image unit to the nth unit applied to the insertion of one. The two
composites in PullbackAdjointEquation agree on these generators, by the ordinary
adjunction unit identities and horizontal naturality. Linearity, Kan extension,
sheafification and the adjunction Hom bijection imply equality of chain maps.
The inverse comparisons are the reversed balanced tensor and inverse-image
comparisons. This constructs em, en and chi with all three required generator
identifications and the displayed equation. No normalization of K, flatness of the
quotient map or commutation of inverse image with the completed coefficient limit
is needed. Equal levels, identity arrows, zero complexes and empty schemes are
included. -/
theorem strictPullbackAdjointConstructor {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W) :
    PullbackTransitions l E g K ∧
    (∀ n : ℕ, PullbackModel l E g K n ∧ PullbackComputes l E g K n) ∧
    (∀ (SW : CoefficientDerivedSystemTensors l E W)
      (DW : CoefficientFiniteQuotientCalculus l E W SW)
      (SV : CoefficientDerivedSystemTensors l E V)
      (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m),
      PullbackAdjointEquation l E g K SW DW SV DV hmn) := by
  refine ⟨(strictPullbackEvaluationConstructor l E g K).1,
    (strictPullbackEvaluationConstructor l E g K).2, ?_⟩
  intro SW DW SV DV m n hmn
  exact pullbackAdjointEquation l E g K SW DW SV DV hmn

end WeilConjectures.StrictQuotient
