/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorFiniteSignedShifts
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorFiniteSignedShiftLaws
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Quotient compatibility of the concrete finite tensor shift maps

Only the two adjacent quotient squares remain here. The finite comparison maps
are already explicit; their existence is not part of this statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] integralOperationsFiniteHasMap

private theorem reduction_shift_component (W : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E W) ℤ) (r i : ℤ) :
    ((unrestrictedIntegralTransition l E W n).app (P⟦r⟧)).f i =
      ((unrestrictedIntegralTransition l E W n).app P).f (i + r) := by
  apply unrestrictedReduction_hom_ext l E W (n + 1) (P.X (i + r))
  intro U s x
  exact ((unrestrictedIntegralTransition_existsUnique l E W n).exists.choose_spec
    (P⟦r⟧) i U s x).trans
      ((unrestrictedIntegralTransition_existsUnique l E W n).exists.choose_spec
        P (i + r) U s x).symm

private theorem tensorTerm_hom_ext (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ)
    (Z : integralOperationsFiniteModules l E W n)
    (a b : ((integralOperationsTensorLevel l E W (n + 1)).obj (P, Q)).X k ⟶
      (SheafOfModules.restrictScalars (integralOperationsProjection l E W n)).obj Z)
    (h : ∀ (p q : ℤ) (hpq : p + q = k) (U : W.ProEtᵒᵖ)
      (x : (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P).X p).val.obj U)
      (y : (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q).X q).val.obj U),
      a.val.app U
        ((CochainComplex.ιMapBifunctor
          ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P)
          ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q)
          (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W (n + 1)))
          p q k hpq).val.app U
          (integralOperationsTensorSection l E W (n + 1) _ _ U x y)) =
      b.val.app U
        ((CochainComplex.ιMapBifunctor
          ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P)
          ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q)
          (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W (n + 1)))
          p q k hpq).val.app U
          (integralOperationsTensorSection l E W (n + 1) _ _ U x y))) :
    a = b := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
  let := integralCoefficientAbSheafify.{u, u} W
  let := integralCoefficientAbLocallyBijective.{u, u} W
  let πm := integralOperationsProjection l E W (n + 1)
  let πn := integralOperationsProjection l E W n
  let δ := integralCoefficientSheafTransition l E W n
  have hπ : πm ≫ δ = πn := integralProjection_step l E W n
  let : Presheaf.IsLocallySurjective (ProEt.topology W) πm.hom :=
    completedProjection_locallySurjective l E W (n + 1)
  apply genericRestrictedTotal_hom_ext
    (integralCoefficientCommRingSheaf l E W (n + 1))
    (integralCoefficientCommRingSheaf l E W n) πm πn δ hπ
    ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P)
    ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q) Z k
  intro p q hpq U x y
  subst k
  exact h p q rfl U x y

private theorem shift_apply_heq {W : Scheme.{u}}
    {K L : CochainComplex (integralTowerModules l E W) ℤ} (f : K ⟶ L)
    (r i j : ℤ) (h : j = i + r) (U : W.ProEtᵒᵖ)
    (x : ((K⟦r⟧).X i).val.obj U) (y : (K.X j).val.obj U) (hxy : HEq x y) :
    HEq (((f⟦r⟧').f i).val.app U x) ((f.f j).val.app U y) := by
  subst j
  have hxy' : x = y := eq_of_heq hxy
  subst y
  rfl

/-- The explicit first- and second-factor finite tensor shifts commute with each
adjacent quotient transition.

Source: Stacks 011G, 07A4; more-algebra.tex, item-shift-tensor; blueprint
theorem-poincare-duality-frobenius--2, Steps 1 and 5
(blueprint: lem-pod-tensor-finite-shift-transitions).

Proof: in each total degree test both composites on a homogeneous pure tensor
in the (p,q)-summand at level n + 1. The defining tensor-transition formula applies
the two coefficient reductions to its factors. First identify the two shifted
coefficient-reduction transitions by their
scalar-extension generator formulas and the uniqueness of those transitions.
The first-factor shift relabels
(p,q) to (p + r,q) with coefficient one, so either order gives that same reduced
pure tensor. The second-factor shift relabels it to (p,q + r) with coefficient
(-1)^(p * r). Reduction is linear and p is unchanged by the second-factor shift,
so the same coefficient occurs on both paths. The ordinary reduction shift and
restriction shift comparisons have identity components. These observations
prove equality on presheaf pure tensors. Sheafification and the coproduct
inclusions extend the equality to every module term, and degreewise
extensionality gives equality of the cochain maps. The proof works for negative
shifts, zero complexes and unbounded complexes without any convergence argument. -/
theorem podTensorFiniteShiftTransitions (W : Scheme.{u}) :
    PodTensorFiniteShiftTransitions l E W := by
  have hg := podTensorFiniteSignedShiftGenerators l E W
  constructor
  · intro n P Q r
    apply HomologicalComplex.hom_ext
    intro k
    apply tensorTerm_hom_ext l E W n (P⟦r⟧) Q k
      ((CochainComplex.mapBifunctor
        ((unrestrictedIntegralFiniteComplex l E W n).obj P)
        ((unrestrictedIntegralFiniteComplex l E W n).obj Q)
        (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n))).X (k + r))
    intro p q hpq U x y
    subst k
    change ((podTensorFiniteShiftLeft l E W n P Q r).hom.f (p + q)).val.app U
        ((((integralOperationsTensorTransition l E W n).app (P⟦r⟧, Q)).f
          (p + q)).val.app U
          (integralOperationsTotalTensorSection l E W (n + 1) (P⟦r⟧) Q p q U x y)) =
      (((((integralOperationsTensorTransition l E W n).app (P, Q))⟦r⟧').f
        (p + q)).val.app U)
        (((podTensorFiniteShiftLeft l E W (n + 1) P Q r).hom.f (p + q)).val.app U
          (integralOperationsTotalTensorSection l E W (n + 1) (P⟦r⟧) Q p q U x y))
    have hstep :=
      (integralOperationsTensorTransition_existsUnique l E W n).exists.choose_spec
        (P⟦r⟧) Q p q U x y
    have hl := hg.1 P Q n p q r U
      ((((unrestrictedIntegralTransition l E W n).app (P⟦r⟧)).f p).val.app U x)
      ((((unrestrictedIntegralTransition l E W n).app Q).f q).val.app U y)
    have hleft := (heq_of_eq (congrArg
      (fun z ↦ ((podTensorFiniteShiftLeft l E W n P Q r).hom.f (p + q)).val.app U z)
      hstep)).trans hl
    have hx := congrArg (fun f ↦ f.val.app U x)
      (reduction_shift_component l E W n P r p)
    have hc := congrArg₂ (integralOperationsTotalTensorSection l E W n P Q (p + r) q U)
      hx (Eq.refl ((((unrestrictedIntegralTransition l E W n).app Q).f q).val.app U y))
    have hr := shift_apply_heq l E
      ((integralOperationsTensorTransition l E W n).app (P, Q))
      r (p + q) ((p + r) + q) (by omega) U _ _
      (hg.1 P Q (n + 1) p q r U x y)
    have ht := (integralOperationsTensorTransition_existsUnique l E W n).exists.choose_spec
      P Q (p + r) q U x y
    exact eq_of_heq ((hleft.trans (heq_of_eq hc)).trans
      (hr.trans (heq_of_eq ht)).symm)
  · intro n P Q r
    apply HomologicalComplex.hom_ext
    intro k
    apply tensorTerm_hom_ext l E W n P (Q⟦r⟧) k
      ((CochainComplex.mapBifunctor
        ((unrestrictedIntegralFiniteComplex l E W n).obj P)
        ((unrestrictedIntegralFiniteComplex l E W n).obj Q)
        (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n))).X (k + r))
    intro p q hpq U x y
    subst k
    change ((podTensorFiniteShiftRight l E W n P Q r).hom.f (p + q)).val.app U
        ((((integralOperationsTensorTransition l E W n).app (P, Q⟦r⟧)).f
          (p + q)).val.app U
          (integralOperationsTotalTensorSection l E W (n + 1) P (Q⟦r⟧) p q U x y)) =
      (((((integralOperationsTensorTransition l E W n).app (P, Q))⟦r⟧').f
        (p + q)).val.app U)
        (((podTensorFiniteShiftRight l E W (n + 1) P Q r).hom.f (p + q)).val.app U
          (integralOperationsTotalTensorSection l E W (n + 1) P (Q⟦r⟧) p q U x y))
    have hstep :=
      (integralOperationsTensorTransition_existsUnique l E W n).exists.choose_spec
        P (Q⟦r⟧) p q U x y
    have hl := hg.2 P Q n p q r U
      ((((unrestrictedIntegralTransition l E W n).app P).f p).val.app U x)
      ((((unrestrictedIntegralTransition l E W n).app (Q⟦r⟧)).f q).val.app U y)
    have hleft := (heq_of_eq (congrArg
      (fun z ↦ ((podTensorFiniteShiftRight l E W n P Q r).hom.f (p + q)).val.app U z)
      hstep)).trans hl
    have hy := congrArg (fun f ↦ f.val.app U y)
      (reduction_shift_component l E W n Q r q)
    have hc := congrArg (fun z ↦ (p * r).negOnePow • z)
      (congrArg₂ (integralOperationsTotalTensorSection l E W n P Q p (q + r) U)
        (Eq.refl ((((unrestrictedIntegralTransition l E W n).app P).f p).val.app U x)) hy)
    have hr := shift_apply_heq l E
      ((integralOperationsTensorTransition l E W n).app (P, Q))
      r (p + q) (p + (q + r)) (by omega) U _ _
      (hg.2 P Q (n + 1) p q r U x y)
    have ht := (integralOperationsTensorTransition_existsUnique l E W n).exists.choose_spec
      P Q p (q + r) U x y
    have hs := congrArg (fun z ↦ (p * r).negOnePow • z) ht
    simp only [Units.smul_def, _root_.map_zsmul] at hr
    exact eq_of_heq ((hleft.trans (heq_of_eq hc)).trans
      (hr.trans (heq_of_eq hs)).symm)

end WeilConjectures
