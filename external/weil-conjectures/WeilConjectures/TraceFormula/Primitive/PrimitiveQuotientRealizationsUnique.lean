/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-! # Uniqueness of representative-normalized primitive realizations

Source: Stacks 06YS, 06YY and 0941; step 6 of
lem-trf-effective-quotient-model-descent.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel
  coefficientSequenceRestriction coefficientSequenceLimit
  integralDerivedPullback integralScalarExtensionOfUniverses

private theorem pullbackLevel_hom_ext {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (M : integralOperationsFiniteModules l E Y n)
    (N : integralOperationsFiniteModules l E X n)
    (a b : (SheafOfModules.restrictScalars
        (integralOperationsProjection l E X n)).obj
          ((integralOperationsLevelPullback l E f n).obj M) ⟶
      (SheafOfModules.restrictScalars (integralOperationsProjection l E X n)).obj N)
    (h : ∀ (U : Y.ProEt) (x : M.val.obj (Opposite.op U)),
      a.val.app (Opposite.op ((Scheme.proEtaleBaseChange f).obj U))
          (integralOperationsPullbackGenerator l E f n M U x) =
        b.val.app (Opposite.op ((Scheme.proEtaleBaseChange f).obj U))
          (integralOperationsPullbackGenerator l E f n M U x)) : a = b := by
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
      (integralOperationsProjection l E X n).hom :=
    completedProjection_locallySurjective l E X n
  apply SheafOfModules.IntegralPullbackProof.restricted_hom_ext
    (integralOperationsBaseChange f) (𝟙 _)
    (integralOperationsDirectRingMap l E f n)
    (integralOperationsPullbackAdjunction l E f n)
    (integralOperationsProjection l E X n) (integralOperationsProjection l E X n)
    (Category.comp_id _) M N a b
  intro U x
  exact h U.unop x

private theorem goodLocalization_essSurj (Y : Scheme.{t}) :
    (integralOperationsGoodLocalization l E Y).EssSurj := by
  let := integralOperationsGoodLocalization_isLocalization l E Y
  exact Localization.essSurj _
    ((HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E Y).ι)

private theorem cancel_normalized
    {D : Type*} [Category D] {A B T : D}
    (a b : A ⟶ B) (c : A ⟶ T) [IsIso a] [IsIso c] (k : B ⟶ T)
    (ha : a ≫ k = c) (hb : b ≫ k = c) : a = b := by
  have := IsIso.of_isIso_fac_left ha
  exact (cancel_mono k).1 (ha.trans hb.symm)

private theorem abEqToHom_cancel {A B : AddCommGrpCat.{u}} (h : A = B) (x : A) :
    (eqToHom h.symm) ((eqToHom h) x) = x := by
  subst B
  rfl

-- The two strict tower comparisons elaborate large coefficient-functor types.
/-- The prescribed quotient-generator normalization determines both primitive
natural realization isomorphisms uniquely.
Source: Stacks, sites-cohomology.tex, Tags 06YS, 06YY and 0941; parent node
step 6, with the representative normalizations of the primitive model interfaces.
(blueprint: lem-trf-primitive-quotient-realizations-unique).

Proof: fix a flat-term K-flat representative P and choose its simultaneous strict quotient
presentation from SY.reductionModel. Apply the normalization fields of the two pullback models
to this same presentation. Their strict tower isomorphisms q coincide: in each degree and at
each coefficient level their homomorphisms agree on the finite pullback unit generators, by the
two displayed generator formulas; the inverse-image module adjunction and restriction along an
epimorphic quotient detect equality on those generators. Thus the normalized Roos factors
coincide. Cancel these isomorphisms in the two normalization equations to identify the
realization components at Q(P). For the scalar models, use the same quotient presentation.
Balanced scalar tensors generate the sheafified finite scalar extension, so their two generator
formulas similarly identify q degreewise and levelwise. The common postcomparison, including
the universal cochain counit and Roos factor, is invertible: composing it with either
realization gives the specified comparison isomorphism by normalization. Cancel that
postcomparison to identify the scalar realizations at Q(P). Every ambient derived object has a
flat-term K-flat good representative; naturality along its comparison isomorphism gives
equality at that object, and natural-transformation extensionality gives equality of the two
natural isomorphisms. The argument includes zero inputs and equal fields; it compares entire
strict systems and never uses finite evaluations to detect equality of arbitrary derived
morphisms. -/
theorem primitiveQuotientRealizations_unique
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρX : IntegralComparisonRoosModel l E X)
    (ρL : IntegralComparisonRoosModel l L Y)
    (α : IntegralComparisonPullbackModel l E f SY ρX)
    (β : IntegralComparisonScalarModel l E L ι Y SY ρL) :
    (∀ α' : IntegralComparisonPullbackModel l E f SY ρX,
      α'.realization = α.realization) ∧
    (∀ β' : IntegralComparisonScalarModel l E L ι Y SY ρL,
      β'.realization = β.realization) := by
  classical
  have := goodLocalization_essSurj l E Y
  constructor
  · intro α'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    let P := (integralOperationsGoodLocalization l E Y).objPreimage K
    let d := (integralOperationsGoodLocalization l E Y).objObjPreimageIso K
    have hP : α'.realization.hom.app (DerivedCategory.Q.obj P.obj) =
        α.realization.hom.app (DerivedCategory.Q.obj P.obj) := by
      -- Whole-tower coherence is required in addition to finite presentation equations.
      obtain ⟨C, e, κ, hC, hcoh⟩ := coherentPrimitiveReductionPresentation l E SY P
      obtain ⟨q, hq, hα⟩ := α.normalization P C e κ hC hcoh
      obtain ⟨q', hq', hα'⟩ := α'.normalization P C e κ hC hcoh
      have hfix : q'.inv ≫ q.hom = 𝟙 _ := by
        apply NatTrans.ext
        funext n
        apply HomologicalComplex.hom_ext
        intro i
        apply pullbackLevel_hom_ext l E f n.unop
          (((unrestrictedIntegralFiniteComplex l E Y n.unop).obj P.obj).X i)
          ((integralOperationsLevelPullback l E f n.unop).obj
            (((unrestrictedIntegralFiniteComplex l E Y n.unop).obj P.obj).X i))
        intro U x
        let z := integralComparisonSequenceSection l E Y (C.X i) n.unop (Opposite.op U)
          (((κ n.unop).inv.f i).val.app (Opposite.op U) x)
        have hz : ((κ n.unop).hom.f i).val.app (Opposite.op U)
            (coefficientEvaluationSection l E Y (C.X i) n.unop (Opposite.op U) z) = x := by
          have hcancel : coefficientEvaluationSection l E Y (C.X i) n.unop
              (Opposite.op U) z = (((κ n.unop).inv.f i).val.app (Opposite.op U) x) :=
            abEqToHom_cancel
              (coefficientSequenceEvaluationAb_eq l E Y (C.X i) n.unop (Opposite.op U)) _
          rw [hcancel]
          exact congrArg (fun k ↦ (k.f i).val.app (Opposite.op U) x)
            (κ n.unop).inv_hom_id
        have hg := congrArg (integralOperationsPullbackGenerator l E f n.unop
          (((unrestrictedIntegralFiniteComplex l E Y n.unop).obj P.obj).X i) U) hz
        have h₁ := (hq' n.unop i U z).trans hg
        have h₂ := (hq n.unop i U z).trans hg
        let w := integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E f).obj (C.X i)) n.unop
          (Opposite.op ((Scheme.proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f (C.X i) n.unop U z)
        have hi : ((q'.inv.app n).f i).val.app _
            (((q'.hom.app n).f i).val.app _ w) = w :=
          congrArg (fun k ↦ ((k.app n).f i).val.app _ w) q'.hom_inv_id
        change ((q.hom.app n).f i).val.app _
          (((q'.inv.app n).f i).val.app _
            (integralOperationsPullbackGenerator l E f n.unop _ U x)) =
          integralOperationsPullbackGenerator l E f n.unop _ U x
        exact (congrArg (fun y ↦ ((q.hom.app n).f i).val.app _
          (((q'.inv.app n).f i).val.app _ y)) h₁.symm).trans
            ((congrArg (fun y ↦ ((q.hom.app n).f i).val.app _ y) hi).trans h₂)
      have heq : q.hom = q'.hom := by
        have h := congrArg (q'.hom ≫ ·) hfix
        simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
          Category.comp_id] using h
      rw [← heq] at hα'
      exact (cancel_normalized _ _ _ _ hα hα').symm
    apply (cancel_epi ((integralDerivedPullback l E f).map d.hom)).1
    rw [α'.realization.hom.naturality, α.realization.hom.naturality]
    exact congrArg (fun z ↦ z ≫ _) hP
  · intro β'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    let P := (integralOperationsGoodLocalization l E Y).objPreimage K
    let d := (integralOperationsGoodLocalization l E Y).objObjPreimageIso K
    have hP : β'.realization.hom.app (DerivedCategory.Q.obj P.obj) =
        β.realization.hom.app (DerivedCategory.Q.obj P.obj) := by
      obtain ⟨C, e, κ, hC, hcoh⟩ := coherentPrimitiveReductionPresentation l E SY P
      obtain ⟨q, hq, hβ⟩ := β.normalization P C e κ hC hcoh
      obtain ⟨q', hq', hβ'⟩ := β'.normalization P C e κ hC hcoh
      have hfix : q'.inv ≫ q.hom = 𝟙 _ := by
        apply NatTrans.ext
        funext n
        apply HomologicalComplex.hom_ext
        intro i
        apply integralScalarReduction_hom_ext l E L ι Y n.unop (P.obj.X i)
        intro U s x
        let w := integralComparisonRestrictedSection l L Y
          ((integralComparisonSequenceScalarModel l E L ι Y).E.obj (C.X i)) n.unop U
          (integralComparisonSequenceTensorSection l E L ι Y (C.X i)
            (Opposite.op (n.unop, U.unop)) s
            (integralComparisonSequenceSection l E Y (C.X i) n.unop U
              (((κ n.unop).inv.f i).val.app U
                (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X i) U 1 x))))
        have h₁ := hq' n.unop i U s x
        have h₂ := hq n.unop i U s x
        have hi : ((q'.inv.app n).f i).val.app U
            (((q'.hom.app n).f i).val.app U w) = w :=
          congrArg (fun k ↦ ((k.app n).f i).val.app U w) q'.hom_inv_id
        change ((q.hom.app n).f i).val.app U
          (((q'.inv.app n).f i).val.app U
            (integralScalarTensorSection l E L ι Y n.unop (P.obj.X i) U s x)) =
          integralScalarTensorSection l E L ι Y n.unop (P.obj.X i) U s x
        exact (congrArg (fun y ↦ ((q.hom.app n).f i).val.app _
          (((q'.inv.app n).f i).val.app _ y)) h₁.symm).trans
            ((congrArg (fun y ↦ ((q.hom.app n).f i).val.app _ y) hi).trans h₂)
      have heq : q.hom = q'.hom := by
        have h := congrArg (q'.hom ≫ ·) hfix
        simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
          Category.comp_id] using h
      rw [← heq] at hβ'
      exact (cancel_normalized _ _ _ _ hβ hβ').symm
    apply (cancel_epi ((integralScalarExtensionOfUniverses l E L ι Y).map d.hom)).1
    rw [β'.realization.hom.naturality, β.realization.hom.naturality]
    exact congrArg (fun z ↦ z ≫ _) hP

end WeilConjectures
