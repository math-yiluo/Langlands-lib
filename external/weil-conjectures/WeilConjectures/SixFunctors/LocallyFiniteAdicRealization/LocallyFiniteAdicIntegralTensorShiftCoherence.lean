/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensor
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportRestrictionShift
import WeilConjectures.SixFunctors.Exceptional.ExceptionalOrdinaryCompletedScalarShift

/-! # Shift coherence of the explicit integral comparison

Source: Bhatt--Scholze, Propositions 3.5.1 and 6.8.14(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]

/-- Conjugation under shift-compatible adjunctions preserves shift compatibility. -/
private theorem conjugateEquiv_symm_commShift
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.CommShift ℤ] [L₂.CommShift ℤ] [R₁.CommShift ℤ] [R₂.CommShift ℤ]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) [a₁.CommShift ℤ] [a₂.CommShift ℤ]
    (τ : R₁ ⟶ R₂) [NatTrans.CommShift τ ℤ] :
    NatTrans.CommShift ((conjugateEquiv a₁ a₂).symm τ) ℤ := by
  change NatTrans.CommShift
    (L₂.leftUnitor.inv ≫
      ((Functor.leftUnitor (𝟭 C ⋙ L₂)).inv ≫
        Functor.whiskerRight a₁.unit (𝟭 C ⋙ L₂) ≫
        (Functor.associator (L₁ ⋙ R₁) (𝟭 C) L₂).inv ≫
        Functor.whiskerRight (Functor.associator L₁ R₁ (𝟭 C)).hom L₂ ≫
        Functor.whiskerRight
          (Functor.whiskerLeft L₁ (R₁.rightUnitor.hom ≫ τ ≫ R₂.leftUnitor.inv)) L₂ ≫
        Functor.whiskerRight (Functor.associator L₁ (𝟭 D) R₂).inv L₂ ≫
        (Functor.associator (L₁ ⋙ 𝟭 D) R₂ L₂).hom ≫
        Functor.whiskerLeft (L₁ ⋙ 𝟭 D) a₂.counit ≫
        (L₁ ⋙ 𝟭 D).rightUnitor.hom) ≫ L₁.rightUnitor.hom) ℤ
  infer_instance

/-- The derived scalar adjunction is compatible with the counit-normalized scalar shift. -/
private theorem pbcDerivedScalarAdjunction_commShift {T : Scheme.{u}}
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    letI : (pbcDerivedRestrict φ).CommShift ℤ :=
      inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.CommShift ℤ)
    (pbcDerivedScalarAdjunction φ).CommShift ℤ := by
  let : NatTrans.CommShift (pbcExtensionCounit φ) ℤ :=
    (PurCompactSupport.scalarCommShift_existsUnique φ).exists.choose_spec
  exact PurCompactSupport.restrictionScalarAdjunction_shift φ

omit [IsCommMonObj (abRing l X)] [(sections l X).Additive] [PreservesFiniteLimits (sections l X)]
  [PreservesFiniteColimits (sections l X)] in
/-- The derived balancing isomorphism commutes with the scalar shifts. -/
private theorem integralTensorBalancing_commShift (C : CoefficientSystem l X)
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    NatTrans.CommShift (integralTensorBalancing l X C h).hom ℤ := by
  have : IsCommMonObj (abRing l X) := C.commutative
  let φ := completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
    (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X
  let ψ := (C.coefficient L).integralMap l X
  let χ := (C.coefficient E).integralMap l X
  let : (pbcDerivedRestrict φ).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.CommShift ℤ)
  let : (pbcDerivedRestrict ψ).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict ψ).mapDerivedCategory.CommShift ℤ)
  let : (pbcDerivedRestrict χ).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict χ).mapDerivedCategory.CommShift ℤ)
  let := pbcDerivedScalarAdjunction_commShift φ
  let := pbcDerivedScalarAdjunction_commShift ψ
  let := pbcDerivedScalarAdjunction_commShift χ
  let : NatTrans.CommShift (pbcDerivedRestrictComp φ ψ χ (C.coefficient_scalar E L h)).hom ℤ := by
    dsimp only [pbcDerivedRestrictComp, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  exact conjugateEquiv_symm_commShift (pbcDerivedScalarAdjunction χ)
    ((pbcDerivedScalarAdjunction φ).comp (pbcDerivedScalarAdjunction ψ))
    (pbcDerivedRestrictComp φ ψ χ (C.coefficient_scalar E L h)).inv

section OrdinaryCompletion
attribute [local instance 5000] integralTowerHasDerivedCategory

/-- The ordinary-to-completed comparison, read as a square with the integral transition. -/
private abbrev ordinaryTransitionComparison {E L : Index l (PadicAlgCl l)}
    (h : E ≤ L) (W : Scheme.{u}) :
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) W).ι ⋙
        integralOrdinaryDerivedScalar l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) W E L h ⋙
        (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) L) W).ι :=
  sfIntegralOrdinaryComparison l (Coefficient.{u} l (PadicAlgCl l) E)
    (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W

/-- The ordinary-to-completed comparison commutes with the normalized transition shift. -/
private theorem ordinaryTransitionComparison_commShift {E L : Index l (PadicAlgCl l)}
    (h : E ≤ L) (W : Scheme.{u}) :
    NatTrans.CommShift (ordinaryTransitionComparison l h W).hom ℤ := by
  constructor
  intro n
  ext K
  have hn := (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
    l (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) L)
    (coefficientInclusion l (PadicAlgCl l) E L h) W).exists.choose_spec n K
  have hn' := eq_of_heq hn
  change _ = (ordinaryTransitionComparison l h W).inv.app (K⟦n⟧) ≫
      (((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) W).ι ⋙
        integralOrdinaryDerivedScalar l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
            W).commShiftIso n).hom.app K ≫
      (shiftFunctor (DerivedCategory (integralTowerModules l
        (Coefficient.{u} l (PadicAlgCl l) L) W)) n).map
        ((ordinaryTransitionComparison l h W).hom.app K) at hn'
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc, ObjectProperty.ι_map]
  change _ = (ordinaryTransitionComparison l h W).hom.app (K⟦n⟧) ≫ _
  refine Eq.trans ?_ (congrArg (fun f ↦ (ordinaryTransitionComparison l h W).hom.app (K⟦n⟧) ≫ f)
    hn').symm
  rw [Iso.hom_inv_id_app_assoc]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]

/-- Intrinsic completion is the inverse ordinary model comparison followed by the
ordinary-to-completed comparison. -/
private theorem intrinsicScalarCompletion_eq {E L : Index l (PadicAlgCl l)}
    (h : E ≤ L) (W : Scheme.{u})
    (e : integralOrdinaryDerivedScalar l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W ≅
      pbcDerivedExtend (completedCoefficientMap.{u, u} l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W))
    (he : e.hom ≫ completedScalarComparison.{u, u} l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W =
      scalarCompletion l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W) :
    intrinsicScalarCompletion l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W =
      Functor.whiskerLeft _ e.inv ≫ (ordinaryTransitionComparison l h W).hom := by
  ext K
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, ordinaryTransitionComparison,
    ← intrinsicScalarCompletion_paste l _ _ _ W e he K]
  exact (Iso.inv_hom_id_app_assoc e K.obj _).symm

/-- Completion restricted to intrinsic objects commutes with the normalized shifts. -/
private theorem intrinsicScalarCompletion_commShift {E L : Index l (PadicAlgCl l)}
    (h : E ≤ L) (W : Scheme.{u}) :
    NatTrans.CommShift (intrinsicScalarCompletion l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W)
        ℤ := by
  obtain ⟨e, he, hs⟩ := ordinary_completed_scalar_shift l (Coefficient.{u} l (PadicAlgCl l) E)
    (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) W
  have := ordinaryTransitionComparison_commShift l h W
  rw [intrinsicScalarCompletion_eq l h W e he]
  infer_instance

end OrdinaryCompletion

/-- The integral comparison is inverse balancing followed by the whiskered intrinsic
completion square. -/
private theorem integralTensorComparison_eq (C : CoefficientSystem l X)
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    integralTensorComparison l X C h =
      (Functor.whiskerLeft (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
          (integralTensorBalancing l X C h).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (intrinsicScalarCompletion l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X)
          (pbcDerivedExtend ((C.coefficient L).integralMap l X)) ≫
        (Functor.associator _ _ _).hom :
        integralTensor l X C E ⟶
          GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X E L h ⋙
            integralTensor l X C L) := by
  ext K
  rw [integralTensorComparison_app]
  simp [intrinsicScalarCompletion, completedTensorComparison]

/-- The explicit inverse-balancing/completion comparison commutes with every integer shift.

Source: Bhatt--Scholze, Propositions 3.5.1 and 6.8.14(2); the shift clause of
`lem-sf-native-integral-tensor-coherence`
(blueprint: new-lem-sf-native-integral-tensor-shift-coherence).

Proof: the ordinary tensor comparison commutes with the degreewise shift of complexes,
and so does its quotient-completion chain map, since both are defined degreewise.
The derived scalar-extension counit is compatible with shifts
(`lem-sbc-derived-scalar-extension-counit-shift`), and a shift structure on a scalar
counit is unique (`lem-pur-scalar-counit-shift-unique`); hence the universal derived
counits lift the two degreewise squares uniquely. The integral transition's shift
structure is defined by the same ordinary tensor normalization, so the composite
inverse-balancing/completion map commutes with the shift by one; compatibility with
the shift by one and the shift coherence isomorphisms give every integer shift. -/
theorem integralTensorComparison_shift (C : CoefficientSystem l X) :
    ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
      NatTrans.CommShift (integralTensorComparison l X C h) ℤ := by
  intro E L h
  have := integralTensorBalancing_commShift l X C h
  have := intrinsicScalarCompletion_commShift l h X
  rw [integralTensorComparison_eq l X C h]
  infer_instance

end WeilConjectures.LocallyFiniteAdicRealization
