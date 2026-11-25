/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSystem
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
import WeilConjectures.Algebra.Homology.Derived.DerivedScalarExtensionCounitShift

/-! # The integral tensor maps underlying the finite native cocone

Source: Bhatt--Scholze, Proposition 3.5.1 and Proposition 6.8.14(2).
The functors and comparison maps are constructed before scalar localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option linter.all false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]
variable (C : CoefficientSystem l X)

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

instance integralTensor_sourceShiftAdditive (E : Index l (PadicAlgCl l)) :
    ∀ n : ℤ, (shiftFunctor
      (sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) n).Additive :=
  fun n ↦ by infer_instance

/-- Integral extension into the ordinary section modules of the native ring.
Source: BS 6.8.14(2) (blueprint: lem-sf-native-integral-tensor). -/
def integralTensor (E : Index l (PadicAlgCl l)) :
    sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X ⥤
      DerivedCategory (pbcModules X (ringSheaf l X)) :=
  ObjectProperty.ι (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X) ⋙
    pbcDerivedExtend ((C.coefficient E).integralMap l X)

instance integralTensor_shift (E : Index l (PadicAlgCl l)) :
    (integralTensor l X C E).CommShift ℤ := by
  unfold integralTensor
  infer_instance

/-- Derived extension is exact for its counit-normalized shift.
Source: Stacks Tag 06YY (blueprint: lem-sf-native-integral-tensor). -/
theorem derivedTensor_triangulated
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedExtend φ).IsTriangulated := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  have := pbcDerivedExtension_universal φ
  obtain ⟨σ, hσ, huniq, hadd, htri⟩ :=
    SheafOfModules.derivedScalarExtension_counitShift φ (pbcExtend φ)
      (pbcExtensionExistence φ).choose_spec.choose
      (pbcExtensionExistence φ).choose_spec.choose_spec.choose
      (pbcDerivedExtend φ) (pbcExtensionCounit φ)
  have : NatTrans.CommShift (pbcExtensionCounit φ) ℤ :=
    (PurCompactSupport.scalarCommShift_existsUnique φ).exists.choose_spec
  have he : (pbcDerivedExtend φ).commShiftIso (1 : ℤ) = σ := by
    apply huniq
    intro P
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm (pbcExtensionCounit φ) (1 : ℤ) P
  constructor
  intro T hT
  simpa only [Functor.mapTriangle_obj, he] using htri T hT

instance integralTensor_triangulated (E : Index l (PadicAlgCl l)) :
    (integralTensor l X C E).IsTriangulated := by
  letI := derivedTensor_triangulated X ((C.coefficient E).integralMap l X)
  unfold integralTensor
  infer_instance

instance integralTensor_additive (E : Index l (PadicAlgCl l)) :
    (integralTensor l X C E).Additive := by infer_instance

/-- The natural balanced derived tensor comparison, with the recorded adjunction units.
Source: Stacks Tag 06YY; BS 6.8.14(2)
(blueprint: lem-sf-native-integral-tensor). -/
def integralTensorBalancing {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    pbcDerivedExtend (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X) ⋙
      pbcDerivedExtend ((C.coefficient L).integralMap l X) ≅
    pbcDerivedExtend ((C.coefficient E).integralMap l X) :=
  Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction _)
    (pbcDerivedScalarAdjunction _) (pbcDerivedScalarAdjunction _)
    (pbcDerivedRestrictComp _ _ _ (C.coefficient_scalar E L h))

/-- The natural balancing comparison has exactly the prescribed component.
Source: Stacks Tag 06YY (blueprint: lem-sf-native-integral-tensor). -/
theorem integralTensorBalancing_app {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : DerivedCategory (scalarReductionSource l (Coefficient.{u} l (PadicAlgCl l) E) X)) :
    (integralTensorBalancing l X C h).app K =
      pbcReductionNormalization
        (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) X)
        ((C.coefficient L).integralMap l X) ((C.coefficient E).integralMap l X)
        (C.coefficient_scalar E L h) K := by
  apply Iso.ext
  dsimp [integralTensorBalancing, pbcReductionNormalization, pbcReductionNormalizationHom,
    pbcReductionTransition]
  simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc, asIso_hom]

/-- The explicit integral comparison: inverse balancing followed by completion.
Source: BS 3.5.1 and 6.8.14(2)
(blueprint: lem-sf-native-integral-tensor). -/
def integralTensorComparison {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    integralTensor l X C E ⟶
      GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X E L h ⋙
        integralTensor l X C L :=
  Functor.whiskerLeft _ (integralTensorBalancing l X C h).inv ≫
    Functor.whiskerLeft _ (Functor.whiskerRight
      (completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h))
      (pbcDerivedExtend ((C.coefficient L).integralMap l X)))

/-- Component formula for the integral comparison, avoiding functor-alias unfolding.
Source: BS 3.5.1 and 6.8.14(2) (blueprint: lem-sf-native-integral-tensor). -/
theorem integralTensorComparison_app {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (integralTensorComparison l X C h).app K =
      (integralTensorBalancing l X C h).inv.app K.obj ≫
        (pbcDerivedExtend ((C.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h)).app K.obj) := by
  rfl

instance integralTensorComparison_isIso {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    IsIso (integralTensorComparison l X C h) := by
  haveI (K : sfIntegralConstructibleCategory l
      (Coefficient.{u} l (PadicAlgCl l) E) X) :
      IsIso ((integralTensorComparison l X C h).app K) := by
    haveI hχ : IsIso
        ((completedScalarComparison l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) X).app K.obj) :=
      ((finiteFreeCompletedScalarComparison l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X).2.1 K.obj
        (CompletedLineTensor.intrinsic_complete l _ X K)).1
    unfold integralTensorComparison completedTensorComparison
    change IsIso ((integralTensorBalancing l X C h).inv.app K.obj ≫
      (pbcDerivedExtend ((C.coefficient L).integralMap l X)).map
        ((completedScalarComparison l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) X).app K.obj))
    exact Iso.isIso_hom
      (((integralTensorBalancing l X C h).app K.obj).symm ≪≫
        (pbcDerivedExtend ((C.coefficient L).integralMap l X)).mapIso
          (@asIso _ _ _ _ _ hχ))
  exact NatIso.isIso_of_isIso_app _

end WeilConjectures.LocallyFiniteAdicRealization
