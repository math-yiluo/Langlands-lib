/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor

/-! # Extensionality on scalar quotient representatives

The existing quotient section construction and its proved generator criterion
are isolated to keep the scalar-extension coherence file within its compile budget.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory WeilConjectures.coefficientTotalTensor
  SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The actual local section of a strict quotient model specified by its evaluation iso.
Source: node proof step 2 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def modelSection (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (A : CoefficientExtensionSystems.{u, u} l E L ι W)
    (d : CoefficientExtensionReductionData.{u, u} l E L ι W SE SL A)
    (P : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
    (x : (P.obj.X i).val.obj U) :
    ((d.direct.obj P).X i).val.obj (op (n, U.unop)) :=
  integralComparisonSequenceSection.{u, u} l L W ((d.direct.obj P).X i) n U
    ((((d.directEvaluation n).inv.app P).f i).val.app U
      (integralScalarTensorSection.{u, u} l E L ι W n (P.obj.X i) U b x))

/-- Quotient-model tensor generators determine a whole sequence-site module map.
Source: quotient uniqueness in proof steps 1--2 of scalar-extension tower coherence;
Stacks 03EL and 07A4 (blueprint: stage3-pur-scalar-quotient-section-extensionality).
Proof: evaluate at each quotient level and precompose with the inverse of the
specified direct-evaluation isomorphism. Forget the module action. The sheafified
finite scalar tensors generate, so the section hypothesis makes the evaluated
maps equal. Extensionality on the product sequence site then proves equality
of the whole maps, including all transition data. -/
theorem quotientModelSection_hom_ext (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (A : CoefficientExtensionSystems.{u, u} l E L ι W)
    (d : CoefficientExtensionReductionData.{u, u} l E L ι W SE SL A)
    (K : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory) (i : ℤ)
    {T : coefficientSequenceModules.{u, u} l L W}
    (f g : (d.direct.obj K).X i ⟶ T)
    (h : ∀ (n : ℕ) (U : W.ProEtᵒᵖ)
      (b : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
      (x : (K.obj.X i).val.obj U),
      f.val.app (op (n, U.unop)) (modelSection l E L ι W SE SL A d K n i U b x) =
        g.val.app (op (n, U.unop)) (modelSection l E L ι W SE SL A d K n i U b x)) :
    f = g := by
  have he (n : ℕ) : (coefficientSequenceEvaluation l L W n).map f =
      (coefficientSequenceEvaluation l L W n).map g := by
    apply (cancel_epi (((d.directEvaluation n).inv.app K).f i)).mp
    apply (SheafOfModules.toSheaf _).map_injective
    apply WeilConjectures.scalarTensor_ab_hom_ext l E L ι W n (K.obj.X i)
    intro U b x
    exact h n U b x
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact congrArg (fun k ↦ k.val.app (op U.unop.2) x) (he U.unop.1)

end WeilConjectures.ScalarExtensionTower
