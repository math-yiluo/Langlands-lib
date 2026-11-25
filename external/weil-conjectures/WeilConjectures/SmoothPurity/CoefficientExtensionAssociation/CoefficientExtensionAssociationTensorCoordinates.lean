/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientScalarCochainEvaluation
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation

import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationScalarUnits
import all WeilConjectures.SmoothPurity.CoefficientExtensionAssociation.CoefficientExtensionAssociationQuotientUnits

/-! # Pure tensors in balanced scalar association coordinates

Source: Stacks 03D7 and 03EK; the sequence site preceding 0941.
The inverse coordinate formula and its successor use only ordinary adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace CoefficientExtensionAssociation
section BalancedUnitMap
universe c v r
private theorem map_balanced_units
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {M : SheafOfModules.{r} R} {N : SheafOfModules.{r} S}
    (f : M ⟶ (SheafOfModules.restrictScalars φ).obj N)
    (U : Cᵒᵖ) (b : R.obj.obj U) (c : S.obj.obj U)
    (x u : M.val.obj U) (y v : N.val.obj U)
    (hc : φ.hom.app U b = c) (hx : x = b • u) (hy : y = c • v)
    (hu : HEq (f.val.app U u) v) : HEq (f.val.app U x) y := by
  rw [hx, hy]
  have hs := (f.val.app U).hom.map_smul b u
  change f.val.app U (b • u) =
    (φ.hom.app U b) • (show N.val.obj U from f.val.app U u) at hs
  rw [hc, eq_of_heq hu] at hs
  exact heq_of_eq hs
end BalancedUnitMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  integralScalarReduction completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint SemilinearSections.systemMap
  scalarReductionExtension scalarReductionExistence coefficientOrdinaryQuotient
  coefficientQuotientNatTrans coefficientOrdinaryQuotientComponent

private theorem association_inverse_tensor
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (K : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (b : (integralCoefficientSheaf l L W n).obj.obj U) (x : K.val.obj U) :
    let a (n : ℕ) := Functor.isoWhiskerLeft M.tensor (ρ n) ≪≫
      Functor.isoWhiskerRight (M.evaluation n) (A.levels n).model.E ≪≫ association n
    ((a n).inv.app K).val.app U (integralScalarTensorSection l E L ι W n K U b x) =
      b • evaluatedUnitSection l E L ι W A ρ (M.tensor.obj K) n U
        (quotientUnitSection l E W M K n U x) := by
  dsimp only
  let a (k : ℕ) := Functor.isoWhiskerLeft M.tensor (ρ k) ≪≫
    Functor.isoWhiskerRight (M.evaluation k) (A.levels k).model.E ≪≫ association k
  let y := quotientUnitSection l E W M K n U x
  let z := evaluatedUnitSection l E L ι W A ρ (M.tensor.obj K) n U y
  have hρy := evaluatedUnitSection_hom l E L ι W A ρ (M.tensor.obj K) n U y
  simp only [finiteScalarUnitSection] at hρy
  have hn := congrArg (fun f ↦ f.val.app U y)
    ((A.levels n).ordinaryAdjunction.unit.naturality ((M.evaluation n).hom.app K))
  change (((A.levels n).ordinaryAdjunction.unit.app
    ((scalarReductionExtension l E W n).obj K)).val.app U
      (((M.evaluation n).hom.app K).val.app U y)) =
    ((A.levels n).model.E.map ((M.evaluation n).hom.app K)).val.app U
      (((A.levels n).ordinaryAdjunction.unit.app
        ((coefficientSequenceEvaluation l E W n).obj (M.tensor.obj K))).val.app U y) at hn
  have hy := quotientUnitSection_evaluation l E W M K n U x
  have hu := (congrArg
    (fun z ↦ ((A.levels n).model.E.map ((M.evaluation n).hom.app K)).val.app U z)
    hρy).trans hn.symm
  rw [hy] at hu
  simp only [finiteUnitSection, normalizedUnitSection, quotientAdjunction] at hu
  have ha := hassociation n K U 1 b x
  erw [one_smul, map_one, one_mul, scalarSection_eq_unit] at ha
  have hc : ((a n).hom.app K).val.app U (b • z) =
      integralScalarTensorSection l E L ι W n K U b x := by
    change ((association n).hom.app K).val.app U
      (((A.levels n).model.E.map ((M.evaluation n).hom.app K)).val.app U
        (((ρ n).hom.app (M.tensor.obj K)).val.app U (b • z))) = _
    have hsρ := (((ρ n).hom.app (M.tensor.obj K)).val.app U).hom.map_smul b z
    have hsE := (((A.levels n).model.E.map ((M.evaluation n).hom.app K)).val.app U).hom.map_smul
      b (((ρ n).hom.app (M.tensor.obj K)).val.app U z)
    erw [hsρ, hsE, hu]
    exact ha
  have hi := congrArg (fun z ↦ ((a n).inv.app K).val.app U z) hc
  exact hi.symm.trans (iso_hom_inv_section W ((a n).app K) U (b • z))

private theorem scalar_unit_transition
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (K : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ) (x : K.val.obj U) :
    HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app
      (A.scalar.model.E.obj (M.tensor.obj K))).val.app U
        (evaluatedUnitSection l E L ι W A ρ (M.tensor.obj K) (n + 1) U
            (quotientUnitSection l E W M K (n + 1) U x)))
      (evaluatedUnitSection l E L ι W A ρ (M.tensor.obj K) n U
        (quotientUnitSection l E W M K n U x)) := by
  exact evaluatedUnitSection_transition l E L ι W A ρ hρ (M.tensor.obj K)
    (Nat.le_succ n) U (quotientUnitSection l E W M K (n + 1) U x)
    (quotientUnitSection l E W M K n U x) (quotientUnitSection_transition l E W M K n U x)

/-- The successor in balanced association coordinates reduces the coefficient of a pure tensor.

Source: Stacks 03D7 and 03EK; sequence-site construction preceding 0941.
(blueprint: stage3-pur-extension-associated-tensor-transition).

Proof: naturality of the finite scalar unit and the balanced association formula
at coefficient one identify the inverse coordinate of b tensor x with b times
the evaluated scalar unit of the quotient unit section. Quotient units commute
with successors, and scalar unit naturality preserves that compatibility.
The successor is semilinear, so it reduces b and carries this unit section to
the lower one. The inverse coordinate formula at the lower level gives exactly
the asserted reduced tensor. No nonzero, flatness, or good-complex condition is used. -/
theorem associatedTensor_transition
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (K : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s₀ : (integralCoefficientCommRingSheaf l L W (n + 1)).obj.obj U) (x : K.val.obj U) :
    let a (k : ℕ) := Functor.isoWhiskerLeft M.tensor (ρ k) ≪≫
      Functor.isoWhiskerRight (M.evaluation k) (A.levels k).model.E ≪≫ association k
    HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app
      (A.scalar.model.E.obj (M.tensor.obj K))).val.app U
      (((a (n + 1)).inv.app K).val.app U
        (integralScalarTensorSection l E L ι W (n + 1) K U s₀ x)))
      (((a n).inv.app K).val.app U (integralScalarTensorSection l E L ι W n K U
        ((integralCoefficientSheafTransition l L W n).hom.app U s₀) x)) := by
  dsimp only
  let e (k : ℕ) := (Functor.isoWhiskerLeft M.tensor (ρ k) ≪≫
    Functor.isoWhiskerRight (M.evaluation k) (A.levels k).model.E ≪≫ association k).app K
  let τ := (coefficientSequenceTransition l L W (Nat.le_succ n)).app
    (A.scalar.model.E.obj (M.tensor.obj K))
  let s : (integralCoefficientSheaf l L W (n + 1)).obj.obj U := s₀
  have hi := association_inverse_tensor l E L ι W A M ρ association hassociation
    K (n + 1) U s x
  have hj := association_inverse_tensor l E L ι W A M ρ association hassociation
    K n U ((integralCoefficientSheafTransition l L W n).hom.app U s) x
  have hs : (normalizedDVRQuotient l L W (Nat.le_succ n)).hom.app U s =
    (integralCoefficientSheafTransition l L W n).hom.app U s := by
    exact congrArg (fun f ↦ f.hom.app U s)
      (Functor.ofOpSequence_map_homOfLE_succ (integralCoefficientSheafTransition l L W) n)
  have ht := map_balanced_units (normalizedDVRQuotient l L W (Nat.le_succ n)) τ U s
    ((integralCoefficientSheafTransition l L W n).hom.app U s)
    ((e (n + 1)).inv.val.app U
      (integralScalarTensorSection l E L ι W (n + 1) K U s x))
    (evaluatedUnitSection l E L ι W A ρ (M.tensor.obj K) (n + 1) U
      (quotientUnitSection l E W M K (n + 1) U x))
    ((e n).inv.val.app U (integralScalarTensorSection l E L ι W n K U
      ((integralCoefficientSheafTransition l L W n).hom.app U s) x))
    (evaluatedUnitSection l E L ι W A ρ (M.tensor.obj K) n U
      (quotientUnitSection l E W M K n U x)) hs hi hj
    (scalar_unit_transition l E L ι W A M ρ hρ K n U x)
  exact ht

end CoefficientExtensionAssociation
end WeilConjectures
