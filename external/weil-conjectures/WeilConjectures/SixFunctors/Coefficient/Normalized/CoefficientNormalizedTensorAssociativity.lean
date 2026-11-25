/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedTensorAssociativityHom

/-! # Associativity of normalized tensor comparisons

Source: Stacks 07A4, 08J9 and 0941; Zheng Construction 4.1.
(blueprint: lem-coef-normalized-tensor-associativity).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures

/-- The associativity equation for the inverse tensor comparison.
Source: Stacks 07A4; the associativity axiom for a strong monoidal functor.
(blueprint: lem-coef-normalized-tensor-associativity). -/
def CoefficientTensorAssociativity
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ P Q V : A,
    SB.tensor.map (Prod.mkHom (μ.inv.app (P, Q)) (𝟙 (F.obj V))) ≫
        μ.inv.app (SA.tensor.obj (P, Q), V) ≫
        F.map (SA.monoidal.associator P Q V).hom =
      (SB.monoidal.associator (F.obj P) (F.obj Q) (F.obj V)).hom ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj P)) (μ.inv.app (Q, V))) ≫
        μ.inv.app (P, SA.tensor.obj (Q, V))

private theorem inverse_associativity_of_hom
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (P Q V : A)
    (h : F.map (SA.monoidal.associator P Q V).hom ≫
        μ.hom.app (P, SA.tensor.obj (Q, V)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj P)) (μ.hom.app (Q, V))) =
      μ.hom.app (SA.tensor.obj (P, Q), V) ≫
        SB.tensor.map (Prod.mkHom (μ.hom.app (P, Q)) (𝟙 (F.obj V))) ≫
        (SB.monoidal.associator (F.obj P) (F.obj Q) (F.obj V)).hom) :
    SB.tensor.map (Prod.mkHom (μ.inv.app (P, Q)) (𝟙 (F.obj V))) ≫
        μ.inv.app (SA.tensor.obj (P, Q), V) ≫
        F.map (SA.monoidal.associator P Q V).hom =
      (SB.monoidal.associator (F.obj P) (F.obj Q) (F.obj V)).hom ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj P)) (μ.inv.app (Q, V))) ≫
        μ.inv.app (P, SA.tensor.obj (Q, V)) := by
  let _ := SA.monoidal
  let _ := SB.monoidal
  simp only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id, id_tensorHom]
  change (μ.inv.app (P, Q) ▷ F.obj V) ≫ μ.inv.app (SA.tensor.obj (P, Q), V) ≫
      F.map (α_ P Q V).hom =
    (α_ (F.obj P) (F.obj Q) (F.obj V)).hom ≫
      (F.obj P ◁ μ.inv.app (Q, V)) ≫ μ.inv.app (P, SA.tensor.obj (Q, V))
  change F.map (α_ P Q V).hom ≫ μ.hom.app (P, SA.tensor.obj (Q, V)) ≫
      (𝟙 (F.obj P) ⊗ₘ μ.hom.app (Q, V)) =
    μ.hom.app (SA.tensor.obj (P, Q), V) ≫
      (μ.hom.app (P, Q) ⊗ₘ 𝟙 (F.obj V)) ≫
      (α_ (F.obj P) (F.obj Q) (F.obj V)).hom at h
  apply (cancel_epi (μ.hom.app (SA.tensor.obj (P, Q), V) ≫
    (μ.hom.app (P, Q) ▷ F.obj V))).1
  apply (cancel_mono (μ.hom.app (P, SA.tensor.obj (Q, V)) ≫
    (F.obj P ◁ μ.hom.app (Q, V)))).1
  have hr : (μ.hom.app (P, Q) ▷ F.obj V) ≫
      (μ.inv.app (P, Q) ▷ F.obj V) = 𝟙 _ := by
    rw [← comp_whiskerRight, Iso.hom_inv_id_app, id_whiskerRight]
  have hl : (F.obj P ◁ μ.inv.app (Q, V)) ≫
      (F.obj P ◁ μ.hom.app (Q, V)) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app,
      MonoidalCategory.whiskerLeft_id]
  simp only [Category.assoc, reassoc_of% hr, hl,
    Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  erw [Category.comp_id]
  erw [id_tensorHom, tensorHom_id] at h
  exact h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The normalized reduction and finite tensor comparisons preserve associators.
Source: Stacks 07A4 (lemma-pullback-tensor-product); the signed total-tensor
associator models, and step 3 of lem-coef-normalized-internal-hom-fibers.
(blueprint: lem-coef-normalized-tensor-associativity).

Proof: choose flat-term K-flat representatives of the three inputs. The model
squares hR and hF identify each binary comparison with ordinary scalar tensor
reassociation. The associator models in hT identify the two associators with
reassociation of three pure-tensor summands, with no additional sign. Both
composites send a triple tensor to the same reduced triple tensor. Local tensor
generators prove equality of chain maps, before localization. In the reduction
case use the strict system representatives supplied by hR, so this is an equality
of system maps, not an inference from equality of their evaluated derived maps.
Localize the equality and cancel the representative isomorphisms. Naturality
transports it to arbitrary derived objects. The identity quotient and index zero
use the same formulas; no flatness of a coefficient quotient is required. -/
theorem coefficientNormalizedTensorAssociativity
    (R : CoefficientDerivedSystemReduction l E W)
    (hT : CoefficientDerivedSystemTensorCoherence l E W R.toCoefficientDerivedSystemTensors)
    (hR : CoefficientReductionTensorNormalization l E W R)
    (hF : CoefficientFiniteTensorNormalization l E W R) :
    CoefficientTensorAssociativity R.integralClosed R.systemClosed R.reduction R.reductionTensor ∧
      ∀ n : ℕ, CoefficientTensorAssociativity R.integralClosed (R.finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n) := by
  classical
  obtain ⟨hred, hfin⟩ := coefficientNormalizedTensorAssociativityHom l E W R hT hR hF
  refine ⟨?_, ?_⟩
  · intro P Q V
    exact inverse_associativity_of_hom R.integralClosed R.systemClosed R.reduction
      R.reductionTensor P Q V (hred P Q V)
  · intro n P Q V
    exact inverse_associativity_of_hom R.integralClosed (R.finiteClosed n)
      (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n) P Q V
      (hfin n P Q V)

end WeilConjectures
