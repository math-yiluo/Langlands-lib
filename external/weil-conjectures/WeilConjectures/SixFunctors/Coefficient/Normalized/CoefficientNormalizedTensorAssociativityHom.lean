/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.SixFunctors.Coefficient.Finite.CoefficientFiniteTensorMonoidal
import WeilConjectures.SixFunctors.Coefficient.CoefficientStrictReductionFunctorModel
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityDescent

/-! # Forward coherence of normalized tensor comparisons

Source: Stacks 07A4 and 08J9; Zheng Construction 4.1.
(blueprint: lem-coef-normalized-tensor-associativity-hom).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

/-- The forward tensorator associativity equation.
Source: Stacks 07A4; this is the strong monoidal coherence equation whose inverse
form is used by `CoefficientTensorAssociativity`.
(blueprint: lem-coef-normalized-tensor-associativity-hom).

Proof: choose simultaneous flat-term K-flat representatives and use the prescribed
pairwise normalization squares to identify every tensorator with its ordinary
pure-tensor chain map.  The signed total-tensor associator sends each triple pure
tensor to the same reassociated tensor.  Equality on coproduct generators gives the
chain-map equality, and localization and naturality transport it to all derived
objects.  The same construction applies to every finite coefficient level. -/
def CoefficientTensorHomAssociativity
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ P Q V : A,
    F.map (SA.monoidal.associator P Q V).hom ≫
        μ.hom.app (P, SA.tensor.obj (Q, V)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj P)) (μ.hom.app (Q, V))) =
      μ.hom.app (SA.tensor.obj (P, Q), V) ≫
        SB.tensor.map (Prod.mkHom (μ.hom.app (P, Q)) (𝟙 (F.obj V))) ≫
        (SB.monoidal.associator (F.obj P) (F.obj Q) (F.obj V)).hom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local implicit_reducible] CategoryTheory.uniformProd

private theorem homAssociativity_of_core
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (m : @Functor.CoreMonoidal _ _ SA.monoidal _ _ SB.monoidal F)
    (hm : ∀ P Q,
      (@Functor.CoreMonoidal.μIso _ _ SA.monoidal _ _ SB.monoidal F m P Q).hom =
        μ.inv.app (P, Q)) :
    CoefficientTensorHomAssociativity SA SB F μ := by
  let := SA.monoidal
  let := SB.monoidal
  have hi (P Q : A) : (m.μIso P Q).inv = μ.hom.app (P, Q) := by
    have he : m.μIso P Q = (μ.app (P, Q)).symm := Iso.ext (hm P Q)
    exact congrArg Iso.inv he
  intro P Q V
  simp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj,
    MonoidalCategory.tensor_map]
  erw [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id]
  have h := m.toOplaxMonoidal.oplax_associativity P Q V
  simpa only [Functor.CoreMonoidal.toOplaxMonoidal_δ, hi,
    Functor.comp_obj, Functor.prod_obj, MonoidalCategory.tensor_obj] using h.symm

/-- Forward coherence for the fixed reduction and finite tensor comparisons.
(blueprint: lem-coef-normalized-tensor-associativity-hom). -/
theorem coefficientNormalizedTensorAssociativityHom
    (R : CoefficientDerivedSystemReduction l E W)
    (hT : CoefficientDerivedSystemTensorCoherence l E W R.toCoefficientDerivedSystemTensors)
    (hR : CoefficientReductionTensorNormalization l E W R)
    (hF : CoefficientFiniteTensorNormalization l E W R) :
    CoefficientTensorHomAssociativity R.integralClosed R.systemClosed R.reduction
        R.reductionTensor ∧
      ∀ n : ℕ, CoefficientTensorHomAssociativity R.integralClosed (R.finiteClosed n)
        (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n) := by
  refine ⟨?_, fun n ↦ ?_⟩
  · obtain ⟨⟨βI, ⟨cI⟩⟩, ⟨βS, ⟨cS⟩⟩, _⟩ := hT
    obtain ⟨M⟩ := coefficientStrictReductionFunctorModel l E W R hR
    intro X Y Z
    apply coefficientTensorAssociativityDescent
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
      R.integralClosed R.integralTensorModel βI cI
      R.systemClosed R.systemTensorModel βS cS
      M.complexFunctor R.reduction M.comparison M.computes M.preserves
      M.tensor M.associativity R.reductionTensor ?_ X Y Z
    intro P Q hP hQ hUP hUQ fP fQ
    have hh := M.normalization P Q hP hQ fP fQ
    unfold CoefficientTensorComparisonSquare at hh
    dsimp only [coefficientIntegralTensorModelIso, coefficientSystemTensorModelIso] at hh
    with_unfolding_all exact hh
  · obtain ⟨m, hm⟩ := coefficientFiniteTensorMonoidal l E W R hT hF n
    exact homAssociativity_of_core R.integralClosed (R.finiteClosed n)
      (coefficientFiniteDerivedExtension l E W n) (R.finiteTensor n) m hm

end WeilConjectures
