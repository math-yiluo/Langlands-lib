/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SmoothPurity.CoefficientClosedStructure.CoefficientClosedTensorComparison
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization

/-! # Compatibility of normalized representative tensor models

Source: Stacks 0A90, 0A95 and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] coefficientSequenceInternalHom

private theorem coefficientTensorModelComparison_of_normalize
    {V : Type*} [Category V] {H : Vᵒᵖ × V ⥤ V}
    (S T : CoefficientClosedStructure H) (A P Q : V)
    (f : S.tensor.obj (A, P) ⟶ Q) (g : T.tensor.obj (A, P) ⟶ Q)
    (h : A ⟶ H.obj (Opposite.op P, Q)) (e : Q ⟶ Q) (he : e = 𝟙 Q)
    (hs : (S.transpose A P Q).symm h = f ≫ e)
    (ht : (T.transpose A P Q).symm h = g ≫ e) :
    (CoefficientClosedStructure.comparison T S).hom.app (A, P) ≫ f = g := by
  subst e
  rw [Category.comp_id] at hs ht
  apply (T.transpose A P Q).injective
  rw [CoefficientClosedStructure.comparison_transpose, ← hs, ← ht]
  exact ((S.transpose A P Q).apply_symm_apply h).trans
    ((T.transpose A P Q).apply_symm_apply h).symm

-- The identity total tensor has to be compared across the two site universe parameters.
/-- The representative tensor models commute with the canonical closed-tensor comparison.
Source: Stacks 0A90, 0A95 and 08J9
(blueprint: lem-coef-representative-tensor-model-comparison).

Proof: curry the identity of the ordinary total tensor. The representative
normalization in both closed structures identifies its uncurrying with the inverse
representative tensor isomorphism. The canonical comparison preserves transpose;
apply the two tensor-Hom bijections and their inverse laws to identify these maps.
The argument applies also to zero complexes and the empty scheme. -/
theorem coefficientTensorModelComparison (W : Scheme.{u})
    (S T : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (C D : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) C)
    (hD : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) D) :
    (CoefficientClosedStructure.comparison T.systemClosed S.systemClosed).hom.app
        (DerivedCategory.Q.obj C, DerivedCategory.Q.obj D) ≫
      (CoefficientTensorModels.iso.{u, u + 1, u, u + 2}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l E W)
        S.systemClosed S.systemTensorModel C D hC hD).inv =
        (CoefficientTensorModels.iso.{u, u + 1, u, u + 2}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l E W)
        T.systemClosed T.systemTensorModel C D hC hD).inv := by
  let J := coefficientSequenceTopology (Scheme.ProEt.topology W)
  let R := coefficientSequenceCommRingSheaf.{u, u} l E W
  let I := (coefficientTotalTensor.{u, u + 1, u} J R).obj (C, D)
  obtain ⟨g, hg, _⟩ := coefficientCochainTensorCurry_exists J R C D I (𝟙 I)
  have hs := coefficientTensorCurry_normalize.{u, u + 1, u, u + 2} J R
    S.systemClosed S.systemTensorModel C D I hC hD (𝟙 I) g hg
  have ht := coefficientTensorCurry_normalize.{u, u + 1, u, u + 2} J R
    T.systemClosed T.systemTensorModel C D I hC hD (𝟙 I) g hg
  have hid := (DerivedCategory.Q (C := coefficientSequenceModules.{u, u} l E W)).map_id I
  exact coefficientTensorModelComparison_of_normalize
    S.systemClosed T.systemClosed _ _ _ _ _ _ _ hid hs ht

end WeilConjectures
