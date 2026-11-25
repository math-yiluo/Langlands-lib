/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison
public import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentation

/-! # Extensionality and generator formulas for the strict reduction tensor equation

Source: Stacks 03EK, 03EL, 07A4 and 0941.
(blueprint: lem-pod-reduction-reindex-strict-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReductionRepresentatives
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite reduction unit inserts the scalar `1`.
Source: Stacks 06YY. -/
theorem finiteAdjunction_unit_apply (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pullbackTensorFiniteAdjunction l E W n).unit.app M).val.app U x =
      unrestrictedIntegralTensorSection l E W n M U 1 x := by
  have h := (scalarReductionExtension_adjunction l E W n).choose_spec M U x
  exact h.trans rfl

/-- The finite reduction transpose evaluates a map on the unit-inserted section.
Source: Stacks 06YY. -/
theorem finiteAdjunction_homEquiv_apply (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (N : scalarReductionTarget l E W n)
    (f : (unrestrictedIntegralReductionFunctor l E W n).obj M ⟶ N)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (((pullbackTensorFiniteAdjunction l E W n).homEquiv M N f).val.app U) x =
      f.val.app U (unrestrictedIntegralTensorSection l E W n M U 1 x) := by
  rw [Adjunction.homEquiv_unit]
  exact congrArg (f.val.app U) (finiteAdjunction_unit_apply l E W n M U x)

/-- Transposing an evaluated ordinary reduction map evaluates it on the quotient unit. -/
private theorem ordinaryReduction_homEquiv_apply (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (N : coefficientSequenceModules l E W)
    (f : (pullbackTensorOrdinaryReduction l E W).obj M ⟶ N)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (((pullbackTensorFiniteAdjunction l E W n).homEquiv M
      ((coefficientSequenceEvaluation l E W n).obj N)
      ((pullbackTensorReductionEvaluation l E W n).hom.app M ≫
        (coefficientSequenceEvaluation l E W n).map f)).val.app U) x =
      f.val.app (op (n, U.unop))
        (((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app U
          (unrestrictedIntegralTensorSection l E W n M U 1 x)) := by
  exact finiteAdjunction_homEquiv_apply l E W n M
    ((coefficientSequenceEvaluation l E W n).obj N)
    ((pullbackTensorReductionEvaluation l E W n).hom.app M ≫
      (coefficientSequenceEvaluation l E W n).map f) U x

/-- Equality on a quotient unit gives equality of the corresponding transpose sections. -/
private theorem ordinaryReduction_homEquiv_apply_eq (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (N : coefficientSequenceModules l E W)
    (f g : (pullbackTensorOrdinaryReduction l E W).obj M ⟶ N)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U)
    (h : f.val.app (op (n, U.unop))
        (((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app U
          (unrestrictedIntegralTensorSection l E W n M U 1 x)) =
      g.val.app (op (n, U.unop))
        (((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app U
          (unrestrictedIntegralTensorSection l E W n M U 1 x))) :
    (((pullbackTensorFiniteAdjunction l E W n).homEquiv M
      ((coefficientSequenceEvaluation l E W n).obj N)
      ((pullbackTensorReductionEvaluation l E W n).hom.app M ≫
        (coefficientSequenceEvaluation l E W n).map f)).val.app U) x =
    (((pullbackTensorFiniteAdjunction l E W n).homEquiv M
      ((coefficientSequenceEvaluation l E W n).obj N)
      ((pullbackTensorReductionEvaluation l E W n).hom.app M ≫
        (coefficientSequenceEvaluation l E W n).map g)).val.app U) x := by
  rw [ordinaryReduction_homEquiv_apply, ordinaryReduction_homEquiv_apply]
  exact h


/-- Degreewise, the complex-level reduction evaluation is the termwise one.
Source: Stacks 0941. -/
theorem reductionEvaluationComplex_hom_f (W : Scheme.{u}) (n : ℕ)
    (C : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ) :
    ((pullbackTensorReductionEvaluationComplex l E W n).hom.app C).f k =
      (pullbackTensorReductionEvaluation l E W n).hom.app (C.X k) := by
  simp only [Functor.comp_obj, pullbackTensorReductionEvaluationComplex, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app]
  exact Category.comp_id _

/-- Degreewise, the inverse complex-level reduction evaluation is the termwise inverse.
Source: Stacks 0941. -/
theorem reductionEvaluationComplex_inv_f (W : Scheme.{u}) (n : ℕ)
    (C : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ) :
    ((pullbackTensorReductionEvaluationComplex l E W n).inv.app C).f k =
      (pullbackTensorReductionEvaluation l E W n).inv.app (C.X k) := by
  simp only [Functor.comp_obj, pullbackTensorReductionEvaluationComplex, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom, NatTrans.id_app,
    NatIso.mapHomologicalComplex_inv_app_f]
  exact Category.id_comp _

/-- Maps out of the ordinary reduction of a degree of a total tensor are determined by the
reductions of unit-inserted pure tensors at every level.
Source: Stacks 03EK, 06YY and 0941. -/
theorem reduction_total_hom_ext (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ)
    {N : coefficientSequenceModules l E W}
    {h₁ h₂ : (pullbackTensorOrdinaryReduction l E W).obj
      (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X k) ⟶ N}
    (h : ∀ (n : ℕ) (p q : ℤ) (hpq : p + q = k) (V : W.ProEt)
      (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)),
      h₁.val.app (op (n, V))
        (((pullbackTensorReductionEvaluation l E W n).hom.app _).val.app (op V)
          (unrestrictedIntegralTensorSection l E W n _ (op V) 1
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq (op V) x y))) =
      h₂.val.app (op (n, V))
        (((pullbackTensorReductionEvaluation l E W n).hom.app _).val.app (op V)
          (unrestrictedIntegralTensorSection l E W n _ (op V) 1
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq (op V) x y)))) :
    h₁ = h₂ := by
  let M : integralTowerModules l E W :=
    (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X k)
  have hn (n : ℕ) : (coefficientSequenceEvaluation l E W n).map h₁ =
      (coefficientSequenceEvaluation l E W n).map h₂ := by
    let R := (coefficientSequenceEvaluation l E W n).obj N
    let f₁ : M ⟶ (scalarReductionRestriction l E W n).obj R :=
      (pullbackTensorFiniteAdjunction l E W n).homEquiv M R
        ((pullbackTensorReductionEvaluation l E W n).hom.app M ≫
          (coefficientSequenceEvaluation l E W n).map h₁)
    let f₂ : M ⟶ (scalarReductionRestriction l E W n).obj R :=
      (pullbackTensorFiniteAdjunction l E W n).homEquiv M R
        ((pullbackTensorReductionEvaluation l E W n).hom.app M ≫
          (coefficientSequenceEvaluation l E W n).map h₂)
    rw [← cancel_epi ((pullbackTensorReductionEvaluation l E W n).hom.app M)]
    apply ((pullbackTensorFiniteAdjunction l E W n).homEquiv M R).injective
    change f₁ = f₂
    refine StrictTensorAugmentation.total_hom_ext l E W P Q k
      ((scalarReductionRestriction l E W n).obj R) (f := f₁) (g := f₂) ?_
    intro p q hpq V x y
    let z : M.val.obj V := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq V x y
    exact ordinaryReduction_homEquiv_apply_eq l E W n M N h₁ h₂ V z
      (h n p q hpq V.unop x y)
  apply SheafOfModules.hom_ext
  ext ⟨n, V⟩ r
  exact congrArg (fun f ↦ f.val.app (op V) r) (hn n)


end WeilConjectures.PodReductionRepresentatives
