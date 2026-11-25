/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.SixFunctors.Supporting.SemilinearTotalTensorEvaluation

/-! # Ordinary total-tensor evaluation for the actual coefficient sequence

Source: Stacks 03EK, 07A4 and 0941.
(blueprint: lem-coef-actual-total-tensor-evaluation)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.moduleAbelian

universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Evaluation of the actual coefficient sequence commutes with ordinary total tensor,
uniquely on all pure generators and with the specified underlying-section transport.
Source: Stacks 03EK, 07A4 and 0941
(blueprint: lem-coef-actual-total-tensor-evaluation).
Proof: the actual coefficient ring sequence has the same ringed sequence sheaf and
vertical evaluation as the generic semilinear construction, by their definitions.
Supply this functor equality and its actual zero-morphism preservation instance to
the generic total-tensor theorem. Its generator formula and uniqueness then give
the displayed assertion for every unbounded pair of complexes, with no flatness
or normalization assumption. -/
private theorem coefficientTotalTensorEvaluation_general (n : ℕ)
    (σ : ∀ (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ),
      M.val.obj (op (n, U.unop)) →
        ((coefficientSequenceEvaluation l E W n).obj M).val.obj U)
    (hσ : ∀ M U x, HEq (σ M U x) x)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    ∃! e : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((coefficientTotalTensor.{u, t+1, t}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P,
           ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q),
      ∀ (p q k : ℤ) (h : p + q = k) (U : W.ProEtᵒᵖ)
        (x : (P.X p).val.obj (op (n, U.unop)))
        (y : (Q.X q).val.obj (op (n, U.unop))),
      (e.hom.f k).val.app U
        (σ _ U
          (coefficientTensorGenerator.{u, t+1, t}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) P Q p q k h
            (op (n, U.unop)) x y)) =
        coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q k h U
          (σ (P.X p) U x)
          (σ (Q.X q) U y) := by
  have hF : coefficientSequenceEvaluation l E W n =
      SemilinearSections.evaluation.{t+1, t, max u (t+1)}
        (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
        (coefficientSequenceCommRingTransition l E W) n := by
    rfl
  have h0 : (coefficientSequenceEvaluation l E W n).PreservesZeroMorphisms := inferInstance
  exact semilinearTotalTensorEvaluation_existsUnique.{t+1, t, u} (hF0 := h0)
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W) n
    (coefficientSequenceEvaluation l E W n) hF
    σ hσ P Q

private theorem transport_heq {A B : AddCommGrpCat.{w}}
    (h : A = B) (x : A) : HEq ((eqToHom h) x) x := by
  cases h
  rfl

/-- The actual coefficient section transport fixes total-tensor evaluation uniquely.
Source: Stacks 03EK, 07A4 and 0941
(blueprint: lem-coef-actual-total-tensor-evaluation).
Proof: specialize the ordinary total-tensor evaluation comparison to the canonical
eqToHom transport between the recorded abelian section objects. Equality elimination
shows that this transport is heterogeneously the identity. The general comparison
then supplies the isomorphism, its generator formula, and its uniqueness. -/
theorem coefficientTotalTensorEvaluation_existsUnique (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    ∃! e : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((coefficientTotalTensor.{u, t+1, t}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P,
           ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q),
      ∀ (p q k : ℤ) (h : p + q = k) (U : W.ProEtᵒᵖ)
        (x : (P.X p).val.obj (op (n, U.unop)))
        (y : (Q.X q).val.obj (op (n, U.unop))),
      (e.hom.f k).val.app U
        ((eqToHom (coefficientSequenceEvaluationAb_eq l E W _ n U).symm)
          (coefficientTensorGenerator.{u, t+1, t}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) P Q p q k h
            (op (n, U.unop)) x y)) =
        coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q k h U
          ((eqToHom (coefficientSequenceEvaluationAb_eq l E W (P.X p) n U).symm) x)
          ((eqToHom (coefficientSequenceEvaluationAb_eq l E W (Q.X q) n U).symm) y) := by
  have hσ (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ)
      (x : M.val.obj (op (n, U.unop))) :
      HEq ((eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U).symm) x) x := by
    exact transport_heq (coefficientSequenceEvaluationAb_eq l E W M n U).symm x
  have hh := coefficientTotalTensorEvaluation_general l E W n
    (fun M U x ↦ (eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U).symm) x)
    hσ P Q
  with_reducible exact hh

end WeilConjectures
