/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Naturality of the generator-normalized total tensor evaluation

Source: Stacks Project, Tags 03EK, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.all false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem eqToHom_surjective {A B : AddCommGrpCat.{u}} (h : A = B) :
    Function.Surjective (eqToHom h) := by
  subst B
  exact fun x ↦ ⟨x, rfl⟩

private theorem evaluationSection_surjective (W : Scheme.{u})
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Surjective (coefficientEvaluationSection l E W M n U) :=
  eqToHom_surjective (coefficientSequenceEvaluationAb_eq l E W M n U).symm

private theorem evaluationSection_map (W : Scheme.{u})
    {M N : coefficientSequenceModules l E W} (f : M ⟶ N) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceEvaluation l E W n).map f).val.app U)
      (coefficientEvaluationSection l E W M n U x) =
    coefficientEvaluationSection l E W N n U (f.val.app (op (n, U.unop)) x) := rfl

private theorem cochainIso_inv_section
    {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {P Q : CochainComplex (SheafOfModules.{u} R) ℤ} (e : P ≅ Q) (k : ℤ) (U : Cᵒᵖ)
    (x : (P.X k).val.obj U) (y : (Q.X k).val.obj U)
    (h : (e.hom.f k).val.app U x = y) : (e.inv.f k).val.app U y = x :=
  (congrArg (fun z ↦ (e.inv.f k).val.app U z) h).symm.trans
    (congrArg (fun z : P ⟶ P ↦ (z.f k).val.app U x) e.hom_inv_id)

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

private theorem pullbackTensorEvaluationTensor_generator_cast (W : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj (op (n, U.unop)))
    (y : (Q.X q).val.obj (op (n, U.unop))) :
    ((coefficientEvaluationTensorIso.{u, u} l E W n P Q).hom.f k).val.app U
      (coefficientEvaluationSection l E W _ n U
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q p q k h (op (n, U.unop)) x y)) =
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
      p q k h U
        (coefficientEvaluationSection l E W (P.X p) n U x)
        (coefficientEvaluationSection l E W (Q.X q) n U y) :=
  (coefficientEvaluationTensorIso_exists.{u, u} l E W n P Q).choose_spec.1 p q k h U x y

attribute [local irreducible] coefficientEvaluationTensorIso
  coefficientSequenceEvaluation coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology SheafOfModules.monoidalCategory

/-- The prescribed evaluation tensor isomorphisms are natural in both complexes.
Source: Stacks Project, Cohomology on Sites, Tag 07A4, and Modules on Sites, Tag 03EK
(blueprint: lem-coef-evaluation-total-tensor-naturality).
Proof: precompose the square with the inverse comparison and test each total degree
on its pure-tensor summands. Its normalization identifies the inverse image of a
pure tensor with the corresponding tensor of sequence sections. The tensor maps
apply the two given chain maps to their two factors. Evaluation maps those same
sections, so the forward comparison normalization identifies both results. -/
theorem pullbackTensorEvaluationTensor_naturality (W : Scheme.{u}) (n : ℕ)
    {P P' Q Q' : CochainComplex (coefficientSequenceModules l E W) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom a b)) ≫
        (coefficientEvaluationTensorIso.{u, u} l E W n P' Q').hom =
      (coefficientEvaluationTensorIso.{u, u} l E W n P Q).hom ≫
        (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map
          (Prod.mkHom
            (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a)
            (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map b)) := by
  let e := coefficientEvaluationTensorIso.{u, u} l E W n P Q
  let e' := coefficientEvaluationTensorIso.{u, u} l E W n P' Q'
  apply e.inv_comp_eq.mp
  apply HomologicalComplex.hom_ext
  intro k
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u}
    (J := ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
    (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Q) k _
  intro p q hpq U
  -- Lift the sections without substituting through the tensor constructions.
  refine (evaluationSection_surjective l E W (P.X p) n U).forall.2 ?_
  intro x0
  refine (evaluationSection_surjective l E W (Q.X q) n U).forall.2 ?_
  intro y0
  have hn := pullbackTensorEvaluationTensor_generator_cast l E W n P Q p q k hpq U x0 y0
  have hi := cochainIso_inv_section e k U _ _ hn
  change (e'.hom.f k).val.app U
      (((coefficientSequenceEvaluation l E W n).map
        (((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom a b)).f k)).val.app U
        ((e.inv.f k).val.app U _)) = _
  let t := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom a b)
  have hs := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
    a b p q k hpq (op (n, U.unop)) x0 y0
  have hm := evaluationSection_map l E W (t.f k) n U
    (coefficientTensorGenerator.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) P Q p q k hpq (op (n, U.unop)) x0 y0)
  have ht := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
    (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a)
    (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map b)
    p q k hpq U
    (coefficientEvaluationSection l E W (P.X p) n U x0)
    (coefficientEvaluationSection l E W (Q.X q) n U y0)
  have ha := evaluationSection_map l E W (a.f p) n U x0
  have hb := evaluationSection_map l E W (b.f q) n U y0
  -- Compose the generator formulas without rewriting the surrounding large types.
  exact (congrArg (fun z ↦ (e'.hom.f k).val.app U
      (((coefficientSequenceEvaluation l E W n).map (t.f k)).val.app U z)) hi).trans
    ((congrArg (fun z ↦ (e'.hom.f k).val.app U z)
      (hm.trans (congrArg (coefficientEvaluationSection l E W _ n U) hs))).trans
      ((pullbackTensorEvaluationTensor_generator_cast l E W n P' Q' p q k hpq U
        ((a.f p).val.app (op (n, U.unop)) x0)
        ((b.f q).val.app (op (n, U.unop)) y0)).trans
        ((congrArg₂ (fun x y ↦ coefficientTensorGenerator.{u, u + 1, u}
          (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P')
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Q')
          p q k hpq U x y) ha hb).symm.trans ht.symm)))

end WeilConjectures
