/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality
import WeilConjectures.SmoothPurity.Supporting.NaturalCoherentTensorLevel
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerTransitionSquare
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.OrdinaryScalarTowerProof

/-! # Homogeneous generators of the transported strict quotient tensor tower

Source: Stacks 03EL, 07A4 and 0941; step 3 of
stage3-pur-scalar-tensor-model-normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace WeilConjectures.ScalarExtensionTower

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf completedIntegralCommRingSheafUnrestricted coefficientSequenceCommRingSheaf

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Tensoring strict quotient identifications gives the specified generator formula.
Source: Stacks 03EL, 07A4 and 0941; step 3 of
stage3-pur-scalar-tensor-model-normalization.
(blueprint: lem-pur-strict-quotient-tensor-generator).

Proof: evaluate the restricted tensor of the inverse isomorphisms a,b at level n.
Naturality of restriction/evaluation and the normalized tensor evaluation comparison
identifies its composite with the reference tower comparison with the finite total
tensor of kappaC,kappaD. This uses the two displayed evaluation equations and cancels
the reference evaluation isomorphisms. The tensor evaluation comparison carries a
homogeneous generator to the tensor of its evaluated sections. A total tensor map
applies its two component chain maps to these sections. Scalar restriction leaves
the section unchanged. These three equations give the displayed formula. The maps
are already strict tower maps; no new transition compatibility or derived
faithfulness is asserted. All total degrees and the zero and first-quotient cases
are included. -/
theorem strictQuotientTensorGenerator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules.{u, u} l E W) ℤ)
    (C D : Complex l E W)
    (a : (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P) ≅ C)
    (b : (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q) ≅ D)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj Q)
    (ha : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        κC n = ((pullbackTensorReductionEvaluationComplex l E W n).app P).symm)
    (hb : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso b ≪≫
        κD n = ((pullbackTensorReductionEvaluationComplex l E W n).app Q).symm) :
    let F := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    let q := F.mapIso ((tensor l E W).mapIso (a.symm.prod b.symm)) ≪≫
      pullbackTensorTensorTower l E W P Q
    ∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
      (x : (C.X p).val.obj (op (n, U.unop)))
      (y : (D.X r).val.obj (op (n, U.unop))),
      ((q.hom.app (op n)).f (p + r)).val.app U
        (integralComparisonRestrictedSection l E W
          (((tensor l E W).obj (C, D)).X (p + r)) n U
          (generator l E W C D p r (op (n, U.unop)) x y)) =
        integralTensorGenerator l E W P Q n p r U
          (((κC n).hom.f p).val.app U
            (coefficientEvaluationSection l E W (C.X p) n U x))
          (((κD n).hom.f r).val.app U
            (coefficientEvaluationSection l E W (D.X r) n U y)) := by
  dsimp only
  intro n p r V x y
  let ev := (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)
  have hκa : ev.map a.inv ≫ (pullbackTensorReductionEvaluationComplex l E W n).inv.app P =
      (κC n).hom := by
    have h := congrArg Iso.hom (ha n)
    change ev.map a.hom ≫ (κC n).hom =
      (pullbackTensorReductionEvaluationComplex l E W n).inv.app P at h
    rw [← h, ← Category.assoc, ← ev.map_comp, a.inv_hom_id, ev.map_id, Category.id_comp]
  have hκb : ev.map b.inv ≫ (pullbackTensorReductionEvaluationComplex l E W n).inv.app Q =
      (κD n).hom := by
    have h := congrArg Iso.hom (hb n)
    change ev.map b.hom ≫ (κD n).hom =
      (pullbackTensorReductionEvaluationComplex l E W n).inv.app Q at h
    rw [← h, ← Category.assoc, ← ev.map_comp, b.inv_hom_id, ev.map_id, Category.id_comp]
  let f := (tensor l E W).map (Prod.mkHom a.inv b.inv)
  have htw := (pullbackTensorTensorTower_existsUnique l E W P Q).exists.choose_spec n
  change (pullbackTensorTensorTower l E W P Q).app (op n) = _ at htw
  change (((pullbackTensorTensorTower l E W P Q).hom.app (op n)).f (p + r)).val.app V
    (((((coefficientSequenceRestriction l E W).map (f.f (p + r))).app (op n)).val.app V)
      (integralComparisonRestrictedSection l E W _ n V
        (generator l E W C D p r (op (n, V.unop)) x y))) = _
  rw [OrdinaryScalarTowerProof.restriction_map_section]
  have hg := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
    a.inv b.inv p r (p + r) rfl (op (n, V.unop)) x y
  change (f.f (p + r)).val.app (op (n, V.unop))
      (generator l E W C D p r (op (n, V.unop)) x y) = _ at hg
  rw [hg, ← Iso.app_hom, htw]
  have ht := tensorLevel_generator l E W P Q n p r (p + r) rfl V
    ((a.inv.f p).val.app (op (n, V.unop)) x)
    ((b.inv.f r).val.app (op (n, V.unop)) y)
  refine ht.trans ?_
  have hx := congrArg (fun g ↦ (g.f p).val.app V
    (coefficientEvaluationSection l E W (C.X p) n V x)) hκa
  have hy := congrArg (fun g ↦ (g.f r).val.app V
    (coefficientEvaluationSection l E W (D.X r) n V y)) hκb
  change (((pullbackTensorReductionEvaluationComplex l E W n).inv.app P).f p).val.app V
    (coefficientEvaluationSection l E W _ n V
      ((a.inv.f p).val.app (op (n, V.unop)) x)) = _ at hx
  change (((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q).f r).val.app V
    (coefficientEvaluationSection l E W _ n V
      ((b.inv.f r).val.app (op (n, V.unop)) y)) = _ at hy
  rw [hx, hy]
  exact finite_coefficient_generator l E W P Q n p r V _ _

end WeilConjectures.ScalarExtensionTower
