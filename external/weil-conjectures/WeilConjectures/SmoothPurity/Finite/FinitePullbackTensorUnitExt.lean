/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality

/-! # Extensionality through the intrinsic finite inverse-image adjunction

Maps from pulled-back evaluated total tensors are determined by the units of pure generators.
Source: Stacks Tags 07A4 and 03D2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] sfIntrinsicPullback coefficientTotalTensor
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local instance] sfIntrinsicPullback_additive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Maps out of an intrinsic pulled-back total tensor are determined by unit pure tensors.
Source: Stacks Tag 07A4, total-complex pure generators, and Tag 03D2, adjunction
(blueprint: lem-pur-finite-pullback-tensor-unit-ext).
Proof: apply degreewise extensionality. Transpose each degree through the intrinsic
inverse-image adjunction. Its transpose is the original map preceded by the unit.
The summand inclusions and sheaf pure-tensor generators jointly determine maps
from the total tensor. Lift finite sections through the surjective evaluation
section transports, so the assumed equalities identify these transposes.
-/
theorem finitePullbackTensor_unit_ext {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (H : CochainComplex (normalizedDVRModules l E X n) ℤ)
    (a b : ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1))
      f).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
          (integralCoefficientCommRingSheaf l E Y n)).obj
          ((((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P),
           (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj Q))) ⟶ H)
    (h : ∀ (p q i : ℤ) (hpq : p + q = i) (U : Y.ProEt)
      (x : (P.X p).val.obj (op (n, U)))
      (y : (Q.X q).val.obj (op (n, U))),
      (a.f i).val.app (op ((proEtaleBaseChange f).obj U))
        (((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app _).val.app (op U)
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
            (integralCoefficientCommRingSheaf l E Y n)
            (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)
            (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj Q)
            p q i hpq (op U)
            (coefficientEvaluationSection l E Y (P.X p) n (op U) x)
            (coefficientEvaluationSection l E Y (Q.X q) n (op U) y))) =
      (b.f i).val.app (op ((proEtaleBaseChange f).obj U))
        (((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app _).val.app (op U)
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
            (integralCoefficientCommRingSheaf l E Y n)
            (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)
            (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj Q)
            p q i hpq (op U)
            (coefficientEvaluationSection l E Y (P.X p) n (op U) x)
            (coefficientEvaluationSection l E Y (Q.X q) n (op U) y)))) :
    a = b := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ((sfIntrinsicConstantModuleAdjunction f
    (finiteCoefficientRing l E (n + 1))).homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u}
    (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y n)
    (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)
    (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj Q) i _
  intro p q hpq U x y
  obtain ⟨x0, rfl⟩ := evaluationSection_surjective l E Y (P.X p) n U x
  obtain ⟨y0, rfl⟩ := evaluationSection_surjective l E Y (Q.X q) n U y
  exact h p q i hpq U.unop x0 y0

end WeilConjectures
