/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransportData
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarOperationsExistence
public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

/-! # Normalized finite evaluation of whole-system scalar extension

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 06YY, 07A6 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open SemilinearSections

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (W : Scheme.{u})

/-- Consecutive quotient maps commute with coefficient embeddings.
Source: the quotient-map square in Stacks 0941
(blueprint: lem-sf-system-scalar-finite-evaluation). -/
theorem scalarQuotient_compatible (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι W (n + 1) ≫
        coefficientSequenceCommRingTransition l L W n =
      coefficientSequenceCommRingTransition l E W n ≫
        integralScalarQuotientSheafMap l E L ι W n := by
  change integralScalarQuotientSheafMap l E L ι W (n + 1) ≫
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Padic.coefficientExtensionTransition l L (n + 1)).ulift) =
    (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift) ≫
      integralScalarQuotientSheafMap l E L ι W n
  unfold integralScalarQuotientSheafMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext x
  exact congrArg (fun q ↦ q x.down) (integralScalarQuotientMap_transition l E L ι n)

/-- The generic scalar-system map is the project's sectionwise quotient map.
Source: Zheng Construction 4.1 (blueprint: lem-sf-system-scalar-finite-evaluation). -/
theorem scalarSystemMap_eq :
    systemMap (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W) (scalarQuotient_compatible l E L ι W) =
      integralComparisonSequenceScalarMap l E L ι W := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact (systemMap_existsUnique (ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W)
    (scalarQuotient_compatible l E L ι W)).exists.choose_spec U.unop.1 (op U.unop.2)

/-- The fixed universal cochain model admits the tensor-normalized adjunctions.
The model equality and SystemScalarModel's unit and transpose fields fix every
piece of data used below. Source: Stacks 06YY and 07A6
(blueprint: lem-sf-system-scalar-finite-evaluation). -/
theorem finiteEvaluationSystemScalarModel_exists :
    ∃ A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (integralComparisonSequenceScalarMap l E L ι W),
      A.model = integralComparisonSequenceScalarModel l E L ι W := by
  exact SequenceScalarProof.scalarPackageExists
    (integralComparisonSequenceScalarMap l E L ι W)
    (integralComparisonSequenceScalarModel l E L ι W)

/-- The normalized scalar adjunction for the fixed universal cochain model.
Its ordinary unit and derived transpose are fixed by the tensor generator and counit,
respectively. Source: Stacks 06YY and 07A6
(blueprint: lem-sf-system-scalar-finite-evaluation). -/
def finiteEvaluationSystemScalarAdjunction :
    integralComparisonDerivedSequenceScalar l E L ι W ⊣
      (res (integralComparisonSequenceScalarMap l E L ι W)).mapDerivedCategory := by
  let h := finiteEvaluationSystemScalarModel_exists l E L ι W
  let A := h.choose
  have hA : A.model = integralComparisonSequenceScalarModel l E L ι W := h.choose_spec
  change (integralComparisonSequenceScalarModel l E L ι W).T ⊣ _
  rw [← hA]
  exact A.adjunction

/-- Finite evaluation of the fixed scalar model. The two adjoint-uniqueness maps
transport the normalized generic evaluation to the fixed system and finite models.
All choices are universal scalar pairs with their normalized transposes, so the
comparison is fixed by the identity-on-sections restriction square.
Source: Zheng 4.1 and 4.10; Stacks 06YY and 07A6
(blueprint: lem-sf-system-scalar-finite-evaluation). -/
def systemScalarFiniteEvaluation (n : ℕ) :
    integralComparisonDerivedSequenceScalar l E L ι W ⋙
        coefficientSequenceDerivedEvaluation l L W n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙
        pbcDerivedExtend (FiniteCompactScalar.scalarRingMap
          (integralScalarQuotientMap l E L ι n) W) := by
  let d := Classical.choice (semilinearScalarOperations.{u + 1, u, u + 1} (ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W) (scalarQuotient_compatible l E L ι W))
  let a : integralComparisonDerivedSequenceScalar l E L ι W ⊣
      resD (systemMap (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W) (scalarQuotient_compatible l E L ι W)) := by
    rw [scalarSystemMap_eq]
    exact finiteEvaluationSystemScalarAdjunction l E L ι W
  let e₀ := a.leftAdjointUniq d.scalar.adjunction
  let e₁ := (d.levels n).adjunction.leftAdjointUniq
    (pbcDerivedScalarAdjunction (FiniteCompactScalar.scalarRingMap
      (integralScalarQuotientMap l E L ι n) W))
  exact Functor.isoWhiskerRight e₀ (coefficientSequenceDerivedEvaluation l L W n) ≪≫
    d.evaluation n ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E W n) e₁

end WeilConjectures.FrobeniusExchange
