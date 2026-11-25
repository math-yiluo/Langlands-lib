/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction
import all WeilConjectures.SixFunctors.OpenTensorQuotient.OpenQuotientScalarComparisonCanonicalTransition
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Ordinary scalar reduction at one quotient level

Source: Stacks 03EK and 0940.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] WeilConjectures.PurStrictScalar.ordinaryReduction
  WeilConjectures.PurStrictScalar.ordinaryReductionAdj
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

attribute [local irreducible] scalarReductionExistence scalarReductionExtension

private theorem reductionUnit_epi (W : Scheme.{u}) (M : scalarReductionSource l E W)
    (n : ℕ) : Epi ((ordinaryReductionAdj l E W).unit.app M ≫
      limit.π ((coefficientSequenceRestriction l E W).obj
        ((ordinaryReduction l E W).obj M)) (op n)) := by
  obtain ⟨O⟩ := CompletionUnit.ordinaryModel_exists l E W
  let U := coefficientSequenceRestriction l E W
  let e := (ordinaryReductionAdj l E W).leftAdjointUniq O.adjunction
  let k := (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).app
      (O.tensor.obj M) ≪≫
    (scalarReductionRestriction l E W n).mapIso ((O.evaluation n).app M)
  let v := O.adjunction.unit.app M ≫ limit.π (U.obj (O.tensor.obj M)) (op n)
  have hv : v ≫ k.hom = (purSequenceFiniteAdjunction l E W n).unit.app M := by
    ext V x
    exact (O.unit_tensor M n V x).trans (CompletionUnit.finite_unit_tensor l E W M n V x).symm
  have : Epi (v ≫ k.hom) := hv.symm ▸
    OpenTensorQuotient.scalarUnit_epi l E W n M
  have : Epi v := (epi_comp_iff_of_isIso v k.hom).mp inferInstance
  let c := (U.mapIso (e.app M)).app (op n)
  let a := (ordinaryReductionAdj l E W).unit.app M ≫
    limit.π (U.obj ((ordinaryReduction l E W).obj M)) (op n)
  have hc : a ≫ c.hom = v := by
    change ((ordinaryReductionAdj l E W).unit.app M ≫
      limit.π (U.obj ((ordinaryReduction l E W).obj M)) (op n)) ≫
      (U.map (e.hom.app M)).app (op n) = v
    erw [Category.assoc, ← limMap_π, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ limit.π (U.obj (O.tensor.obj M)) (op n))
      ((ordinaryReductionAdj l E W).unit_leftAdjointUniq_hom_app O.adjunction M)
  have : Epi (a ≫ c.hom) := hc.symm ▸ inferInstanceAs (Epi v)
  exact (epi_comp_iff_of_isIso a c.hom).mp inferInstance

/-- The reduction-unit tensor sections jointly detect maps from one source level.
Source: Stacks 03EK (tensor adjunction and sheafification), 0940 (quotient systems).
Proof: the nth evaluation of the quotient-system left adjoint is the ordinary
quotient of M by the nth positive uniformizer power, with quotient map induced
by the adjunction unit. This quotient map is an epimorphism of underlying module
sheaves: locally every quotient section lifts to M. After constant scalar
extension, every section locally is a sum of tensors b tensor (1 tensor x).
If two module maps agree on these sections for every site object, linearity gives
agreement on the sums and separatedness gives agreement on the original section.
Sectionwise extensionality then identifies the maps. This applies to any target
module and needs neither ramification nor any balancing comparison.
(blueprint: lem-pur-ordinary-scalar-reduction-generators). -/
theorem ordinaryScalarReduction_hom_ext (W : Scheme.{u})
    (M : scalarReductionSource l E W) (n : ℕ)
    (N : Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W)
    (f g : (pbcExtend (constantMap l E F i W)).obj
      (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n)) ⟶ N)
    (h : ∀ (U : W.ProEtᵒᵖ) (b : ((constants l F).ring W).obj.obj U)
      (x : M.val.obj U),
      f.val.app U (pbcTensorSection (constantMap l E F i W)
        (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n)) U b
        ((((ordinaryReductionAdj l E W).unit.app M ≫
          limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
            ((ordinaryReduction l E W).obj M)) (op n)).val.app U) x)) =
      g.val.app U (pbcTensorSection (constantMap l E F i W)
        (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n)) U b
        ((((ordinaryReductionAdj l E W).unit.app M ≫
          limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
            ((ordinaryReduction l E W).obj M)) (op n)).val.app U) x))) : f = g := by
  let A := (((ordinaryReduction l E W ⋙ systemRestriction l E W).obj M).obj (op n))
  let η := (ordinaryReductionAdj l E W).unit.app M ≫
    limit.π ((coefficientSequenceRestriction l E W).obj
      ((ordinaryReduction l E W).obj M)) (op n)
  have : Epi η := reductionUnit_epi l E W M n
  let η' := (constantRestriction l E W).map η
  have : PreservesFiniteColimits (constantRestriction l E W) :=
    (coefficientRestriction_exact (integralConstantToCompletionOfUniverses l E W)).2
  have : Epi η' := by
    dsimp only [η']
    infer_instance
  apply ((pbcScalarAdjunction (constantMap l E F i W)).homEquiv A N).injective
  apply (cancel_epi η').mp
  ext U x
  change f.val.app U (((pbcScalarAdjunction (constantMap l E F i W)).unit.app A).val.app
      U (η.val.app U x)) =
    g.val.app U (((pbcScalarAdjunction (constantMap l E F i W)).unit.app A).val.app
      U (η.val.app U x))
  erw [(pbcScalarAdjunction_exists (constantMap l E F i W)).exists.choose_spec]
  exact h U 1 x

end WeilConjectures.PurStrictScalar
