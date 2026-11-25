/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels

/-!
# The actual completion unit on a strict quotient cone

Source: blueprint main-20261015, trace formula, rational Frobenius integral model,
proof (2)--(3); Stacks 07A6, 09T5, 0D6E, 0941 and 08TC. This is the normalization
refinement of those constructions, not a verbatim assertion of a Stacks tag.
(blueprint: lem-trf-completion-unit-strict-quotient-model).

The auxiliary structures package canonical constructions and their normalization
conditions. They introduce no alternative tensor, limit, or derived category.
The theorem asserts their existence together with the whole-morphism unit formula.
The compatible-model construction is isolated in `canonicalModels`; the proof here
derives the cone, unit and two-resolution formulas from its normalizations.
Index n denotes the positive exponent n+1. Site and coefficient universes are independent.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures
namespace CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private theorem limitUnit_isIso
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective] :
    IsIso (D.limitUnit.app J) := by
  have hn := D.limitUnit_normalization J
  have : IsIso (D.limitUnit.app J ≫
      ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom

private theorem unit_at_complex
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite) :
    S.adjunction.unit.app (DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map (M.coneAugmentation l E W Q) ≫
        (D.completionComparison l E W Q hQ hflat).hom := by
  have := D.reduction_isIso Q hQ hflat
  apply (cancel_mono ((coefficientSequenceLimit l E W).map
    (D.reductionComparison.app Q))).1
  have h := D.hom_normalization Q ((M.quotient l E W).obj Q) (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Adjunction.homEquiv_unit] at h
  erw [Category.comp_id, Category.comp_id] at h
  rw [h, D.systemUnit_composition]
  dsimp only [DerivedModel.completionComparison, OrdinaryModel.coneAugmentation,
    OrdinaryModel.augmentation, OrdinaryModel.transpose, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app, asIso_inv]
  simp only [Category.assoc]
  simp only [← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← D.roos_normalization]
  simp only [Category.assoc]

private theorem augmentation_sections (M : OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (p : ℤ) (n : ℕ) (V : W.ProEtᵒᵖ) (x : (Q.X p).val.obj V) :
    (((M.augmentation l E W Q ≫
        limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor
          (op n)).f p ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
          (((M.quotient l E W).obj Q).X p) ≫
        (scalarReductionRestriction l E W n).map
          ((M.evaluation n).hom.app (Q.X p))).val.app V) x =
      unrestrictedIntegralTensorSection l E W n (Q.X p) V 1 x := by
  have hu : (M.augmentation l E W Q).f p =
      M.adjunction.unit.app (Q.X p) ≫
        (M.limitComparison.hom.app ((M.quotient l E W).obj Q)).f p := by
    dsimp only [OrdinaryModel.augmentation, OrdinaryModel.transpose]
    rw [Adjunction.homEquiv_unit]
    simp only [CategoryTheory.Functor.map_id, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, Adjunction.mapHomologicalComplex_unit_app_f]
    erw [Category.comp_id]
  have hp := M.limitComparison_projection ((M.quotient l E W).obj Q) n p
  rw [HomologicalComplex.comp_f] at hp
  have hproj : (M.augmentation l E W Q ≫
      limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor (op n)).f p =
      M.adjunction.unit.app (Q.X p) ≫ limit.π
        ((coefficientSequenceRestriction l E W).obj
          (((M.quotient l E W).obj Q).X p)) (op n) := by
    rw [HomologicalComplex.comp_f, hu, Category.assoc, hp]
  rw [hproj]
  exact M.unit_tensor (Q.X p) n V x

end CompletionUnit
end WeilConjectures
