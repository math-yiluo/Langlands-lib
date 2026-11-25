/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFiniteMateComparison

/-! # The natural cochain comparison for completed-coefficient reduction

Source: Stacks 07A6, 09T5, 0D6E and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : Scheme.{t})

namespace ReductionCochainComparison

set_option backward.defeqAttrib.useBackward true

-- The cone of ordinary inverse-limit projections in each degree.
private def termwiseLimitCone
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) : Cone Z.asFunctor where
  pt := ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
    scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj Z
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app Z
      naturality := by
        intro n m f
        ext p : 1
        change 𝟙 _ ≫ limit.π (Z.X p) m =
          limit.π (Z.X p) n ≫ (Z.X p).map f
        exact (Category.id_comp _).trans (limit.w (Z.X p) f).symm }

private def termwiseLimitConeIsLimit
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    IsLimit (termwiseLimitCone l E W Z) :=
  HomologicalComplex.isLimitOfEval Z.asFunctor (termwiseLimitCone l E W Z)
    (fun p ↦ limit.isLimit (Z.X p))

private def termwiseLimitComparisonComponent
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj Z ≅
        limit Z.asFunctor :=
  (termwiseLimitConeIsLimit l E W Z).conePointUniqueUpToIso (limit.isLimit _)

private theorem termwiseLimitComparisonComponent_projection
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    (termwiseLimitComparisonComponent l E W Z).hom ≫ limit.π Z.asFunctor (op n) =
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app Z :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

private def termwiseLimitComparison :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅
        roosLimitFunctor (A := scalarReductionSource l E W) :=
  NatIso.ofComponents (termwiseLimitComparisonComponent l E W) (by
    intro X Y f
    apply limit.hom_ext
    intro n
    change ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map f ≫
        ((termwiseLimitComparisonComponent l E W Y).hom ≫ limit.π Y.asFunctor n) =
      (termwiseLimitComparisonComponent l E W X).hom ≫
        (limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) ≫
          limit.π Y.asFunctor n)
    erw [termwiseLimitComparisonComponent_projection l E W Y n.unop]
    erw [limMap_π]
    erw [← Category.assoc,
      termwiseLimitComparisonComponent_projection l E W X n.unop]
    ext p : 1
    exact limMap_π (f.f p) n)

private theorem termwiseLimitComparison_projection
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) (p : ℤ) :
    ((termwiseLimitComparison l E W).hom.app Z ≫ limit.π Z.asFunctor (op n)).f p =
      limit.π (Z.X p) (op n) :=
  congrArg (fun f ↦ f.f p) (termwiseLimitComparisonComponent_projection l E W Z n)

private def constantLimitUnit :
    roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W := by
  let A := ℕᵒᵖ ⥤ scalarReductionSource l E W
  let B := scalarReductionSource l E W
  let F : A ⥤ B := lim
  let π := HomotopyCategory.quotient A (.up ℤ)
  let e : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      π ⋙ (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  exact (Functor.isoWhiskerRight (termwiseLimitComparison l E W).symm
      DerivedCategory.Q).hom ≫ e.hom ≫
    Functor.whiskerLeft π F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        F.rightDerivedFunctor).hom

private theorem constantLimitUnit_normalization
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective] :
    (constantLimitUnit l E W).app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
      DerivedCategory.Q.map ((termwiseLimitComparison l E W).inv.app J) := by
  dsimp only [coefficientConstantTowerLimit]
  have hqA : (DerivedCategory.quotientCompQhIso
      (ℕᵒᵖ ⥤ scalarReductionSource l E W)).hom.app J = 𝟙 _ := rfl
  have hqiB (K : CochainComplex (scalarReductionSource l E W) ℤ) :
      (DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app K =
        𝟙 _ := rfl
  have hf : ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomotopyCategoryFactors (.up ℤ)).inv.app J =
        𝟙 _ := rfl
  dsimp only [constantLimitUnit, Functor.rightDerivedFunctorObjQIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, asIso_inv, Iso.app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [hqA, hqiB, hf]
  simp only [Functor.comp_obj, Functor.mapHomotopyCategory_obj,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    IsIso.hom_inv_id_assoc, Category.comp_id]

end ReductionCochainComparison

/-- Reduction's cochain counit, before changing the coefficient field.

Source: Stacks sites-cohomology.tex, lemma-adjoint (07A6),
lemma-derived-pushforward-composition (0D6E), and derived.tex,
lemma-derived-adjoint-functors (09T5); step 1 of
stage3-pur-extension-strict-derived-comparison.
(blueprint: stage3-pur-reduction-natural-cochain-comparison).

Proof: take the standard right-derived limit unit, transported along the canonical
termwise-limit isomorphism. Compose with the exact restriction comparison and
M.limitComparison to obtain the system limit unit. Localize the ordinary tensor
unit and follow it by this system unit. Transpose this natural transformation
through S.adjunction; naturality follows from naturality of its Hom equivalence.
The resulting comparison has exactly the ordinary-unit transpose required by
CompletionUnit.finiteComparison_of_unit. Apply that lemma to compute its finite
values on flat-term K-flat complexes. No construction of a new derived adjunction
or universal left-derived functor is needed. The construction applies to every
scheme, unbounded complexes, zero complexes, and n = 0. -/
theorem coefficientReductionNaturalCochainComparison
    (S : CoefficientDerivedSystemCalculus l E W)
    (M : CompletionUnit.OrdinaryModel l E W) :
    ∃ ε : DerivedCategory.Q ⋙ S.reduction ⟶
        M.quotient l E W ⋙ DerivedCategory.Q,
      ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E W n).map (ε.app P.obj) ≫
            (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
              ((M.quotient l E W).obj P.obj) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P.obj) =
          (S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P.obj) ≫
            (coefficientFiniteReductionModel l E W P.obj P.property.1 n).hom := by
  let c := ReductionCochainComparison.termwiseLimitComparison l E W
  let η := ReductionCochainComparison.constantLimitUnit l E W
  let δ : (CompletionUnit.ordinaryLimit l E W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ coefficientSequenceLimit l E W :=
    Functor.whiskerRight M.limitComparison.hom DerivedCategory.Q ≫
      Functor.whiskerLeft (CompletionUnit.tower l E W) η ≫
      Functor.whiskerRight
        (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv
        (coefficientConstantTowerLimit l E W)
  let β : DerivedCategory.Q ⟶
      (M.quotient l E W ⋙ DerivedCategory.Q) ⋙ coefficientSequenceLimit l E W :=
    Functor.whiskerRight (M.adjunction.mapHomologicalComplex (.up ℤ)).unit
      DerivedCategory.Q ≫ Functor.whiskerLeft (M.quotient l E W) δ
  let ε : DerivedCategory.Q ⋙ S.reduction ⟶
      M.quotient l E W ⋙ DerivedCategory.Q :=
    { app := fun Q ↦ (S.adjunction.homEquiv _ _).symm (β.app Q)
      naturality := by
        intro P Q f
        apply (S.adjunction.homEquiv _ _).injective
        change S.adjunction.homEquiv _ _
            (S.reduction.map (DerivedCategory.Q.map f) ≫ _) =
          S.adjunction.homEquiv _ _ (_ ≫ DerivedCategory.Q.map ((M.quotient l E W).map f))
        rw [S.adjunction.homEquiv_naturality_left,
          S.adjunction.homEquiv_naturality_right]
        dsimp only [Functor.comp_obj]
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact β.naturality f }
  refine ⟨ε, fun P n ↦ ?_⟩
  apply CompletionUnit.finiteComparison_of_unit l E W S M c
    (ReductionCochainComparison.termwiseLimitComparison_projection l E W) η
    (ReductionCochainComparison.constantLimitUnit_normalization l E W) ε
    ?_ P.obj P.property.1 P.property.2 n
  intro Q
  change (S.adjunction.homEquiv _ _)
    ((S.adjunction.homEquiv _ _).symm (β.app Q)) = _
  rw [Equiv.apply_symm_apply]
  rfl

end WeilConjectures
