/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientReductionComparison
import WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientScalarTowerComparison
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Primitive quotient scalar model existence

Construct the scalar realization by descent from its actual ordinary quotient tower.
Normalization tests whole-system coherent simultaneous quotient presentations.
Source: Stacks 03EK, 03D7, 06YY and 0941.
(blueprint: lem-trf-primitive-quotient-scalar-model-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem sequenceKFlat_of_evaluations (W : Scheme.{t})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hC : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) C := by
  let D := (SemilinearSections.semilinearDerivedSections.{t + 1, t, u}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)).some.systems
  let R := coefficientSequenceCommRingSheaf l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro Z hZ i
  apply (D.componentwise _).2
  intro n
  have hZn : (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex
      (.up ℤ)).obj Z).Acyclic := by
    intro j
    exact (hZ j).map (coefficientSequenceEvaluation l E W n)
  have ht := hC n _ hZn
  exact (ht i).of_iso (coefficientEvaluationTensorIso l E W n Z C).symm

/- STATEMENT-DISPUTED: the retired primitiveQuotientScalarModelNormalization
quantified over an arbitrary realization. Unit twisting contradicts that assertion;
the construction below chooses the realization together with its normalization. -/

/-- The scalar realization is obtained by descending its strict tensor comparison.
Source: Stacks 03EK, 03D7, 06YY and 0941.
(blueprint: lem-trf-primitive-quotient-scalar-model-existence).
Proof: choose the actual ordinary quotient model and its derived comparison with
SW. Each evaluated quotient of a good complex is K-flat, hence so is its whole
sequence complex by componentwise tensor and exactness. The scalar cochain counit
therefore computes on these complexes. Combine this counit with the fixed normalized
Roos comparison and the ordinary balanced scalar tower isomorphism. Descend the
resulting natural isomorphism along the good-complex localization. For another
coherent presentation, use its unique strict quotient isomorphism. Naturality of
the cochain counit and Roos comparison and cancellation of this strict isomorphism
give the normalization equation. -/
theorem primitiveQuotientScalarModelExistence
    (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (SW : CoefficientDerivedSystemCalculus l E W)
    (ρW : IntegralComparisonRoosModel l L W) :
    Nonempty (IntegralComparisonScalarModel l E L ι W SW ρW) := by
  obtain ⟨M, D, hD⟩ := coherentQuotientReductionComparison l E W _hlW SW
  obtain ⟨θ, hθ⟩ := ordinaryQuotientScalarTowerComparison l E L ι W M
  let A := (integralOperationsGoodComplex l E W).ι
  let R := M.quotient l E W
  let F := (integralComparisonSequenceScalarModel l E L ι W).E
  let U := coefficientSequenceRestriction l L W
  let H : (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l L W) ℤ) ⥤
      DerivedCategory (scalarReductionSource l L W) :=
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  let T := F.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let LL := coefficientSequenceLimit l L W
  let V := integralComparisonDerivedSequenceScalar l E L ι W ⋙ LL
  let η : DerivedCategory.Q ⋙ V ⟶ T ⋙ H :=
    Functor.whiskerRight (integralComparisonSequenceScalarModel l E L ι W).ε LL ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (Functor.isoWhiskerRight U.mapDerivedCategoryFactors
            (coefficientConstantTowerLimit l L W) ≪≫
          Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ)) ρW.comparison).hom
  have hη (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      IsIso (η.app (R.obj P.obj)) := by
    have hk : CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) (R.obj P.obj) := by
      apply sequenceKFlat_of_evaluations l E W
      intro n
      exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E W n)
        ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P.obj).symm
        ((coefficientTensorModelPreservation l E W).1 P.obj P.property.1 n)
    have := (integralComparisonSequenceScalarModel l E L ι W).computes _ hk
    dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  let d : integralOperationsGoodLocalization l E W ⋙ SW.reduction ≅
      A ⋙ R ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      haveI := D.reduction_isIso P.obj P.property.1 P.property.2
      exact asIso (D.reductionComparison.app P.obj)) (by
        intro P Q a
        exact D.reductionComparison.naturality a.hom)
  have : IsIso (Functor.whiskerLeft (A ⋙ R) η) :=
    (NatTrans.isIso_iff_isIso_app _).2 hη
  let δ : integralOperationsGoodLocalization l E W ⋙ (SW.reduction ⋙ V) ≅
      integralScalarOnGood l E L ι W :=
    Functor.isoWhiskerRight d V ≪≫ asIso (Functor.whiskerLeft (A ⋙ R) η) ≪≫
      Functor.isoWhiskerLeft A (Functor.isoWhiskerRight θ H)
  obtain ⟨r, hr, _⟩ :=
    (integralScalarExtensionWellDefined l E L ι W).2.choose_spec.choose_spec.2.2.1
      (SW.reduction ⋙ V) δ
  change Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E W) r ≪≫ δ =
    integralScalarExtensionComparisonOfUniverses l E L ι W at hr
  refine ⟨⟨r, ?_⟩⟩
  intro P C e κ hp hc
  obtain ⟨a, ha, hκ⟩ := hD P C e κ hp hc
  let q := T.mapIso a.symm ≪≫ θ.app P.obj
  refine ⟨q, hθ P.obj C a κ hκ, ?_⟩
  have he := congrArg (fun z ↦ z.hom.app P) hr
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (V.map (D.reductionComparison.app P.obj) ≫ η.app (R.obj P.obj) ≫
        H.map (θ.hom.app P.obj)) =
    (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P at he
  have hn := η.naturality a.hom
  change V.map (DerivedCategory.Q.map a.hom) ≫ η.app C =
    η.app (R.obj P.obj) ≫ H.map (T.map a.hom) at hn
  have hq : T.map a.hom ≫ q.hom = θ.hom.app P.obj := by
    dsimp only [q]
    change T.map a.hom ≫ (T.map a.inv ≫ θ.hom.app P.obj) = _
    rw [← Category.assoc, ← T.map_comp, a.hom_inv_id, T.map_id, Category.id_comp]
  have hcancel : H.map (T.map a.hom) ≫ H.map q.hom = H.map (θ.hom.app P.obj) := by
    rw [← H.map_comp, hq]
  have hcomp : V.map e.hom ≫ η.app C ≫ H.map q.hom =
      V.map (D.reductionComparison.app P.obj) ≫ η.app (R.obj P.obj) ≫
        H.map (θ.hom.app P.obj) := by
    rw [← ha, V.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (V.map (DerivedCategory.Q.map a.hom)), hn]
    simp only [Category.assoc]
    rw [hcancel]
  have hηC : LL.map ((integralComparisonSequenceScalarModel l E L ι W).ε.app C) ≫
      (integralComparisonRoosBridge l L W ρW _).hom = η.app C := by
    rfl
  have hfirst :
      LL.map ((integralComparisonDerivedSequenceScalar l E L ι W).map e.hom) ≫
        LL.map ((integralComparisonSequenceScalarModel l E L ι W).ε.app C) ≫
          (integralComparisonRoosBridge l L W ρW _).hom ≫ H.map q.hom =
      V.map e.hom ≫ η.app C ≫ H.map q.hom := by
    simpa only [V, Functor.comp_map, Category.assoc] using
      congrArg (fun g ↦ V.map e.hom ≫ g ≫ H.map q.hom) hηC
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (LL.map ((integralComparisonDerivedSequenceScalar l E L ι W).map e.hom) ≫
        LL.map ((integralComparisonSequenceScalarModel l E L ι W).ε.app C) ≫
          (integralComparisonRoosBridge l L W ρW _).hom ≫ H.map q.hom) = _
  rw [hfirst, hcomp]
  exact he

end WeilConjectures
