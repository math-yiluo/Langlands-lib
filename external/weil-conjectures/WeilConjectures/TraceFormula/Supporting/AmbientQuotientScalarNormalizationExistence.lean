/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientModelComparison
import WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientScalarTowerComparison
import all WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence
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

/-! # Ambient scalar quotient normalization

Source: Stacks 06YY and 0941; the scalar quotient construction in the final
common-stage transport paragraph of the trace-transport blueprint.
(blueprint: new-trf-ambient-quotient-scalar-normalization)

Proof: transport the balanced finite quotient tensor association through the
canonical coherent quotient comparison and the normalized Roos bridge; its
unit-tensor equation gives the required whole-system normalization.
-/

@[expose] public noncomputable section
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard

/- STATEMENT-DISPUTED: the former statement normalized every realization. A nontrivial
scalar-unit twist preserves being an isomorphism but changes the prescribed Roos equation.
The corrected theorem below constructs its realization together with normalization. -/

/-- Choose the ambient scalar realization together with its prescribed coherent
quotient normalization. Source: Stacks 06YY and 0941; strict quotient scalar
construction in the common-stage transport argument.
(blueprint: new-trf-ambient-quotient-scalar-normalization).

Proof: construct ordinary and derived quotient models for the supplied calculus.
The evaluated quotients of a good complex are K-flat, hence their whole system is
K-flat. Compose the derived scalar counit, the normalized Roos comparison, and
the ordinary balanced scalar tower association. Descend this natural isomorphism
along the good-complex localization. A coherent presentation differs from the
canonical quotient by a strict isomorphism. Naturality of the counit and Roos
comparison and cancellation of that isomorphism give the required whole-system
equation, while the ordinary balanced association gives its generator formula.
The realization must be chosen by this construction: an arbitrary realization
can be twisted by a scalar unit and need not satisfy normalization. -/
theorem ambientQuotientScalarModel_normalization_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X) :
    ∃ realization : integralScalarExtensionOfUniverses l E L ι X ≅
        S.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι X ⋙
          coefficientSequenceLimit l L X,
      IsIntegralComparisonScalarNormalized l E L ι X S ρ realization := by
  obtain ⟨M, ⟨D⟩⟩ := CompletionUnit.fixedCalculusModels l E X S
  obtain ⟨θ, hθ⟩ := ordinaryQuotientScalarTowerComparison l E L ι X M
  let A := (integralOperationsGoodComplex l E X).ι
  let R := M.quotient l E X
  let F := (integralComparisonSequenceScalarModel l E L ι X).E
  let U := coefficientSequenceRestriction l L X
  let H : (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l L X) ℤ) ⥤
      DerivedCategory (scalarReductionSource l L X) :=
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  let T := F.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let LL := coefficientSequenceLimit l L X
  let V := integralComparisonDerivedSequenceScalar l E L ι X ⋙ LL
  let η : DerivedCategory.Q ⋙ V ⟶ T ⋙ H :=
    Functor.whiskerRight (integralComparisonSequenceScalarModel l E L ι X).ε LL ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (Functor.isoWhiskerRight U.mapDerivedCategoryFactors
            (coefficientConstantTowerLimit l L X) ≪≫
          Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ)) ρ.comparison).hom
  have hη (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
      IsIso (η.app (R.obj P.obj)) := by
    have hk : CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E X) (R.obj P.obj) := by
      apply sequenceKFlat_of_evaluations l E X
      intro n
      exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E X n)
        ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P.obj).symm
        ((coefficientTensorModelPreservation l E X).1 P.obj P.property.1 n)
    have := (integralComparisonSequenceScalarModel l E L ι X).computes _ hk
    dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  let d : integralOperationsGoodLocalization l E X ⋙ S.reduction ≅
      A ⋙ R ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      have := D.reduction_isIso P.obj P.property.1 P.property.2
      exact asIso (D.reductionComparison.app P.obj)) (by
        intro P Q a
        exact D.reductionComparison.naturality a.hom)
  have : IsIso (Functor.whiskerLeft (A ⋙ R) η) :=
    (NatTrans.isIso_iff_isIso_app _).2 hη
  let δ : integralOperationsGoodLocalization l E X ⋙ (S.reduction ⋙ V) ≅
      integralScalarOnGood l E L ι X :=
    Functor.isoWhiskerRight d V ≪≫ asIso (Functor.whiskerLeft (A ⋙ R) η) ≪≫
      Functor.isoWhiskerLeft A (Functor.isoWhiskerRight θ H)
  obtain ⟨r, hr, _⟩ :=
    (integralScalarExtensionWellDefined l E L ι X).2.choose_spec.choose_spec.2.2.1
      (S.reduction ⋙ V) δ
  change Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E X) r ≪≫ δ =
    integralScalarExtensionComparisonOfUniverses l E L ι X at hr
  refine ⟨r, ?_⟩
  intro P C e κ _hp hc
  obtain ⟨a, ha, hκ⟩ := coherentQuotientModelComparison l E X S M D P.obj C e κ hc
  let q := T.mapIso a.symm ≪≫ θ.app P.obj
  refine ⟨q, hθ P.obj C a κ hκ, ?_⟩
  have he := congrArg (fun z ↦ z.hom.app P) hr
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (V.map (D.reductionComparison.app P.obj) ≫ η.app (R.obj P.obj) ≫
        H.map (θ.hom.app P.obj)) =
    (integralScalarExtensionComparisonOfUniverses l E L ι X).hom.app P at he
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
  have hηC : LL.map ((integralComparisonSequenceScalarModel l E L ι X).ε.app C) ≫
      (integralComparisonRoosBridge l L X ρ _).hom = η.app C := by
    rfl
  have hfirst :
      LL.map ((integralComparisonDerivedSequenceScalar l E L ι X).map e.hom) ≫
        LL.map ((integralComparisonSequenceScalarModel l E L ι X).ε.app C) ≫
          (integralComparisonRoosBridge l L X ρ _).hom ≫ H.map q.hom =
      V.map e.hom ≫ η.app C ≫ H.map q.hom := by
    simpa only [V, Functor.comp_map, Category.assoc] using
      congrArg (fun g ↦ V.map e.hom ≫ g ≫ H.map q.hom) hηC
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (LL.map ((integralComparisonDerivedSequenceScalar l E L ι X).map e.hom) ≫
        LL.map ((integralComparisonSequenceScalarModel l E L ι X).ε.app C) ≫
          (integralComparisonRoosBridge l L X ρ _).hom ≫ H.map q.hom) = _
  rw [hfirst, hcomp]
  exact he

end WeilConjectures
