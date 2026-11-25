/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitDerivedAdjunctionComparison
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Canonical ordinary and derived models of the completion adjunction

Source: Stacks 07A6, 09T5, 0D6E, 0941 and the normalization refinement in
lem-trf-completion-unit-strict-quotient-model, steps 1--4.
(blueprint: lem-trf-completion-unit-canonical-models).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

section CanonicalComparisons

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

private theorem constantLimitUnit_isRightDerived :
    (coefficientConstantTowerLimit l E W).IsRightDerivedFunctor
      (constantLimitUnit l E W)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ)) := by
  let A := ℕᵒᵖ ⥤ scalarReductionSource l E W
  let F : A ⥤ scalarReductionSource l E W := lim
  let e := Functor.isoWhiskerRight (termwiseLimitComparison l E W) DerivedCategory.Q
  have h : (CochainComplex.KInjectives.localizerMorphism A).Derives
      (roosLimitFunctor ⋙ DerivedCategory.Q) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _
      (Functor.isoWhiskerLeft (CochainComplex.KInjectives.localizerMorphism A).functor e)).mp
        (CategoryTheory.derives F)
  apply h.isRightDerivedFunctor_of_isIso (constantLimitUnit l E W)
  intro I
  have : I.obj.IsKInjective := I.property
  have hn := constantLimitUnit_normalization l E W I.obj
  have : IsIso ((constantLimitUnit l E W).app I.obj ≫
      (F.rightDerivedFunctorObjQIso I.obj).hom) := by
    rw [hn]
    infer_instance
  change IsIso ((constantLimitUnit l E W).app I.obj)
  exact IsIso.of_isIso_comp_right ((constantLimitUnit l E W).app I.obj)
    (F.rightDerivedFunctorObjQIso I.obj).hom

private theorem constantRoosComparison_exists :
    ∃ r : roosF (A := scalarReductionSource l E W) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W,
      ∀ Z, DerivedCategory.Q.map (roosι Z) ≫ r.hom.app Z =
        (constantLimitUnit l E W).app Z := by
  let R := SheafOfModules.derivedChangeRingIndependentCoefficients
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)
  let : HasExactLimitsOfShape (Discrete ℕ) (scalarReductionSource l E W) :=
    Scheme.ProEt.products_exact W R ℕ
  obtain ⟨CF, κ, hCF, _⟩ := strictRoosDerivation.{t+1, t, u}
    (Scheme.ProEt.topology W) R (fun U a b ↦
      @mul_comm ((completedIntegralCommRingSheafUnrestricted l E W).obj.obj U)
        inferInstance a b)
  let := hCF
  let := constantLimitUnit_isRightDerived l E W
  let V := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ)
  let ρ : CF ≅ coefficientConstantTowerLimit l E W :=
    CF.rightDerivedUnique _ (roosDerivedUnit κ) (constantLimitUnit l E W) V
  let r := κ ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q ρ
  refine ⟨r, ?_⟩
  intro Z
  have h := CF.rightDerivedNatTrans_app _ (roosDerivedUnit κ)
    (constantLimitUnit l E W) V (𝟙 _) Z
  simpa [r, ρ, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
    roosDerivedUnit, roosInclusion, roosLimitFunctor,
    Functor.rightDerivedNatTrans, Category.assoc] using h

end CanonicalComparisons

/-- The ordinary tensor/limit adjunction and its derived comparison can be chosen
compatibly with the coherent coefficient calculus. This asserts the construction
and comparison normalizations only; it makes no assertion about the strict cone
augmentation or the completion unit formula.

Source: Stacks 03D7 (ordinary adjunction), 07A6 and 09T5 (derived adjunction), 0D6E
(composition), and 0941 (Roos), with steps 1--4 of
lem-trf-completion-unit-strict-quotient-model, an agent normalization refinement.
(blueprint: lem-trf-completion-unit-canonical-models).

Proof: Form the strict system whose nth term is scalar extension along the
completion projection and whose transition is the ordinary quotient adjunct.
The scalar-extension Hom bijections identify maps out of this system with
compatible families into the scalar restrictions; the limit universal property
gives its right adjoint. The unit is the family of pure tensors 1 tensor x.
Evaluation of the complex limit cone gives the canonical termwise comparison,
with its stated projections. The system construction is additive.

Choose a coherent calculus S by coefficientDerivedSystemEvaluationCalculus.
Derive the ordinary adjunction using flat-term K-flat representatives on the left
and K-injective representatives on the sequence site on the right. Factor the
right adjoint through exact scalar restriction and constant-ring inverse limit,
and transport the derived adjunction along the normalized composition comparison.
Both its left adjoint and S.reduction are left adjoint to coefficientSequenceLimit.
The unique adjunction-compatible isomorphism between these left adjoints transports
the universal left-derived comparison to reductionComparison. Transport preserves
its universal property and its invertibility on flat-term K-flat complexes.
The resolving Hom equation gives hom_normalization for every chain map.

To check reduction_evaluation, apply the finite scalar-extension Hom bijection to
the evaluated counit. S.counit_projection identifies its transpose with the actual
total-limit projection. The generic sequence comparison has the same projected
counit, and finite derived scalar extension has the same normalized K-flat
comparison. The two finite adjunction mates are therefore equal. On a flat-term
K-flat representative their equality is exactly reduction_evaluation. This is an
adjunction-mate computation, not detection of a derived map by its level values.
The chosen S and its coherence are retained throughout this transport.

Take the canonical right-derived unit of the constant tower limit and transport
through the termwise-limit comparison. It has the prescribed normalization on
K-injectives by the definition of rightDerivedFunctorObjQIso. Exact countable
products on the pro-etale site make the strict Roos cone a right-derived limit
model. Uniqueness of right-derived functors supplies roos, and its unit equation
is roos_normalization. The normalized derived composition theorem gives systemUnit
and its composition equation and proves that it is invertible on K-injective
systems; restriction is exact but need not preserve K-injectivity. These data form
M and D. Zero objects and zero complexes use the same universal properties; there
is no boundedness, completeness, or additional invertibility hypothesis on inputs. -/
theorem canonicalModels [∀ x : W, Invertible (l : W.residueField x)] :
    ∃ (S : CoefficientDerivedSystemCalculus l E W)
      (_coherence : CoefficientDerivedSystemCoherence l E W S)
      (M : OrdinaryModel l E W), Nonempty (DerivedModel l E W S M) := by
  obtain ⟨S, ⟨coherence⟩⟩ := coefficientDerivedSystemEvaluationCalculus l E W
  obtain ⟨M⟩ := ordinaryModel_exists l E W
  obtain ⟨r, hr⟩ := constantRoosComparison_exists l E W
  obtain ⟨hI, ε, hε, hflat, heval, hhom⟩ :=
    derivedAdjunctionComparison_exists l E W S coherence M
      (termwiseLimitComparison l E W) (termwiseLimitComparison_projection l E W)
      (constantLimitUnit l E W) (constantLimitUnit_normalization l E W)
      (constantLimitUnit_isRightDerived l E W)
  refine ⟨S, coherence, M, ⟨{
    towerLimitComparison := termwiseLimitComparison l E W
    towerLimitComparison_projection := termwiseLimitComparison_projection l E W
    limitUnit := constantLimitUnit l E W
    limitUnit_normalization := constantLimitUnit_normalization l E W
    roos := r
    roos_normalization := hr
    systemUnit := systemLimitUnit l E W M (constantLimitUnit l E W)
    system_isIso := hI
    systemUnit_composition := ?_
    reductionComparison := ε
    reduction_isLeftDerived := hε
    reduction_isIso := hflat
    reduction_evaluation := heval
    hom_normalization := hhom }⟩⟩
  intro I
  rfl

end WeilConjectures.CompletionUnit
