/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import all WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientNormalization
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
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarTensorSubstitution
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarPullbackSubstitution

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients

attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar sfConstructibleIntegralScalarExtension substituteInputs
  ScalarExtensionTower.tensor coefficientTotalTensor sourceExpression targetExpression
  constructibleIntegralPullback constructibleIntegralTensor IntegralCoherence.complexMonoidal
  SheafOfModules.cochainModulesMonoidal

section

attribute [local irreducible] pullbackTensorCalculus integralDerivedPullback
  integralCompletedTensor coefficientTotalTensor SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory

private theorem scalar_substitution_naturality {W : Scheme.{u}}
    {ρ : IntegralComparisonRoosModel l L W}
    (S : IntegralComparisonScalarModel l E L ι W (pullbackTensorCalculus l E W) ρ)
    {K K' : DerivedCategory (scalarReductionSource l E W)}
    {A A' : StrictQuotient.Complex l E W}
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (β' : K' ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A'))
    (k : K ⟶ K') (a : A ⟶ A')
    (hc : k ≫ β' = β ≫ (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map a)) :
    (integralScalarExtension l E L ι W).map k ≫ scalarSubstitution l E L ι S A' β' =
      scalarSubstitution l E L ι S A β ≫ (coefficientSequenceLimit l L W).map
        (DerivedCategory.Q.map ((ScalarExtensionTower.scalar l E L ι W).map a)) := by
  let F := integralComparisonDerivedSequenceScalar l E L ι W
  let R := (pullbackTensorCalculus l E W).reduction
  let LL := coefficientSequenceLimit l L W
  have he := (integralComparisonSequenceScalarModel l E L ι W).ε.naturality a
  change F.map (DerivedCategory.Q.map a) ≫
      (integralComparisonSequenceScalarModel l E L ι W).ε.app A' =
    (integralComparisonSequenceScalarModel l E L ι W).ε.app A ≫
      DerivedCategory.Q.map ((ScalarExtensionTower.scalar l E L ι W).map a) at he
  have hd := reduction_naturality l E β β' k (DerivedCategory.Q.map a) hc
  have hs : (integralScalarExtension l E L ι W).map k ≫ S.realization.hom.app K' =
      S.realization.hom.app K ≫ LL.map (F.map (R.map k)) :=
    S.realization.hom.naturality k
  unfold scalarSubstitution
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hs]
  simp only [Category.assoc]
  rw [← LL.map_comp_assoc, ← F.map_comp, hd, F.map_comp, LL.map_comp]
  simp only [Category.assoc]
  rw [← LL.map_comp, he, LL.map_comp]

private theorem system_good_iso {W : Scheme.{u}}
    {A B : StrictQuotient.Complex l E W} (e : A ≅ B)
    (hA : StrictQuotient.SystemGood l E A) : StrictQuotient.SystemGood l E B := by
  refine ⟨SheafOfModules.kFlat_iso_independent _ e hA.1, ?_⟩
  intro i
  have h := SheafOfModules.flatOnSite_of_iso
    (coefficientSequenceCommRingSheaf l E W)
    (HomologicalComplex.eval _ _ i |>.mapIso e) (hA.2 i)
  exact h

end

attribute [local irreducible] coefficientSequenceLimit coefficientConstantTowerLimit
  HasDerivedCategory.standard

/-- The right scalar coordinate for arbitrary good quotient substitutions.
Source: Stacks 07A4 and 0941; the categorical part of the right route coordinate.
(blueprint: lem-pur-completed-scalar-right-substitution).

Proof: scalar substitution naturality moves t across the given compatible strict
comparison. Apply tensor scalar substitution at X, scalar pullback substitution
on both inputs, and tensor substitution naturality for the two kappa maps. -/
theorem scalarRouteRightSubstitution
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    {ρX : IntegralComparisonRoosModel l L X} {ρY : IntegralComparisonRoosModel l L Y}
    (SX : IntegralComparisonScalarModel l E L ι X (pullbackTensorCalculus l E X) ρX)
    (SY : IntegralComparisonScalarModel l E L ι Y (pullbackTensorCalculus l E Y) ρY)
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (A : Fin 3 → StrictQuotient.Complex l E Y)
    (hA : ∀ i, StrictQuotient.SystemGood l E (A i))
    (hP : ∀ i, StrictQuotient.SystemGood l E (StrictQuotient.pull l E f (A i)))
    (hgoodL : ∀ i, StrictQuotient.SystemGood l L
      (StrictQuotient.pull l L f ((ScalarExtensionTower.scalar l E L ι Y).obj (A i))))
    (β : ∀ i, (M i).obj ⟶ (coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj (A i)))
    (t : (integralDerivedPullback l E f).obj
        ((integralCompletedTensor l E Y).obj ((M 0).obj, (M 1).obj)) ⟶
      (integralCompletedTensor l E X).obj
        ((integralDerivedPullback l E f).obj (M 0).obj,
          (integralDerivedPullback l E f).obj (M 1).obj))
    (hc : t ≫ tensorSubstitution l E (StrictQuotient.pull l E f (A 0))
        (StrictQuotient.pull l E f (A 1)) (hP 0) (hP 1)
        (pullSubstitution l E f (A 0) (β 0)) (pullSubstitution l E f (A 1) (β 1)) =
      pullSubstitution l E f (StrictQuotient.total l E (A 0) (A 1))
        (tensorSubstitution l E (A 0) (A 1) (hA 0) (hA 1) (β 0) (β 1)) ≫
        (coefficientSequenceLimit l E X).map
          (DerivedCategory.Q.map (comparison l E f (A 0) (A 1)).hom)) :
    let C := fun i ↦ (ScalarExtensionTower.scalar l E L ι Y).obj (A i)
    let βs := fun i ↦ scalarSubstitution l E L ι SY (A i) (β i)
    scalarSubstitution l E L ι SX
      (StrictQuotient.pull l E f (StrictQuotient.total l E (A 0) (A 1)))
      (pullSubstitution l E f (StrictQuotient.total l E (A 0) (A 1))
        (tensorSubstitution l E (A 0) (A 1) (hA 0) (hA 1)
          (β 0) (β 1))) ≫
        (coefficientSequenceLimit l L X).map
          (DerivedCategory.Q.map (scalarRight l E L ι f (A 0) (A 1)).hom) =
      (integralScalarExtension l E L ι X).map t ≫
      (integralTensorScalarComparison l E L ι X
        ((constructibleIntegralPullback l E f).obj (M 0))
        ((constructibleIntegralPullback l E f).obj (M 1))).hom.hom ≫
      (integralCompletedTensor l L X).map (Prod.mkHom
        (integralPullbackScalarComparison l E L ι f (M 0)).hom.hom
        (integralPullbackScalarComparison l E L ι f (M 1)).hom.hom) ≫
      tensorSubstitution l L (StrictQuotient.pull l L f (C 0))
        (StrictQuotient.pull l L f (C 1))
        (hgoodL 0) (hgoodL 1)
        (pullSubstitution l L f (C 0) (βs 0)) (pullSubstitution l L f (C 1) (βs 1)) := by
  dsimp only
  let C (i : Fin 3) := (ScalarExtensionTower.scalar l E L ι Y).obj (A i)
  let βs (i : Fin 3) := scalarSubstitution l E L ι SY (A i) (β i)
  let LL := coefficientSequenceLimit l L X
  have hn := scalar_substitution_naturality l E L ι SX
    (pullSubstitution l E f (StrictQuotient.total l E (A 0) (A 1))
      (tensorSubstitution l E (A 0) (A 1) (hA 0) (hA 1)
        (β 0) (β 1)))
    (tensorSubstitution l E (StrictQuotient.pull l E f (A 0))
      (StrictQuotient.pull l E f (A 1)) (hP 0)
      (hP 1) (pullSubstitution l E f (A 0) (β 0))
      (pullSubstitution l E f (A 1) (β 1)))
    t (comparison l E f (A 0) (A 1)).hom hc
  have hβ (i : Fin 3) := completedScalarPullbackSubstitution l E L ι f SX SY (M i) (A i)
    (hA i) (β i)
  have hgood (i : Fin 3) : StrictQuotient.SystemGood l L
      ((ScalarExtensionTower.scalar l E L ι X).obj (StrictQuotient.pull l E f (A i))) :=
    system_good_iso l L ((ScalarExtensionTower.kappa l E L ι f).app (A i)).symm
      (hgoodL i)
  have ht := completedScalarTensorSubstitution l E L ι SX
    ((constructibleIntegralPullback l E f).obj (M 0))
    ((constructibleIntegralPullback l E f).obj (M 1))
    (StrictQuotient.pull l E f (A 0)) (StrictQuotient.pull l E f (A 1))
    (hP 0) (hP 1) (hgood 0) (hgood 1)
    (pullSubstitution l E f (A 0) (β 0)) (pullSubstitution l E f (A 1) (β 1))
  have htn := tensor_substitution_naturality l L (hgood 0)
    (hgoodL 0) (hgood 1) (hgoodL 1)
    (scalarSubstitution l E L ι SX (StrictQuotient.pull l E f (A 0))
      (pullSubstitution l E f (A 0) (β 0)))
    (pullSubstitution l L f (C 0) (βs 0))
    (scalarSubstitution l E L ι SX (StrictQuotient.pull l E f (A 1))
      (pullSubstitution l E f (A 1) (β 1)))
    (pullSubstitution l L f (C 1) (βs 1))
    (integralPullbackScalarComparison l E L ι f (M 0)).hom.hom
    (integralPullbackScalarComparison l E L ι f (M 1)).hom.hom
    ((ScalarExtensionTower.kappa l E L ι f).hom.app (A 0))
    ((ScalarExtensionTower.kappa l E L ι f).hom.app (A 1))
    (hβ 0).symm (hβ 1).symm
  with_unfolding_all
    unfold scalarRight
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
    rw [← Category.assoc, ← Category.assoc, ← hn]
    simp only [Category.assoc]
    rw [reassoc_of% ht]
    simp only [Iso.prod_hom, Iso.app_hom]
    dsimp only [ScalarExtensionTower.tensor]
    rw [← htn]

end WeilConjectures.CompletedQuotient
