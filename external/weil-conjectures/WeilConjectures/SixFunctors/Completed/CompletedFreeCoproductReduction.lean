/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all WeilConjectures.SixFunctors.CompleteLiftedTopCell.CompleteLiftedTopCellTriangle
import all WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
import all WeilConjectures.SixFunctors.Completed.CompletedFreeCellOrdinaryLimit
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Normalized coefficient reduction of actual finite free coproducts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionExtension
attribute [-instance] integralCoefficientAbLocallyBijective integralCoefficientAbSheafify
  GrothendieckTopology.hasSheafify_of_essentiallySmall
/-- The published category structure at the explicit coefficient sizes.
Source: Stacks 03DA (blueprint: lem-sf-completed-free-coproduct-reduction). -/
abbrev completedCoproductLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X

attribute [local instance 6000] completedCoproductLocallyBijective


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The published category structure at the explicit coefficient sizes.
Source: Stacks 03DA (blueprint: lem-sf-completed-free-coproduct-reduction). -/
abbrev completedCoproductSiteSmall : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance 6000] completedCoproductSiteSmall

/-- The published category structure at the explicit coefficient sizes.
Source: Stacks 03DA (blueprint: lem-sf-completed-free-coproduct-reduction). -/
abbrev completedCoproductSourceAbelian :
    Abelian (scalarReductionSource.{u, u} l E X) :=
  @SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
    (integralCoefficientAbSheafify.{u, u} X)
    (integralCoefficientAbLocallyBijective.{u, u} X)

attribute [local instance 3000] completedCoproductSourceAbelian

/-- The published category structure at the explicit coefficient sizes.
Source: Stacks 03DA (blueprint: lem-sf-completed-free-coproduct-reduction). -/
abbrev completedCoproductTargetAbelian :
    Abelian (scalarReductionTarget.{u, u} l E X 0) :=
  @SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
    (integralCoefficientSheaf.{u, u} l E X 0)
    (integralCoefficientAbSheafify.{u, u} X)
    (integralCoefficientAbLocallyBijective.{u, u} X)

attribute [local instance 3000] completedCoproductTargetAbelian

/-- The published category structure at the explicit coefficient sizes.
Source: Stacks 05RU (blueprint: lem-sf-completed-free-coproduct-reduction). -/
abbrev completedCoproductSourceDerived :
    HasDerivedCategory (scalarReductionSource.{u, u} l E X) :=
  scalarReductionSourceDerived.{u, u} l E X

attribute [local instance 2000] completedCoproductSourceDerived

/-- The published category structure at the explicit coefficient sizes.
Source: Stacks 05RU (blueprint: lem-sf-completed-free-coproduct-reduction). -/
abbrev completedCoproductTargetDerived :
    HasDerivedCategory (scalarReductionTarget.{u, u} l E X 0) :=
  scalarReductionTargetDerived.{u, u} l E X 0

attribute [local instance 2000] completedCoproductTargetDerived

/-- The published category structure at the explicit coefficient sizes.
Source: Stacks 03DA (blueprint: lem-sf-completed-free-coproduct-reduction). -/
abbrev completedCoproductRestrictionLimits :
    PreservesFiniteLimits (scalarReductionRestriction.{u, u} l E X 0) :=
  scalarReductionRestrictionLimits.{u, u} l E X 0

attribute [local instance 3000] completedCoproductRestrictionLimits

/-- The published category structure at the explicit coefficient sizes.
Source: Stacks 03DA (blueprint: lem-sf-completed-free-coproduct-reduction). -/
abbrev completedCoproductRestrictionColimits :
    PreservesFiniteColimits (scalarReductionRestriction.{u, u} l E X 0) :=
  scalarReductionRestrictionColimits.{u, u} l E X 0

attribute [local instance 3000] completedCoproductRestrictionColimits

attribute [local instance] scalarReductionExtensionAdditive

/-- The actual finite coproduct of completed coefficient units.
Source: Stacks 09C3 (blueprint: lem-sf-completed-free-coproduct-reduction). -/
abbrev completedCoproductIntegralFree (r : ℕ) : scalarReductionSource.{u, u} l E X :=
  @SheafOfModules.free X.ProEt inferInstance (ProEt.topology X)
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
    (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
    (integralCoefficientAbLocallyBijective.{u, u} X)
    (ULift.{u + 1} (Fin r))

/-- The actual finite coproduct of residue coefficient units.
Source: Stacks 09C3 (blueprint: lem-sf-completed-free-coproduct-reduction). -/
abbrev completedCoproductResidueFree (r : ℕ) : scalarReductionTarget.{u, u} l E X 0 :=
  @SheafOfModules.free X.ProEt inferInstance (ProEt.topology X)
    (integralCoefficientSheaf.{u, u} l E X 0)
    (inferInstanceAs (HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}))
    (integralCoefficientAbLocallyBijective.{u, u} X)
    (ULift.{u + 1} (Fin r))

private def topCellFreeProductIso (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (n : ℕ) : SheafOfModules.free (R := R) (ULift.{u + 1} (Fin n)) ≅
      ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit R := by
  let : HasFiniteBiproducts (SheafOfModules.{u + 1} R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact Sigma.reindex Equiv.ulift (fun _ : Fin n ↦ SheafOfModules.unit R) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin n ↦ SheafOfModules.unit R)).symm ≪≫
    biproduct.isoProduct (fun _ : Fin n ↦ SheafOfModules.unit R)

private theorem topCell_ordinary_free_reduction (r : ℕ)
    (q : (completedCoproductIntegralFree l E X r) ⟶
      (scalarReductionRestriction.{u, u} l E X 0).obj
      (completedCoproductResidueFree l E X r))
    (hq : ∀ i : ULift.{u + 1} (Fin r), SheafOfModules.ιFree i ≫ q =
      CompletedCoefficientFree.quotientProjection.{u, u} l E X 0 ≫
        (scalarReductionRestriction.{u, u} l E X 0).map (SheafOfModules.ιFree i)) :
    ∃ e : (scalarReductionExtension.{u, u} l E X 0).obj
        (completedCoproductIntegralFree l E X r) ≅
        (completedCoproductResidueFree l E X r),
      (scalarReductionExtension_adjunction.{u, u} l E X 0).choose.unit.app _ ≫
        (scalarReductionRestriction.{u, u} l E X 0).map e.hom =
          q := by
  let F := scalarReductionExtension.{u, u} l E X 0
  let R := scalarReductionRestriction.{u, u} l E X 0
  let adj := (scalarReductionExtension_adjunction.{u, u} l E X 0).choose
  let : F.IsLeftAdjoint := ⟨R, ⟨adj⟩⟩
  let e₁ := (extensionUnit_normalized.{u, u} l E X 0).choose
  have he₁ := (extensionUnit_normalized.{u, u} l E X 0).choose_spec
  let e := PreservesCoproduct.iso F
    (fun _ : ULift.{u + 1} (Fin r) ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)) ≪≫
        Sigma.mapIso (fun _ : ULift.{u + 1} (Fin r) ↦ e₁)
  refine ⟨e, ?_⟩
  apply Sigma.hom_ext
  intro i
  let j := SheafOfModules.ιFree
    (R := completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) i
  have hn := adj.unit.naturality j
  change j ≫ adj.unit.app _ = adj.unit.app _ ≫ R.map (F.map j) at hn
  change j ≫ (adj.unit.app _ ≫ R.map e.hom) = _
  rw [← Category.assoc, hn, Category.assoc, ← R.map_comp]
  have hpre : F.map j ≫ (PreservesCoproduct.iso F
      (fun _ : ULift.{u + 1} (Fin r) ↦
        SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X))).hom =
      Sigma.ι (fun _ : ULift.{u + 1} (Fin r) ↦ F.obj
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X))) i := by
    dsimp only [PreservesCoproduct.iso]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit F
        (fun _ : ULift.{u + 1} (Fin r) ↦ SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)))
      (coproductIsCoproduct (fun _ : ULift.{u + 1} (Fin r) ↦ F.obj
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)))) (Discrete.mk i)
  have he : F.map j ≫ e.hom = e₁.hom ≫ SheafOfModules.ιFree i := by
    simp only [e, Iso.trans_hom, ← Category.assoc, hpre, Sigma.ι_mapIso_hom]
    rfl
  rw [he]
  rw [R.map_comp, ← Category.assoc]
  erw [he₁]
  exact (hq i).symm

private theorem topCell_quotient_epi (r : ℕ)
    (q : (completedCoproductIntegralFree l E X r) ⟶
      (scalarReductionRestriction.{u, u} l E X 0).obj
      (completedCoproductResidueFree l E X r))
    (hq : ∀ i : ULift.{u + 1} (Fin r), SheafOfModules.ιFree i ≫ q =
      CompletedCoefficientFree.quotientProjection.{u, u} l E X 0 ≫
        (scalarReductionRestriction.{u, u} l E X 0).map (SheafOfModules.ιFree i)) : Epi (q) := by
  let R := scalarReductionRestriction.{u, u} l E X 0
  let p := CompletedCoefficientFree.quotientProjection.{u, u} l E X 0
  let Y := SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E X 0)
  have : Epi p := (CompletedCoefficientFree.coefficient_shortExact.{u, u} l E X 0).epi_g
  let : ∀ _ : ULift.{u + 1} (Fin r), Epi p := fun _ ↦ inferInstance
  have heq : q =
      Limits.Sigma.map (fun _ : ULift.{u + 1} (Fin r) ↦ p) ≫
        sigmaComparison R (fun _ : ULift.{u + 1} (Fin r) ↦ Y) := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_map_assoc]
    change _ = p ≫ (Sigma.ι (fun _ : ULift.{u + 1} (Fin r) ↦ R.obj Y) i ≫
      sigmaComparison R (fun _ : ULift.{u + 1} (Fin r) ↦ Y))
    rw [ι_comp_sigmaComparison]
    exact hq i
  rw [heq]
  infer_instance

private theorem topCell_free_good (r : ℕ) (b : ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
      ((CochainComplex.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (completedCoproductIntegralFree l E X r)) := by
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E X
  let A := scalarReductionSource.{u, u} l E X
  let P := (CochainComplex.singleFunctor A b).obj
    (completedCoproductIntegralFree l E X r)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := SheafOfModules.tensorPreadditive R
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft M)
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  let : HasColimitsOfSize.{0, 0} A := inferInstance
  have : ∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂ := by
    intro X₁ X₂ j
    infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  have hunit : ObjectProperty.flat (show A from SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)) :=
    ObjectProperty.prop_unit ObjectProperty.flat
  have hprod : ObjectProperty.flat (show A from ∏ᶜ fun _ : Fin r ↦
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)) :=
    ObjectProperty.prop_of_isLimit _ (productIsProduct _) (fun _ ↦ hunit)
  have hfree : ObjectProperty.flat (show A from
      (completedCoproductIntegralFree l E X r)) :=
    ObjectProperty.prop_of_iso _
      (topCellFreeProductIso X
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) r).symm hprod
  have hs (i : ℤ) : ObjectProperty.flat (P.X i) := by
    by_cases hi : i = b
    · subst i
      exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.singleObjXSelf (.up ℤ) b _).symm hfree
    · exact ObjectProperty.prop_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) b _ i hi)
  have hsite (i : ℤ) : SheafOfModules.IsFlatOnSite
      (J := ProEt.topology X) (R := R) (P.X i) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm (hs i).2
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (R := R) P b hsite

/-- Generator-normalized coefficient reduction on an actual finite free coproduct
is epic, and its adjoint-normalized derived single-cell comparison is invertible.
Source: Stacks 09C3, top-generator lift, and 06YY, bounded-above flat complexes.
Scalar extension preserves the free coproduct; on each generator its unit is the
coefficient projection. The projection is epic, and restriction preserves these
coproducts. Finite free modules are flat, so their single complexes are K-flat.
The derived counit is consequently invertible. Uniqueness under the derived
adjunction identifies this isomorphism with the stipulated comparison.
This includes rank zero and requires no projectivity or completeness hypothesis.
(blueprint: lem-sf-completed-free-coproduct-reduction). -/
theorem completed_free_coproduct_reduction (r : ℕ)
    (q : (completedCoproductIntegralFree l E X r) ⟶
      (scalarReductionRestriction.{u, u} l E X 0).obj
      (completedCoproductResidueFree l E X r))
    (hq : ∀ i : ULift.{u + 1} (Fin r), SheafOfModules.ιFree i ≫ q =
      CompletedCoefficientFree.quotientProjection.{u, u} l E X 0 ≫
        (scalarReductionRestriction.{u, u} l E X 0).map (SheafOfModules.ιFree i)) (b : ℤ)
    (cmp : (scalarReductionDerivedExtension.{u, u} l E X 0).obj
      ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (completedCoproductIntegralFree l E X r)) ⟶
      (DerivedCategory.singleFunctor (scalarReductionTarget.{u, u} l E X 0) b).obj
        (completedCoproductResidueFree l E X r))
    (hcmp : (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X 0).choose.unit.app
      ((DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
        (completedCoproductIntegralFree l E X r)) ≫
      (scalarReductionRestriction.{u, u} l E X 0).mapDerivedCategory.map cmp =
      (DerivedCategory.singleFunctor (scalarReductionSource.{u, u} l E X) b).map q ≫
        ((scalarReductionRestriction.{u, u} l E X 0).mapDerivedCategorySingleFunctor b).inv.app
          (completedCoproductResidueFree l E X r)) :
    IsIso cmp ∧ Epi q := by
  let F := scalarReductionExtension.{u, u} l E X 0
  let : F.Additive := scalarReductionExtensionAdditive.{u, u} l E X 0
  let R := scalarReductionRestriction.{u, u} l E X 0
  let P := (CochainComplex.singleFunctor (scalarReductionSource.{u, u} l E X) b).obj
    (completedCoproductIntegralFree l E X r)
  let c := CompletedCoefficientFree.reductionComplexCounit.{u, u} l E X 0 P
  have : IsIso c := CompletedCoefficientFree.reductionComplexCounit_isIso.{u, u}
    l E X 0 P (topCell_free_good l E X r b)
  obtain ⟨e₀, he₀⟩ := topCell_ordinary_free_reduction l E X r q hq
  let eC := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) b).app
    (completedCoproductIntegralFree l E X r) ≪≫ (CochainComplex.singleFunctor _ b).mapIso e₀
  let e := asIso c ≪≫ DerivedCategory.Q.mapIso eC
  have hc := CompletedCoefficientFree.reductionMap_complex.{u, u} l E X 0 P
    (topCell_free_good l E X r b)
  have he := CompleteLiftedTopCell.derived_single_normalization F R
    (scalarReductionExtension_adjunction.{u, u} l E X 0).choose.unit
    (completedCoproductIntegralFree l E X r) _ e₀ (q) he₀ b _
    (asIso c) (CompletedCoefficientFree.reductionMap.{u, u} l E X 0 _) hc
  have heq : cmp = e.hom := by
    apply ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E X 0).choose.homEquiv
      _ _).injective
    exact hcmp.trans he.symm
  refine ⟨?_, topCell_quotient_epi l E X r q hq⟩
  rw [heq]
  infer_instance

end WeilConjectures
