/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.AlgebraicGeometry.IntegralReductionTransitionSemilinear
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import all WeilConjectures.CategoryTheory.InjectiveTowerRoos.InjectiveTowerRoosShifts
import WeilConjectures.CategoryTheory.Derived.DerivedInjectiveResolutionNaturality
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
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
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.CategoryTheory.Flat.FlatRoosFunctorDescent
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

import all WeilConjectures.SecSmoothPurity.StrictCoefficient.ScalarCalculation.NormalizedScalarTensorTransitionsSupplement
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined

/-! # Well-definedness of integral pullback and completed tensor product

Source: Stacks Project, Tags 06YS, 06YT, 0G7E and 08TC; Bhatt--Scholze,
Definition 3.4.10 and Lemma 6.5.9(4)
(blueprint: lem-pur-integral-operations-well-defined).

The natural-number level n denotes exponent n+1. All towers and their maps are
constructed before localization; the Roos complex uses termwise products and the
specified shifted cone. The final descent includes its natural comparison data.

## Main definitions

* `integralOperationsPullbackComplexFunctor`: strict finite pullback followed by Roos.
* `integralOperationsTensorComplexFunctor`: direct-sum finite tensor followed by Roos.

## Main statements

* `integralOperationsWellDefined`: quasi-isomorphism invariance and normalized descent.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 512

universe t u a b c d r a' b' c' d'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

-- Prefer the module's recorded tensor instances during private proof search.
attribute [-instance] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLocalizationIsMonoidal
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits

-- These proof imports carry broad diagram instances; prefer the concrete instances here.
attribute [local instance 1] CategoryTheory.CochainPullback.RingedPullback.additive
  CategoryTheory.CochainPullback.CoefficientSquare.additive'
  CategoryTheory.CochainPullback.StrictCoefficient.Diagram.additive
  CategoryTheory.CochainPullback.extensionFunctorAdditive

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe wForget uForget vForget

open WeilConjectures

attribute [local instance 2000] SheafOfModules.integralOperationsRestrictScalarsZero

private theorem constantMap_surjective
    {C : Type c} [Category.{d} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
    {A B : CommRingCat.{r}} (q : A ⟶ B) (hq : Function.Surjective q) :
    Presheaf.IsLocallySurjective J ((constantSheaf J CommRingCat.{r}).map q).hom := by
  let k := (Functor.const Cᵒᵖ).map q
  have : Presheaf.IsLocallySurjective J k :=
    Presheaf.isLocallySurjective_of_surjective J k (fun _ ↦ hq)
  have h := (sheafificationAdjunction J CommRingCat.{r}).unit.naturality k
  apply Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (f₁ := toSheafify J ((Functor.const Cᵒᵖ).obj A))
    (f₃ := k ≫ toSheafify J ((Functor.const Cᵒᵖ).obj B))
  exact h.symm

namespace AlgebraicGeometry.Scheme
attribute [local irreducible] coefficientProEtaleDirectRingMap
private theorem directRingMap_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max r (t + 1)}} (q : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).map q ≫
        coefficientProEtaleDirectRingMap.{t, r} f B =
      coefficientProEtaleDirectRingMap.{t,r} f A ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max r (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).map q) := by
  apply ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max r (t + 1)}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max r (t + 1)}).homEquiv _ _
    ((presheafToSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).map
      ((Functor.const _).map q) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  unfold coefficientProEtaleDirectRingMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  exact congrArg (fun z ↦ z.app ((proEtaleBaseChange f).op.obj V))
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{max r (t + 1)}).unit.naturality
      ((Functor.const _).map q))
end AlgebraicGeometry.Scheme

attribute [local irreducible] constantSheaf HasDerivedCategory.standard limit

namespace SheafOfModules.IntegralScalarProof
variable {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  {S T : Sheaf J RingCat.{r}} (q : S ⟶ T)
  (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T)

private noncomputable def retypeMap
    (φ : (toSheaf S).obj M ⟶ (toSheaf T).obj N)
    (hφ : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      φ.hom.app U (s • x) = q.hom.app U s •
        (show N.val.obj U from φ.hom.app U x)) :
    M ⟶ (restrictScalars q).obj N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := M.val.obj U) (Y := ((restrictScalars q).obj N).val.obj U)
        { toFun := φ.hom.app U
          map_add' := _root_.map_add _
          map_smul' := hφ U }
      naturality := by
        intro U V a
        ext x
        exact CategoryTheory.congr_fun (φ.hom.naturality a) x }

section Composition

variable {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T)
  (hq : f ≫ q = g) (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T)
include hq in
private theorem coefficient_comp (U : Cᵒᵖ) (s : R.obj.obj U) :
    q.hom.app U (f.hom.app U s) = g.hom.app U s :=
  ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) hq) s
private noncomputable def restrictMap (φ : M ⟶ (restrictScalars q).obj N) :
    (restrictScalars f).obj M ⟶ (restrictScalars g).obj N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((restrictScalars f).obj M).val.obj U)
        (Y := ((restrictScalars g).obj N).val.obj U)
        { toFun := φ.val.app U
          map_add' := _root_.map_add _
          map_smul' := fun s x ↦ by
            change φ.val.app U (f.hom.app U s • (show M.val.obj U from x)) =
              g.hom.app U s • (show N.val.obj U from φ.val.app U x)
            have h := (φ.val.app U).hom.map_smul (f.hom.app U s) (show M.val.obj U from x)
            change φ.val.app U (f.hom.app U s • (show M.val.obj U from x)) =
              q.hom.app U (f.hom.app U s) • (show N.val.obj U from φ.val.app U x) at h
            rw [coefficient_comp f g q hq] at h
            exact h }
      naturality := by
        intro U V a
        ext x
        exact PresheafOfModules.naturality_apply φ.val a x }
private noncomputable def liftMap [Presheaf.IsLocallySurjective J f.hom]
    (φ : (restrictScalars f).obj M ⟶ (restrictScalars g).obj N) :
    M ⟶ (restrictScalars q).obj N := by
  let φ' : (restrictScalars f).obj M ⟶
      (restrictScalars f).obj ((restrictScalars q).obj N) :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := ((restrictScalars f).obj M).val.obj U)
            (Y := ((restrictScalars f).obj ((restrictScalars q).obj N)).val.obj U)
            { toFun := φ.val.app U
              map_add' := _root_.map_add _
              map_smul' := fun s x ↦ by
                have h := (φ.val.app U).hom.map_smul s x
                change φ.val.app U (f.hom.app U s • (show M.val.obj U from x)) =
                  q.hom.app U (f.hom.app U s) •
                    (show N.val.obj U from φ.val.app U x)
                rw [coefficient_comp f g q hq]
                exact h }
          naturality := by
            intro U V a
            ext x
            exact PresheafOfModules.naturality_apply φ.val a x } }
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective f.hom N.isSheaf).symm
    φ'.val⟩
private theorem liftMap_apply [Presheaf.IsLocallySurjective J f.hom]
    (φ : (restrictScalars f).obj M ⟶ (restrictScalars g).obj N)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (liftMap f g q hq M N φ).val.app U x = φ.val.app U x := by
  rfl

private noncomputable def restrictComplexMap
    {P : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} T) ℤ}
    (φ : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q) :
    (WeilConjectures.integralOperationsRestrictionComplex f).obj P ⟶
      (WeilConjectures.integralOperationsRestrictionComplex g).obj Q where
  f j := restrictMap f g q hq (P.X j) (Q.X j) (φ.f j)
  comm' i j _ := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) (φ.comm i j)

private theorem restrictComplexMap_apply
    {P : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} T) ℤ}
    (φ : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q)
    (j : ℤ) (U : Cᵒᵖ) (x : (P.X j).val.obj U) :
    (integralOperationsComplexSectionApply (restrictComplexMap f g q hq φ) j U) x =
      (integralOperationsComplexSectionApply φ j U) x := by
  rfl

private theorem restrictComplexMap_naturality
    {P P' : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q Q' : CochainComplex (SheafOfModules.{r} T) ℤ}
    (a : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q)
    (b : P' ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q')
    (u : P ⟶ P') (v : Q ⟶ Q')
    (h : u ≫ b = a ≫ (WeilConjectures.integralOperationsRestrictionComplex q).map v) :
    (WeilConjectures.integralOperationsRestrictionComplex f).map u ≫
        restrictComplexMap f g q hq b =
      restrictComplexMap f g q hq a ≫
        (WeilConjectures.integralOperationsRestrictionComplex g).map v := by
  apply HomologicalComplex.hom_ext
  intro i
  ext U x
  exact congrArg (fun z ↦ (z.f i).val.app U x) h

end Composition

end SheafOfModules.IntegralScalarProof

namespace SheafOfModules.IntegralPullbackProof
variable {C : Type c} [Category.{d} C] {D : Type c'} [Category.{d'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {R₀ R₁ : Sheaf K RingCat.{r}} {S₀ S₁ : Sheaf J RingCat.{r}}
  (qR : R₀ ⟶ R₁) (qS : S₀ ⟶ S₁)
  (φ₀ : S₀ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₀)
  (φ₁ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₁)
  (h : qS ≫ φ₁ = φ₀ ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map qR)
private noncomputable def pushRestrictionIso :
    restrictScalars.{r} qR ⋙ pushforward φ₀ ≅
      pushforward φ₁ ⋙ restrictScalars qS :=
  pushforwardComp (G := 𝟭 D) φ₀ qR ≪≫ pushforwardCongr h.symm ≪≫
    (pushforwardComp (F := 𝟭 C) qS φ₁).symm
private theorem pushRestrictionIso_apply (N : SheafOfModules.{r} R₁)
    (U : Cᵒᵖ) (x : N.val.obj (F.op.obj U)) :
    (integralOperationsSectionApply ((pushRestrictionIso F qR qS φ₀ φ₁ h).inv.app N) U) x = x := by
  rfl
end SheafOfModules.IntegralPullbackProof

namespace IntegralMateProof
variable {A : Type a} [Category.{a'} A] {B : Type b} [Category.{b'} B]
  {C : Type c} [Category.{c'} C] {D : Type d} [Category.{d'} D]
  {L : A ⥤ B} {G : B ⥤ A} {L' : C ⥤ D} {G' : D ⥤ C}
  (adj : L ⊣ G) (adj' : L' ⊣ G') (U : C ⥤ A) (V : D ⥤ B)
  (e : V ⋙ G ≅ G' ⋙ U)
private def mate {M : A} {N : C} (f : M ⟶ U.obj N) : L.obj M ⟶ V.obj (L'.obj N) :=
  (adj.homEquiv _ _).symm (f ≫ U.map (adj'.unit.app N) ≫ e.inv.app (L'.obj N))
private theorem mate_unit {M : A} {N : C} (f : M ⟶ U.obj N) :
    adj.unit.app M ≫ G.map (mate adj adj' U V e f) =
      f ≫ U.map (adj'.unit.app N) ≫ e.inv.app (L'.obj N) := by
  exact (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)
private theorem mate_naturality {M₀ M₁ : A} {N₀ N₁ : C}
    (f₀ : M₀ ⟶ U.obj N₀) (f₁ : M₁ ⟶ U.obj N₁)
    (a : M₀ ⟶ M₁) (b : N₀ ⟶ N₁) (h : a ≫ f₁ = f₀ ≫ U.map b) :
    L.map a ≫ mate adj adj' U V e f₁ =
      mate adj adj' U V e f₀ ≫ V.map (L'.map b) := by
  apply adj.homEquiv_naturality_right_square
  have hu : b ≫ adj'.unit.app N₁ = adj'.unit.app N₀ ≫ G'.map (L'.map b) :=
    adj'.unit.naturality b
  have he : e.inv.app (L'.obj N₀) ≫ G.map (V.map (L'.map b)) =
      U.map (G'.map (L'.map b)) ≫ e.inv.app (L'.obj N₁) :=
    (e.inv.naturality (L'.map b)).symm
  calc
    a ≫ (f₁ ≫ U.map (adj'.unit.app N₁) ≫ e.inv.app (L'.obj N₁)) =
        (a ≫ f₁) ≫ U.map (adj'.unit.app N₁) ≫ e.inv.app (L'.obj N₁) :=
      (Category.assoc a f₁ _).symm
    _ = (f₀ ≫ U.map b) ≫ U.map (adj'.unit.app N₁) ≫ e.inv.app (L'.obj N₁) :=
      congrArg (fun z ↦ z ≫ U.map (adj'.unit.app N₁) ≫ e.inv.app (L'.obj N₁)) h
    _ = f₀ ≫ U.map (b ≫ adj'.unit.app N₁) ≫ e.inv.app (L'.obj N₁) := by
      simp only [U.map_comp, Category.assoc]
    _ = f₀ ≫ U.map (adj'.unit.app N₀ ≫ G'.map (L'.map b)) ≫
        e.inv.app (L'.obj N₁) := congrArg
      (fun z ↦ f₀ ≫ U.map z ≫ e.inv.app (L'.obj N₁)) hu
    _ = (f₀ ≫ U.map (adj'.unit.app N₀) ≫ e.inv.app (L'.obj N₀)) ≫
        G.map (V.map (L'.map b)) := by
      simp only [U.map_comp, Category.assoc]
      rw [he]
end IntegralMateProof

namespace SheafOfModules.IntegralPullbackProof
variable {C : Type c} [Category.{d} C] {D : Type c'} [Category.{d'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {R₀ R₁ : Sheaf K RingCat.{r}} {S₀ S₁ : Sheaf J RingCat.{r}}
  (qR : R₀ ⟶ R₁) (qS : S₀ ⟶ S₁)
  (φ₀ : S₀ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₀)
  (φ₁ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R₁)
  (h : qS ≫ φ₁ = φ₀ ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map qR)
  {L₀ : SheafOfModules.{r} S₀ ⥤ SheafOfModules.{r} R₀}
  {L₁ : SheafOfModules.{r} S₁ ⥤ SheafOfModules.{r} R₁}
  (adj₀ : L₀ ⊣ pushforward φ₀) (adj₁ : L₁ ⊣ pushforward φ₁)

/-- A section of the pullback generated by the adjunction unit.
Source: Stacks Tag 03D2 (blueprint: lem-pur-integral-operations-well-defined). -/
private noncomputable def unitSection (M : SheafOfModules.{r} S₀) (U : Cᵒᵖ)
    (x : M.val.obj U) : (L₀.obj M).val.obj (F.op.obj U) :=
  ((adj₀.unit.app M).val.app U) x

private theorem mate_generator {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (integralOperationsSectionApply (IntegralMateProof.mate adj₀ adj₁ (restrictScalars qS)
      (restrictScalars qR)
      (pushRestrictionIso F qR qS φ₀ φ₁ h) a) (F.op.obj U))
        ((integralOperationsSectionApply (adj₀.unit.app M) U) x) =
      (integralOperationsSectionApply (adj₁.unit.app N) U) ((integralOperationsSectionApply a U)
        x) := by
  have he := congrArg (fun k ↦ k.val.app U x)
    (IntegralMateProof.mate_unit adj₀ adj₁ (restrictScalars qS) (restrictScalars qR)
      (pushRestrictionIso F qR qS φ₀ φ₁ h) a)
  exact he.trans (pushRestrictionIso_apply F qR qS φ₀ φ₁ h (L₁.obj N) U
    ((adj₁.unit.app N).val.app U (a.val.app U x)))
private noncomputable def mateData {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) :
    L₀.obj M ⟶ (restrictScalars qR).obj (L₁.obj N) :=
  IntegralMateProof.mate adj₀ adj₁ (restrictScalars qS) (restrictScalars qR)
    (pushRestrictionIso F qR qS φ₀ φ₁ h) a

private theorem mateData_unit_formula
    {M : SheafOfModules.{r} S₀} {N : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (integralOperationsSectionApply (mateData F qR qS φ₀ φ₁ h adj₀ adj₁ a) (F.op.obj U))
        (unitSection F φ₀ adj₀ M U x) =
      unitSection F φ₁ adj₁ N U ((integralOperationsSectionApply a U) x) := by
  exact mate_generator F qR qS φ₀ φ₁ h adj₀ adj₁ a U x

private theorem mateData_naturality
    {M M' : SheafOfModules.{r} S₀} {N N' : SheafOfModules.{r} S₁}
    (a : M ⟶ (restrictScalars qS).obj N) (b : M' ⟶ (restrictScalars qS).obj N')
    (u : M ⟶ M') (v : N ⟶ N') (hab : u ≫ b = a ≫ (restrictScalars qS).map v) :
    L₀.map u ≫ (mateData F qR qS φ₀ φ₁ h adj₀ adj₁ b) =
      (mateData F qR qS φ₀ φ₁ h adj₀ adj₁ a) ≫ (restrictScalars qR).map (L₁.map v) :=
  IntegralMateProof.mate_naturality adj₀ adj₁ (restrictScalars qS) (restrictScalars qR)
    (pushRestrictionIso F qR qS φ₀ φ₁ h) a b u v hab

private theorem restricted_hom_ext
    {R : Sheaf K RingCat.{r}} (π₀ : R ⟶ R₀) (π₁ : R ⟶ R₁)
    (hπ : π₀ ≫ qR = π₁) [Presheaf.IsLocallySurjective K π₀.hom]
    (M : SheafOfModules.{r} S₀) (N : SheafOfModules.{r} R₁)
    (a b : (restrictScalars π₀).obj (L₀.obj M) ⟶ (restrictScalars π₁).obj N)
    (hab : ∀ (U : Cᵒᵖ) (x : M.val.obj U),
      (integralOperationsSectionApply a (F.op.obj U)) (unitSection F φ₀ adj₀ M U x) =
        (integralOperationsSectionApply b (F.op.obj U)) (unitSection F φ₀ adj₀ M U x)) : a = b := by
  let lift := IntegralScalarProof.liftMap π₀ π₁ qR hπ (L₀.obj M) N
  have he : lift a = lift b := by
    apply (adj₀.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext U x
    exact hab U x
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) he

end SheafOfModules.IntegralPullbackProof

attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  SheafOfModules.IntegralPullbackProof.mateData
  SheafOfModules.IntegralPullbackProof.pushRestrictionIso
  IntegralMateProof.mate

private theorem integralHasMap
    {A : Type a} [Category.{b} A] [Preadditive A] [MonoidalCategory A]
    [(MonoidalCategory.curriedTensor A).PreservesZeroMorphisms]
    [∀ M : A, ((MonoidalCategory.curriedTensor A).obj M).PreservesZeroMorphisms]
    [HasCountableCoproducts A] (P Q : CochainComplex A ℤ) :
    HomologicalComplex.HasMapBifunctor P Q
      (MonoidalCategory.curriedTensor A) (.up ℤ) := by
  infer_instance

private theorem scalarRestrictionAdditive
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) :
    (SheafOfModules.restrictScalars.{r} α).Additive := by
  infer_instance

namespace WeilConjectures

section PrivateTensorTransition
attribute [local semireducible] constantSheaf HasDerivedCategory.standard limit
  SheafOfModules.tensorObjIsoSheafification
attribute [-instance] SheafOfModules.integralOperationsRestrictScalarsZero
set_option backward.isDefEq.respectTransparency true
attribute [local instance 2001] scalarRestrictionAdditive
attribute [local instance] CategoryTheory.CochainPullback.RingedPullback.additive
  CategoryTheory.CochainPullback.CoefficientSquare.additive'
  CategoryTheory.CochainPullback.StrictCoefficient.Diagram.additive
  CategoryTheory.CochainPullback.extensionFunctorAdditive
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 2001] integralHasMap
attribute [local instance 3001]
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.tensorCoproducts
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.hasTensorTotal

universe v u' v'

namespace TensorTotalProof
open MonoidalCategory
variable {C : Type a} [Category.{b} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).PreservesZeroMorphisms]
  [∀ X : C, ((curriedTensor C).obj X).PreservesZeroMorphisms]
  {P Q A B : CochainComplex C ℤ}
private theorem totalTensor_map
    (a : P ⟶ A) (b : Q ⟶ B)
    [∀ (K L : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)] :
    (Functor.uncurry.obj (curriedTensor C).map₂CochainComplex).map
      (X := (P, Q)) (Y := (A, B)) (a, b) =
      HomologicalComplex.mapBifunctorMap a b (curriedTensor C) (.up ℤ) := by
  change HomologicalComplex.mapBifunctorMap a (𝟙 Q) _ _ ≫
    HomologicalComplex.mapBifunctorMap (𝟙 A) b _ _ = _
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

private theorem composite_map
    {D : Type a'} [Category.{b'} D] {B : Type c} [Category.{d} B]
    [HasZeroMorphisms B] (F : D ⥤ CochainComplex C ℤ) (R : C ⥤ B)
    [R.PreservesZeroMorphisms]
    [∀ (K L : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)]
    {K L : D × D} (u : K ⟶ L) :
    (integralOperationsTensorComposite F R).map u =
      (R.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (F.map u.1) (F.map u.2)
          (curriedTensor C) (.up ℤ)) := by
  exact congrArg (R.mapHomologicalComplex (.up ℤ)).map
    (totalTensor_map (F.map u.1) (F.map u.2))

end TensorTotalProof

section SignedTensorConstruction

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction

open MonoidalCategory

variable (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)

section GenericTensor

set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] SheafOfModules.monoidalCategory

@[no_expose] private noncomputable def pureTensor
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
    (R : Sheaf J CommRingCat.{r})
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    (M N : SheafOfModules.{r} ((integralOperationsForgetSheaf.{r} J).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv.val.app U
    ((toSheafify J (M.val ⊗ N.val).presheaf).app U (x ⊗ₜ[R.obj.obj U] y))

/-- The common pure section is the image of the sheafification unit.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product). -/
private theorem moduleTmul_eq
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
    (R : Sheaf J CommRingCat.{r})
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    (M N : SheafOfModules.{r} ((integralOperationsForgetSheaf.{r} J).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    CochainPullback.moduleTmul (R := R) M N U x y =
    pureTensor R M N U x y := by
  exact congrArg (fun f ↦
    (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv.val.app U
      (f.app U (x ⊗ₜ[R.obj.obj U] y)))
    (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (R := (integralOperationsForgetSheaf.{r} J).obj R)
      (𝟙 _) (M.val ⊗ N.val))

/-- Maps from the sheaf tensor are determined by the common local pure sections.
Source: Stacks 03EK (blueprint: def-pur-sheaf-tensor-product). -/
private theorem moduleTmul_hom_ext
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
    (R : Sheaf J CommRingCat.{r})
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    (M N Z : SheafOfModules.{r} ((integralOperationsForgetSheaf.{r} J).obj R))
    (φ ψ : M ⊗ N ⟶ Z)
    (h : ∀ U (x : M.val.obj U) (y : N.val.obj U),
      (integralOperationsSectionApply φ U) (pureTensor R M N U x y) =
      (integralOperationsSectionApply ψ U) (pureTensor R M N U x y)) : φ = ψ := by
  apply CochainPullback.StrictCoefficient.ScalarCalculation.tensor_hom_ext M N Z
  intro U x y
  change φ.val.app U (CochainPullback.moduleTmul (R := R) M N U x y) =
    ψ.val.app U (CochainPullback.moduleTmul (R := R) M N U x y)
  simpa only [moduleTmul_eq] using h U x y

-- Explicit section maps avoid comparing the two coefficient-ring constructions in coercions.
private def forgetRestriction
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S)
    (M : SheafOfModules.{r} S) (U : Cᵒᵖ) :
    ((SheafOfModules.restrictScalars α).obj M).val.obj U → M.val.obj U := id

private def intoRestriction
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S)
    (M : SheafOfModules.{r} S) (U : Cᵒᵖ) :
    M.val.obj U → ((SheafOfModules.restrictScalars α).obj M).val.obj U := id

private theorem forgetRestriction_injective
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S)
    (M : SheafOfModules.{r} S) (U : Cᵒᵖ) :
    Function.Injective (forgetRestriction α M U) := fun _ _ h ↦ h

private theorem liftMap_section
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T)
    (hq : f ≫ q = g) [Presheaf.IsLocallySurjective J f.hom]
    (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T)
    (φ : (SheafOfModules.restrictScalars f).obj M ⟶
      (SheafOfModules.restrictScalars g).obj N) (U : Cᵒᵖ) (x : M.val.obj U) :
    forgetRestriction q N U
      ((integralOperationsSectionApply (SheafOfModules.IntegralScalarProof.liftMap f g q hq M N
        φ) U) x) =
      forgetRestriction g N U ((integralOperationsSectionApply φ U) (intoRestriction f M U x)) := by
  exact rfl

private theorem liftMap_injective
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T)
    (hq : f ≫ q = g) [Presheaf.IsLocallySurjective J f.hom]
    (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T) :
    Function.Injective (SheafOfModules.IntegralScalarProof.liftMap f g q hq M N) := by
  intro φ ψ h
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) h

private theorem restrictComplexMap_section
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T)
    (hq : f ≫ q = g) {P : CochainComplex (SheafOfModules.{r} S) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} T) ℤ}
    (φ : P ⟶ (WeilConjectures.integralOperationsRestrictionComplex q).obj Q)
    (j : ℤ) (U : Cᵒᵖ) (x : (P.X j).val.obj U) :
    forgetRestriction g (Q.X j) U
      ((integralOperationsComplexSectionApply
        (SheafOfModules.IntegralScalarProof.restrictComplexMap f g q hq φ) j U)
        (intoRestriction f (P.X j) U x)) =
      forgetRestriction q (Q.X j) U ((integralOperationsComplexSectionApply φ j U) x) := by
  rfl

end GenericTensor

attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

namespace TensorChainProof
open CategoryTheory.CochainPullback
open CategoryTheory.CochainPullback.StrictCoefficient
open CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation
attribute [local instance 2000] SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive
  SheafOfModules.cochainTensorLeftPreservesColimits
  SheafOfModules.cochainTensorRightPreservesColimits
  SheafOfModules.cochainModulesMonoidal
  GrothendieckTopology.hasSheafify_of_essentiallySmall
variable {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
  (R S : Sheaf J CommRingCat.{r}) (α : R ⟶ S)

attribute [local instance] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory

private theorem totalMap_eq {A : Sheaf J CommRingCat.{r}}
    {P Q X Y : Complex A} (f : P ⟶ X) (g : Q ⟶ Y) :
    tensorTotalMap f g =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor (Modules A)) (.up ℤ) := rfl

@[no_expose] private noncomputable def chainAdjunction :=
  (extensionAdjunction α).mapHomologicalComplex (.up ℤ)

@[no_expose] private noncomputable def transpose {K : Complex R} {L : Complex S}
    (f : K ⟶ (restrictComplex α).obj L) : (extend α).obj K ⟶ L :=
  (chainAdjunction R S α).homEquiv K L |>.symm <| f

private theorem transpose_section {K : Complex R} {L : Complex S}
    (f : K ⟶ (restrictComplex α).obj L) (p : ℤ) (U : Cᵒᵖ) (x : (K.X p).val.obj U) :
    ((transpose R S α f).f p).val.app U
      (extensionTmul α (K.X p) U 1 x) = (f.f p).val.app U x := by
  have h := congrArg (fun z ↦ (z.f p).val.app U x)
    ((chainAdjunction R S α).homEquiv K L
      |>.apply_symm_apply f)
  rw [Adjunction.homEquiv_unit] at h
  change ((transpose R S α f).f p).val.app U
    (((extensionAdjunction α).unit.app (K.X p)).val.app U x) = _ at h
  rw [KappaCalculation.extension_unit] at h
  exact h

@[no_expose] private noncomputable def map
    {P Q : CochainPullback.Complex R} {P' Q' : CochainPullback.Complex S}
    (a : P ⟶ (restrictComplex α).obj P')
    (b : Q ⟶ (restrictComplex α).obj Q') :
    total P Q ⟶ (restrictComplex α).obj (total P' Q') :=
  (chainAdjunction R S α).unit.app (total P Q) ≫
    (restrictComplex α).map
      ((tensorComparison (extensionPullback α) (extensionComparison α) P Q).hom ≫
        tensorTotalMap (transpose R S α a) (transpose R S α b))

private theorem totalPure_eq {P Q : CochainPullback.Complex R}
    (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    totalPure P Q p q (p+q) rfl U x y =
      (integralOperationsSectionApply (tensorι (A := R) P Q p q (p+q) rfl) U)
        (pureTensor R (P.X p) (Q.X q) U x y)  := by
  exact congrArg (integralOperationsSectionApply
    (tensorι (A := R) P Q p q (p + q) rfl) U)
    (moduleTmul_eq R (P.X p) (Q.X q) U x y)

private theorem pure
    {P Q : CochainPullback.Complex R} {P' Q' : CochainPullback.Complex S}
    (a : P ⟶ (restrictComplex α).obj P')
    (b : Q ⟶ (restrictComplex α).obj Q') (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
    (y : (Q.X q).val.obj U) :
    ((map R S α a b).f (p+q)).val.app U
      (totalPure P Q p q (p+q) rfl U x y) =
    totalPure P' Q' p q (p+q) rfl U
      ((a.f p).val.app U x) ((b.f q).val.app U y) := by
  change ((tensorTotalMap (transpose R S α a) (transpose R S α b)).f (p+q)).val.app U
    (((tensorComparison (extensionPullback α) (extensionComparison α) P Q).hom.f
      (p+q)).val.app U
      (((extensionAdjunction α).unit.app ((total P Q).X (p+q))).val.app U
        (totalPure P Q p q (p+q) rfl U x y))) = _
  rw [KappaCalculation.extension_unit, scalarTotal_hom, totalMap_pure,
    transpose_section, transpose_section]
attribute [local irreducible] map transpose
private theorem map_naturality
    {P Q X Y : Complex R} {P' Q' X' Y' : Complex S}
    (a : P ⟶ (restrictComplex α).obj P')
    (b : Q ⟶ (restrictComplex α).obj Q')
    (a' : X ⟶ (restrictComplex α).obj X')
    (b' : Y ⟶ (restrictComplex α).obj Y')
    (f : P ⟶ X) (g : Q ⟶ Y) (f' : P' ⟶ X') (g' : Q' ⟶ Y')
    (ha : f ≫ a' = a ≫ (restrictComplex α).map f')
    (hb : g ≫ b' = b ≫ (restrictComplex α).map g') :
    tensorTotalMap f g ≫ map R S α a' b' =
      map R S α a b ≫ (restrictComplex α).map (tensorTotalMap f' g') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply tensor_hom_ext
  intro U x y
  subst n
  change ((map R S α a' b').f (p+q)).val.app U
    (((tensorTotalMap f g).f (p+q)).val.app U
      (totalPure P Q p q (p+q) rfl U x y)) =
    ((tensorTotalMap f' g').f (p+q)).val.app U
      (((map R S α a b).f (p+q)).val.app U
        (totalPure P Q p q (p+q) rfl U x y))
  rw [totalMap_pure, pure, pure, totalMap_pure]
  exact congrArg₂ (totalPure X' Y' p q (p+q) rfl U)
    (congrArg (fun k ↦ (k.f p).val.app U x) ha)
    (congrArg (fun k ↦ (k.f q).val.app U y) hb)

end TensorChainProof

attribute [local irreducible] TensorChainProof.map TensorChainProof.transpose
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.tensorTotalMap
  CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation.totalPure

attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

open CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation in
private theorem genericRestrictedTotal_hom_ext
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {R₀ : Sheaf J RingCat.{r}} (S T : Sheaf J CommRingCat.{r})
    (f : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj S)
    (g : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj T)
    (q₀ : (integralOperationsForgetSheaf.{r} J).obj S ⟶
      (integralOperationsForgetSheaf.{r} J).obj T)
    (hq₀ : f ≫ q₀ = g) [Presheaf.IsLocallySurjective J f.hom]
    (P Q : CochainComplex (SheafOfModules.{r}
      ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ)
    (Z : SheafOfModules.{r}
      ((integralOperationsForgetSheaf.{r} J).obj T)) (j : ℤ)
    (a b : (SheafOfModules.restrictScalars
        f).obj
      ((CategoryTheory.CochainPullback.StrictCoefficient.total P Q).X j) ⟶
        (SheafOfModules.restrictScalars g).obj Z)
    (h : ∀ (p q : ℤ) (hpq : p + q = j) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      forgetRestriction g Z U
        ((integralOperationsSectionApply a U) (intoRestriction f
          ((CategoryTheory.CochainPullback.StrictCoefficient.total P Q).X j) U
            ((integralOperationsSectionApply (tensorι (A := S) P Q
              p q j hpq) U)
              (pureTensor S _ _ U x y)))) =
      forgetRestriction g Z U
        ((integralOperationsSectionApply b U) (intoRestriction f
          ((CategoryTheory.CochainPullback.StrictCoefficient.total P Q).X j) U
            ((integralOperationsSectionApply (tensorι (A := S) P Q
              p q j hpq) U)
              (pureTensor S _ _ U x y))))) : a = b := by
  let lift := SheafOfModules.IntegralScalarProof.liftMap
    f g
    q₀ hq₀
    ((CategoryTheory.CochainPullback.StrictCoefficient.total P Q).X j) Z
  have he : lift a = lift b := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply moduleTmul_hom_ext S
    intro U x y
    apply forgetRestriction_injective q₀ Z U
    change forgetRestriction q₀ Z U
      ((lift a).val.app U _) =
      forgetRestriction q₀ Z U
        ((lift b).val.app U _)
    exact (liftMap_section f
      g _ hq₀ _ _ a U _).trans
      ((h p q hpq U x y).trans
        (liftMap_section f
          g _ hq₀
          _ _ b U _).symm)
  exact liftMap_injective f
    g _ hq₀ _ _ he

namespace TensorNaturalProof
open CategoryTheory.CochainPullback
open CategoryTheory.CochainPullback.StrictCoefficient
open CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation
open MonoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.monoidalPreadditive_independent
variable {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {D : Type c} [Category.{d} D]
  {R₀ : Sheaf J RingCat.{r}} (S T : Sheaf J CommRingCat.{r})
  (f : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj S)
  (g : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj T)
  (q₀ : S ⟶ T)
  (hq₀ : f ≫ ((integralOperationsForgetSheaf J).map q₀) = g)
  (F : D ⥤ CochainComplex (SheafOfModules.{r}
    ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ)
  (G : D ⥤ CochainComplex (SheafOfModules.{r}
    ((integralOperationsForgetSheaf.{r} J).obj T)) ℤ)
  (θ : F ⟶ G ⋙ integralOperationsRestrictionComplex ((integralOperationsForgetSheaf J).map q₀))

@[no_expose] private noncomputable abbrev level
    (f : R₀ ⟶ (integralOperationsForgetSheaf.{r} J).obj S)
    (F : D ⥤ CochainComplex (SheafOfModules.{r}
      ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ) :
    D × D ⥤ CochainComplex (SheafOfModules.{r} R₀) ℤ :=
  integralOperationsTensorComposite F (SheafOfModules.restrictScalars f)

@[no_expose] private noncomputable def sectionPure
    (F : D ⥤ CochainComplex (SheafOfModules.{r}
      ((integralOperationsForgetSheaf.{r} J).obj S)) ℤ)
    (P Q : D) (p q : ℤ) (U : Cᵒᵖ)
    (x : ((F.obj P).X p).val.obj U) (y : ((F.obj Q).X q).val.obj U) :
    ((total (F.obj P) (F.obj Q)).X (p + q)).val.obj U :=
  (integralOperationsSectionApply
    (tensorι (A := S) (F.obj P) (F.obj Q) p q (p+q) rfl) U)
    (pureTensor S _ _ U x y)

@[no_expose] private noncomputable def component (K : D × D) :
    (level S f F).obj K ⟶
      (level T g G).obj K :=
  SheafOfModules.IntegralScalarProof.restrictComplexMap f g ((integralOperationsForgetSheaf
    J).map q₀) hq₀
    (TensorChainProof.map S T q₀ (θ.app K.1) (θ.app K.2))

private theorem component_pure (P Q : D) (p q : ℤ) (U : Cᵒᵖ)
    (x : ((F.obj P).X p).val.obj U) (y : ((F.obj Q).X q).val.obj U) :
    (integralOperationsComplexSectionApply (component S T f g q₀ hq₀ F G θ (P,Q)) (p+q) U)
        (intoRestriction f _ U (sectionPure S F P Q p q U x y)) =
      intoRestriction g _ U (sectionPure T G P Q p q U
        (forgetRestriction ((integralOperationsForgetSheaf J).map q₀) _ U
          ((integralOperationsComplexSectionApply (θ.app
          P) p U) x))
        (forgetRestriction ((integralOperationsForgetSheaf J).map q₀) _ U
          ((integralOperationsComplexSectionApply (θ.app
          Q) q U) y))) := by
  have h := TensorChainProof.pure S T q₀ (θ.app P) (θ.app Q) p q U x y
  rw [TensorChainProof.totalPure_eq, TensorChainProof.totalPure_eq] at h
  apply forgetRestriction_injective g _ U
  exact (restrictComplexMap_section f g ((integralOperationsForgetSheaf J).map q₀) hq₀
    (TensorChainProof.map S T q₀ (θ.app P) (θ.app Q)) (p+q) U _).trans
      h

private theorem level_map_eq {K L : D × D} (a : K ⟶ L) :
    (level S f F).map a =
      (WeilConjectures.integralOperationsRestrictionComplex f).map
        (tensorTotalMap (F.map a.1) (F.map a.2)) := by
  exact (TensorTotalProof.composite_map F (SheafOfModules.restrictScalars f) a).trans
    (congrArg (WeilConjectures.integralOperationsRestrictionComplex f).map
      (TensorChainProof.totalMap_eq (F.map a.1) (F.map a.2)).symm)

@[no_expose] private noncomputable def candidate [Presheaf.IsLocallySurjective J f.hom] :
    level S f F ⟶ level T g G where
  app := component S T f g q₀ hq₀ F G θ
  naturality {K L} u := by
    rw [level_map_eq, level_map_eq]
    exact SheafOfModules.IntegralScalarProof.restrictComplexMap_naturality f g
      ((integralOperationsForgetSheaf J).map q₀) hq₀
      (TensorChainProof.map S T q₀ (θ.app K.1) (θ.app K.2))
      (TensorChainProof.map S T q₀ (θ.app L.1) (θ.app L.2))
      (tensorTotalMap (F.map u.1) (F.map u.2))
      (tensorTotalMap (G.map u.1) (G.map u.2))
      (TensorChainProof.map_naturality S T q₀ (θ.app K.1) (θ.app K.2)
        (θ.app L.1) (θ.app L.2) (F.map u.1) (F.map u.2) (G.map u.1) (G.map u.2)
        (θ.naturality u.1) (θ.naturality u.2))

attribute [local irreducible] component

include hq₀ in
private theorem existsUnique [hf : Presheaf.IsLocallySurjective J f.hom] :
    ∃! τ : level S f F ⟶ level T g G,
      ∀ (P Q : D) (p q : ℤ) (U : Cᵒᵖ)
        (x : ((F.obj P).X p).val.obj U) (y : ((F.obj Q).X q).val.obj U),
      forgetRestriction g _ U
        ((integralOperationsNaturalSectionApply τ (P,Q) (p+q) U)
          (intoRestriction f _ U (sectionPure S F P Q p q U x y))) =
        sectionPure T G P Q p q U
          (forgetRestriction ((integralOperationsForgetSheaf J).map q₀) _ U
            ((integralOperationsComplexSectionApply (θ.app
            P) p U) x))
          (forgetRestriction ((integralOperationsForgetSheaf J).map q₀) _ U
            ((integralOperationsComplexSectionApply (θ.app
            Q) q U) y)) := by
  refine ⟨candidate S T f g q₀ hq₀ F G θ, ?_, ?_⟩
  · intro P Q p q U x y
    exact congrArg (forgetRestriction g _ U)
      (component_pure S T f g q₀ hq₀ F G θ P Q p q U x y)
  · intro τ hτ
    apply NatTrans.ext
    funext K
    obtain ⟨P,Q⟩ := K
    apply HomologicalComplex.hom_ext
    intro j
    apply genericRestrictedTotal_hom_ext S T f g ((integralOperationsForgetSheaf J).map q₀) hq₀
    intro p q hpq U x y
    subst j
    exact (hτ P Q p q U x y).trans
      (congrArg (forgetRestriction g _ U)
        (component_pure S T f g q₀ hq₀ F G θ P Q p q U x y)).symm

end TensorNaturalProof

end SignedTensorConstruction

end PrivateTensorTransition

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients

attribute [local instance 2000] integralOperationsFiniteHasMap

/-- The coefficient projection with its native ring-sheaf source explicit.
Source: Stacks Tag 03DA (blueprint: lem-pur-integral-operations-well-defined). -/
private noncomputable def integralOperationsProjection (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    completedIntegralCoefficientSheafUnrestricted l E W ⟶ integralCoefficientSheaf l E W n :=
  (integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology W)).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)

/-- The canonical base-change functor, kept as a named functor during module calculations.
Source: Stacks Tag 09A5 (blueprint: lem-pur-integral-operations-well-defined). -/
private noncomputable def integralOperationsBaseChange {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) : Y.ProEt ⥤ X.ProEt :=
  AlgebraicGeometry.Scheme.proEtaleBaseChange f

/-- Continuity of the named base-change functor.
Source: Stacks Tag 09A5 (blueprint: lem-pur-integral-operations-well-defined). -/
private instance integralOperationsBaseChange_isContinuous
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) :
    (integralOperationsBaseChange f).IsContinuous
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (AlgebraicGeometry.Scheme.ProEt.topology X) :=
  AlgebraicGeometry.Scheme.proEtaleBaseChange_isContinuous f

/-- The finite coefficient map, with its native ring sheaves explicit.
Source: Stacks Tag 03D2 (blueprint: lem-pur-integral-operations-well-defined). -/
private noncomputable def integralOperationsDirectRingMap
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralCoefficientSheaf l E Y n ⟶
      ((integralOperationsBaseChange f).sheafPushforwardContinuous
        RingCat.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (AlgebraicGeometry.Scheme.ProEt.topology X)).obj
          (integralCoefficientSheaf l E X n) :=
  ⟨Functor.whiskerRight
    (AlgebraicGeometry.Scheme.coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- The canonical finite pullback adjunction, with the native coefficient categories explicit.
Source: Stacks Tag 03D2 (blueprint: lem-pur-integral-operations-well-defined). -/
private noncomputable def integralOperationsPullbackAdjunction
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralOperationsLevelPullback l E f n ⊣
      SheafOfModules.pushforward (integralOperationsDirectRingMap l E f n) :=
  AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

section IntegralTensorTransitionProof

section FiniteLinearization

attribute [local irreducible] unrestrictedIntegralReductionExistence
  unrestrictedIntegralReductionFunctor unrestrictedIntegralTransition
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingProjectionUnrestricted

private noncomputable def integralFiniteStep (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    integralCoefficientCommRingSheaf l E W (n + 1) ⟶
      integralCoefficientCommRingSheaf l E W n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))

private noncomputable abbrev integralFiniteRestrict
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :=
  SheafOfModules.restrictScalars (integralCoefficientSheafTransition l E W n)

private noncomputable def integralFiniteMap
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ) :
    (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P).X i) ⟶
      (integralFiniteRestrict l E W n).obj
        (((unrestrictedIntegralFiniteComplex l E W n).obj P).X i) := by
  refine SheafOfModules.IntegralScalarProof.retypeMap
    (integralCoefficientSheafTransition l E W n) _ _ ?_ ?_
  · exact (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted l E W)).map
      (((unrestrictedIntegralTransition l E W n).app P).f i)
  · intro U s x
    exact unrestrictedIntegralTransition_smul l E W n P i U s x

private noncomputable def integralFiniteTransition
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    unrestrictedIntegralFiniteComplex l E W (n + 1) ⟶
      unrestrictedIntegralFiniteComplex l E W n ⋙
        (integralFiniteRestrict l E W n).mapHomologicalComplex (.up ℤ) where
  app P :=
    { f := integralFiniteMap l E W n P
      comm' := by
        intro i j _
        ext U x
        change _ = _
        exact congrArg (fun k ↦ k.val.app U x)
          (((unrestrictedIntegralTransition l E W n).app P).comm i j) }
  naturality := by
    intro P Q a
    apply HomologicalComplex.hom_ext
    intro i
    ext U x
    exact congrArg (fun k ↦ (k.f i).val.app U x)
      ((unrestrictedIntegralTransition l E W n).naturality a)

end FiniteLinearization

private theorem completedProjection_locallySurjective (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) : Presheaf.IsLocallySurjective (AlgebraicGeometry.Scheme.ProEt.topology W)
      ((integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology
        W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W n)).hom := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology W
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  let : J.WEqualsLocallyBijective CommRingCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let q : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (y.down)
    refine ⟨⟨x⟩, ?_⟩
    apply ULift.ext
    exact hx
  have hc := constantMap_surjective J q hq
  have : Presheaf.IsLocallySurjective J (integralConstantQuotientOfUniverses l E W n).hom := by
    rw [Presheaf.isLocallySurjective_iff_whisker_forget]
    exact (Presheaf.isLocallySurjective_iff_whisker_forget J
      (((constantSheaf J CommRingCat.{max u (t + 1)}).map q).hom)).mp hc
  have hπ : Presheaf.IsLocallySurjective J
      (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom := by
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (f₁ := (integralConstantToCompletionOfUniverses l E W).hom)
      (f₃ := (integralConstantQuotientOfUniverses l E W n).hom)
      (congrArg (fun k ↦ k.hom)
        (limit.lift_π (integralConstantConeOfUniverses l E W) (op n)))
  constructor
  intro U s
  apply J.superset_covering ?_ (Presheaf.imageSieve_mem J
    (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom s)
  intro V f hf
  obtain ⟨x, hx⟩ := hf
  exact ⟨x, hx⟩

private theorem integralProjection_step (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) :
    (integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W (n + 1)) ≫
          integralCoefficientSheafTransition l E W n =
    (integralOperationsForgetSheaf.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology W)).map
        (completedIntegralCommRingProjectionUnrestricted l E W n) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app U ≫
      (integralCoefficientSheafTransition l E W n).hom.app U =
    (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U
  have h := congrArg (fun k ↦ k.hom.app U)
    (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
  simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h

private noncomputable abbrev integralDirectRingMap
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :=
  integralOperationsDirectRingMap l E f n

private theorem integralDirectRingMap_square
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralCoefficientSheafTransition l E Y n ≫ integralDirectRingMap l E f n =
      integralDirectRingMap l E f (n + 1) ≫
        ((integralOperationsBaseChange f).sheafPushforwardContinuous
          RingCat.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (AlgebraicGeometry.Scheme.ProEt.topology X)).map
            (integralCoefficientSheafTransition l E X n) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let q := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp
        (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  exact congrArg (fun k ↦ (integralOperationsRingForget).map (k.hom.app V))
    (AlgebraicGeometry.Scheme.directRingMap_naturality f q)

attribute [local irreducible]
  AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback Functor.leftAdjoint

private noncomputable abbrev integralPullbackAdj
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :=
  integralOperationsPullbackAdjunction l E f n

private noncomputable def integralPullbackFiniteData
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    {M : integralOperationsFiniteModules l E Y (n + 1)}
    {N : integralOperationsFiniteModules l E Y n}
    (a : M ⟶ (integralFiniteRestrict l E Y n).obj N) :=
  SheafOfModules.IntegralPullbackProof.mateData
    (integralOperationsBaseChange f)
    (integralCoefficientSheafTransition l E X n) (integralCoefficientSheafTransition l E Y n)
    (integralDirectRingMap l E f (n + 1)) (integralDirectRingMap l E f n)
    (integralDirectRingMap_square l E f n)
    (integralPullbackAdj l E f (n + 1)) (integralPullbackAdj l E f n) a

private noncomputable def integralPullbackFiniteMap
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    {M : integralOperationsFiniteModules l E Y (n + 1)}
    {N : integralOperationsFiniteModules l E Y n}
    (a : M ⟶ (integralFiniteRestrict l E Y n).obj N) :
    (integralOperationsLevelPullback l E f (n + 1)).obj M ⟶
      (integralFiniteRestrict l E X n).obj ((integralOperationsLevelPullback l E f n).obj N) :=
  integralPullbackFiniteData l E f n a

private theorem integralPullbackFiniteMap_naturality
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    {M M' : integralOperationsFiniteModules l E Y (n + 1)}
    {N N' : integralOperationsFiniteModules l E Y n}
    (a : M ⟶ (integralFiniteRestrict l E Y n).obj N)
    (b : M' ⟶ (integralFiniteRestrict l E Y n).obj N')
    (u : M ⟶ M') (v : N ⟶ N')
    (h : u ≫ b = a ≫ (integralFiniteRestrict l E Y n).map v) :
    (integralOperationsLevelPullback l E f (n + 1)).map u ≫
        integralPullbackFiniteMap l E f n b =
      integralPullbackFiniteMap l E f n a ≫ (integralFiniteRestrict l E X n).map
        ((integralOperationsLevelPullback l E f n).map v) :=
  SheafOfModules.IntegralPullbackProof.mateData_naturality
    (integralOperationsBaseChange f)
    (integralCoefficientSheafTransition l E X n) (integralCoefficientSheafTransition l E Y n)
    (integralDirectRingMap l E f (n + 1)) (integralDirectRingMap l E f n)
    (integralDirectRingMap_square l E f n)
    (integralPullbackAdj l E f (n + 1)) (integralPullbackAdj l E f n) a b u v h

private noncomputable def integralPullbackFiniteComplexMap
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOperationsLevelPullback l E f (n + 1)).mapHomologicalComplex (.up ℤ)).obj
        ((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P) ⟶
      ((integralFiniteRestrict l E X n).mapHomologicalComplex (.up ℤ)).obj
        (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj
          ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) where
  f i := integralPullbackFiniteMap l E f n (((integralFiniteTransition l E Y n).app P).f i)
  comm' i j _ := by
    exact (integralPullbackFiniteMap_naturality l E f n
      (((integralFiniteTransition l E Y n).app P).f i)
      (((integralFiniteTransition l E Y n).app P).f j)
      (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).d i j)
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).d i j)
      (((integralFiniteTransition l E Y n).app P).comm i j).symm).symm

attribute [local irreducible] unrestrictedIntegralReductionExistence
  unrestrictedIntegralReductionFunctor unrestrictedIntegralTransition
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingProjectionUnrestricted

private noncomputable abbrev integralCompletedProjection
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ) := integralOperationsProjection l E W n

private noncomputable abbrev integralCompletedRestrict (W : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) : integralOperationsFiniteModules l E W n ⥤ integralTowerModules l E W :=
  SheafOfModules.restrictScalars.{max u (t + 1)} (integralCompletedProjection l E W n)

private noncomputable def integralPullbackTransitionCandidate
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralOperationsPullbackLevel l E f (n + 1) ⟶ integralOperationsPullbackLevel l E f n where
  app P := by
    refine SheafOfModules.IntegralScalarProof.restrictComplexMap
      (R := completedIntegralCoefficientSheafUnrestricted l E X)
      (S := integralCoefficientSheaf l E X (n + 1))
      (T := integralCoefficientSheaf l E X n)
      (integralCompletedProjection l E X (n + 1))
      (integralCompletedProjection l E X n)
      (integralCoefficientSheafTransition l E X n) (integralProjection_step l E X n)
      ?_
    exact integralPullbackFiniteComplexMap l E f n P
  naturality := by
    intro P Q a
    apply HomologicalComplex.hom_ext
    intro i
    ext U x
    have h := congrArg (fun k ↦ k.f i) ((integralFiniteTransition l E Y n).naturality a)
    have h' := integralPullbackFiniteMap_naturality l E f n
      (((integralFiniteTransition l E Y n).app P).f i)
      (((integralFiniteTransition l E Y n).app Q).f i)
      (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).map a).f i)
      (((unrestrictedIntegralFiniteComplex l E Y n).map a).f i) h
    exact congrArg (fun k ↦ k.val.app U x) h'

private theorem integralPullback_restricted_hom_ext
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (M : integralOperationsFiniteModules l E Y (n + 1))
    (N : integralOperationsFiniteModules l E X n)
    (a b : (integralCompletedRestrict l E X (n + 1)).obj
        ((integralOperationsLevelPullback l E f (n + 1)).obj M) ⟶
      (integralCompletedRestrict l E X n).obj N)
    (h : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      (integralOperationsSectionApply a ((integralOperationsBaseChange f).op.obj (op V)))
          (integralOperationsPullbackGenerator l E f (n + 1) M V x) =
        (integralOperationsSectionApply b ((integralOperationsBaseChange f).op.obj (op V)))
          (integralOperationsPullbackGenerator l E f (n + 1) M V x)) : a = b := by
  have : Presheaf.IsLocallySurjective (AlgebraicGeometry.Scheme.ProEt.topology X)
      (integralCompletedProjection l E X (n + 1)).hom :=
    completedProjection_locallySurjective l E X (n + 1)
  apply SheafOfModules.IntegralPullbackProof.restricted_hom_ext
    (integralOperationsBaseChange f)
    (integralCoefficientSheafTransition l E X n)
    (integralDirectRingMap l E f (n + 1)) (integralPullbackAdj l E f (n + 1))
    (integralCompletedProjection l E X (n + 1)) (integralCompletedProjection l E X n)
    (integralProjection_step l E X n) M N a b
  intro U x
  change a.val.app _ (SheafOfModules.IntegralPullbackProof.unitSection
    (integralOperationsBaseChange f) (integralDirectRingMap l E f (n + 1))
    (integralPullbackAdj l E f (n + 1)) M U x) = _
  exact h U.unop x

end IntegralTensorTransitionProof

section TensorTransitionSpecialization
attribute [local instance 2001] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

end TensorTransitionSpecialization

section Roos

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

end Roos

private theorem integralOperationsExactProducts (W : AlgebraicGeometry.Scheme.{t}) :
    HasExactLimitsOfShape (Discrete ℕ) (integralTowerModules l E W) := by
  exact AlgebraicGeometry.Scheme.ProEt.products_exact.{t, u, 0} W
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)) ℕ

attribute [local instance 3000] Algebra.toModule

-- Prefer the exact completed-module presentation during private proof search.
attribute [local instance 3000] integralTowerHasDerivedCategory

section IntegralOperationsRoosQuasiIsoInvariantProof
set_option Elab.async true

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

private theorem cofiberMap_eq_coneMap
    {A : Type a} [Category.{b} A] [Abelian A]
    {K L K' L' : CochainComplex A ℤ} (s : K ⟶ L) (s' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : s ≫ b = a ≫ s') :
    HomologicalComplex.homotopyCofiber.mapArrowHom s s'
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (Arrow.homMk a b h.symm) =
      CochainComplex.mappingCone.map s s' a b h := by
  exact CategoryTheory.cofiberMap_eq_coneMap s s' a b h

/-- A levelwise quasi-isomorphism induces a quasi-isomorphism of strict Roos complexes.
Source: Stacks Project, Derived Categories, Tags 07KC, 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: exact countable products make the product of the component maps a
quasi-isomorphism. The commutative square for 1-s gives a morphism of the
mapping-cone triangles. Its first two components become isomorphisms under
localization, so the third does as well. Reflection by localization and shift
invariance give the assertion for the recorded diagonal shifted-cone map. -/
private theorem roosMap_quasiIso
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    [HasDerivedCategory A] [HasExactLimitsOfShape (Discrete ℕ) A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (α : C ⟶ C') (hα : ∀ n : ℕ, QuasiIso (α.app (op n))) :
    QuasiIso (integralOperationsRoosMap α) := by
  classical
  let p := Limits.Pi.map (fun n ↦ α.app (op n))
  have (n : Discrete ℕ) : QuasiIso
      ((Discrete.natTrans (F := Discrete.functor (fun n ↦ C.obj (op n)))
        (G := Discrete.functor (fun n ↦ C'.obj (op n)))
        (fun n ↦ α.app (op n.as))).app n) := hα n.as
  have hp : QuasiIso p := HomologicalComplex.quasiIso_limMap
    (Discrete.natTrans (F := Discrete.functor (fun n ↦ C.obj (op n)))
      (G := Discrete.functor (fun n ↦ C'.obj (op n))) (fun n ↦ α.app (op n.as)))
  let s := towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
    (integralOperationsTowerStep C)
  let s' := towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
    (integralOperationsTowerStep C')
  have hcone : QuasiIso (CochainComplex.mappingCone.map s s' p p
      (integralOperationsRoos_square α)) :=
    CochainComplex.mappingCone.quasiIso_map_of_quasiIso s s' p p
      (integralOperationsRoos_square α)
  unfold integralOperationsRoosMap
  rw [cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square α)]
  infer_instance

private theorem integralOperationsRoosQuasiIsoInvariant (W : AlgebraicGeometry.Scheme.{t})
    {C C' : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ}
    (α : C ⟶ C') (hα : ∀ n : ℕ, QuasiIso (α.app (op n))) :
    QuasiIso (integralOperationsRoosMap α) := by
  have := integralOperationsExactProducts l E W
  exact roosMap_quasiIso α hα

end IntegralOperationsRoosQuasiIsoInvariantProof

section IntegralOperationsPullbackQuasiIsoInvariantProof

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

attribute [local irreducible] SheafOfModules.monoidalCategory
  CochainComplex.IsKFlatIndependentCoefficients
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRestriction_exact
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J RingCat.{u}} (φ : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} φ) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} φ) := by
  let U := SheafOfModules.restrictScalars.{u} φ
  have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf S))
  have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf R)⟩

private theorem coefficientRestriction_quasiIso
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J RingCat.{u}} (φ : R ⟶ S)
    {P Q : CochainComplex (SheafOfModules.{u} S) ℤ} (f : P ⟶ Q) (hf : QuasiIso f) :
    QuasiIso (((SheafOfModules.restrictScalars.{u} φ).mapHomologicalComplex (.up ℤ)).map f) := by
  have h := coefficientRestriction_exact φ
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} φ) := h.1
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} φ) := h.2
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f
    (SheafOfModules.restrictScalars.{u} φ) (hφ := hf)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteReduction_quasiIso
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    {P Q : CochainComplex (integralTowerModules l E W) ℤ} (α : P ⟶ Q)
    (hP : (integralOperationsGoodComplex l E W) P)
    (hQ : (integralOperationsGoodComplex l E W) Q) (hα : QuasiIso α) :
    QuasiIso ((unrestrictedIntegralFiniteComplex l E W n).map α) := by
  have : (unrestrictedIntegralReductionFunctor l E W n).Additive :=
    unrestrictedIntegralReductionFunctor_additive l E W n
  exact SheafOfModules.derivedChangeOfRingsIndependentCoefficients_kflat_invariance
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (unrestrictedIntegralReductionFunctor l E W n)
    (unrestrictedReduction_obj l E W n) (unrestrictedReduction_map l E W n)
    α hP.1 hQ.1 hα

set_option backward.isDefEq.respectTransparency false

/-- Pullback comparison for strict integral operations.
Source: Stacks Project, sites-cohomology.tex Tags 06YS, 06YT and 0G7E;
derived.tex Tags 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: reduction modulo the coefficient powers preserves quasi-isomorphisms of
K-flat complexes. Constant-coefficient pro-etale module inverse image is exact,
as is restriction of scalars, so every map in the strict pullback tower is a
quasi-isomorphism. Exact countable products and the mapping-cone triangle give
quasi-isomorphism invariance of the associated Roos complex. -/
private theorem integralOperationsPullbackQuasiIsoInvariant
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) :
    ∀ (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (α : P.obj ⟶ P'.obj), QuasiIso α →
      QuasiIso ((integralOperationsPullbackComplexFunctor l E f).map α) := by
  intro P P' α hα
  apply integralOperationsRoosQuasiIsoInvariant l E X
  intro n
  change QuasiIso ((integralOperationsPullbackLevel l E f n).map α)
  let F := integralOperationsLevelPullback l E f n
  have : F.Additive := integralOperationsLevelPullback_additive l E f n
  have he : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback_exact.{t,u} f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  have : PreservesFiniteLimits F := he.1
  have : PreservesFiniteColimits F := he.2
  let φ := (integralOperationsForgetSheaf.{max u (t + 1)}
    (AlgebraicGeometry.Scheme.ProEt.topology X)).map
      (completedIntegralCommRingProjectionUnrestricted l E X n)
  have hR := finiteReduction_quasiIso l E Y n α P.property P'.property hα
  have hF := HomologicalComplex.quasiIso_map_of_preservesHomology
    ((unrestrictedIntegralFiniteComplex l E Y n).map α) F (hφ := hR)
  exact coefficientRestriction_quasiIso φ _ hF

end IntegralOperationsPullbackQuasiIsoInvariantProof

section IntegralOperationsTensorQuasiIsoInvariantProof

attribute [local irreducible] SheafOfModules.monoidalCategory

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence

private theorem finiteReduction_kFlat
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : (integralOperationsGoodComplex l E W) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology W)
      (R := integralCoefficientCommRingSheaf l E W n)
      ((unrestrictedIntegralFiniteComplex l E W n).obj P) := by
  have : (unrestrictedIntegralReductionFunctor l E W n).Additive :=
    unrestrictedIntegralReductionFunctor_additive l E W n
  let R := completedIntegralCommRingSheafUnrestricted l E W
  let φ := completedIntegralCommRingProjectionUnrestricted l E W n
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  have hflat (i : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X i)) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X i)) (hP.2 i)
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (R := R) (S := integralCoefficientCommRingSheaf l E W n)
    φ P (unrestrictedIntegralReductionFunctor l E W n)
    (unrestrictedReduction_obj l E W n) (unrestrictedReduction_map l E W n)
    hP.1 hflat
  exact h.1

namespace IntegralTensorProof

universe x y z

open SheafOfModules MonoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem tensor_quasiIso
    {C : Type x} [Category.{y} C] [EssentiallySmall.{z} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{z}]
    {R : Sheaf J CommRingCat.{z}}
    {E E' K K' : CochainComplex (SheafOfModules.{z}
      ((integralOperationsForgetSheaf.{z} J).obj R)) ℤ}
    (α : E ⟶ E') (β : K ⟶ K') (hα : QuasiIso α) (hβ : QuasiIso β)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K)
    (hE' : CochainComplex.IsKFlatIndependentCoefficients (R := R) E') :
    let := monoidalCategory R
    QuasiIso ((Functor.uncurry.obj ((curriedTensor (SheafOfModules.{z}
      ((integralOperationsForgetSheaf.{z} J).obj R))).map₂CochainComplex)).map
        (X := (E, K)) (Y := (E', K')) (α, β)) := by
  let := monoidalCategory R
  let := symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  exact quasiIso_comp _ _
    (hφ := SheafOfModules.tensor_right_quasiIso α hα hK)
    (hφ' := SheafOfModules.tensor_left_quasiIso β hβ hE')

end IntegralTensorProof

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteTensor_quasiIso
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    {P P' Q Q' : CochainComplex (integralTowerModules l E W) ℤ}
    (α : P ⟶ P') (β : Q ⟶ Q')
    (hP : (integralOperationsGoodComplex l E W) P)
    (hP' : (integralOperationsGoodComplex l E W) P')
    (hQ : (integralOperationsGoodComplex l E W) Q)
    (hQ' : (integralOperationsGoodComplex l E W) Q')
    (hα : QuasiIso α) (hβ : QuasiIso β) :
    QuasiIso ((Functor.uncurry.obj
      ((MonoidalCategory.curriedTensor
        (integralOperationsFiniteModules l E W n)).map₂CochainComplex)).map
          (X := ((unrestrictedIntegralFiniteComplex l E W n).obj P,
            (unrestrictedIntegralFiniteComplex l E W n).obj Q))
          (Y := ((unrestrictedIntegralFiniteComplex l E W n).obj P',
            (unrestrictedIntegralFiniteComplex l E W n).obj Q'))
          ((unrestrictedIntegralFiniteComplex l E W n).map α,
            (unrestrictedIntegralFiniteComplex l E W n).map β)) := by
  exact IntegralTensorProof.tensor_quasiIso
    (C := W.ProEt) (J := AlgebraicGeometry.Scheme.ProEt.topology W)
    (R := integralCoefficientCommRingSheaf l E W n)
    ((unrestrictedIntegralFiniteComplex l E W n).map α)
    ((unrestrictedIntegralFiniteComplex l E W n).map β)
    (finiteReduction_quasiIso l E W n α hP hP' hα)
    (finiteReduction_quasiIso l E W n β hQ hQ' hβ)
    (finiteReduction_kFlat l E W n Q hQ)
    (finiteReduction_kFlat l E W n P' hP')

set_option backward.isDefEq.respectTransparency false

/-- Tensor comparison for strict integral operations.
Source: Stacks Project, sites-cohomology.tex Tags 06YS, 06YT and 0G7E;
derived.tex Tags 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: finite coefficient reduction preserves quasi-isomorphisms between K-flat
complexes, and preserves K-flatness and flat terms by tensor cancellation under
change of rings. Tensoring the acyclic mapping cone with the other K-flat
factor proves invariance of the finite total tensors. Restriction of scalars is exact, so every
level of the strict tower map is a quasi-isomorphism. Exact countable products and
the mapping-cone triangle imply quasi-isomorphism invariance of its Roos complex. -/
private theorem integralOperationsTensorQuasiIsoInvariant
    (W : AlgebraicGeometry.Scheme.{t}) :
    ∀ (P P' Q Q' : (integralOperationsGoodComplex l E W).FullSubcategory)
      (α : P.obj ⟶ P'.obj) (β : Q.obj ⟶ Q'.obj), QuasiIso α → QuasiIso β →
      QuasiIso ((integralOperationsTensorComplexFunctor l E W).map
        (X := (P.obj, Q.obj)) (Y := (P'.obj, Q'.obj)) (α, β)) := by
  intro P P' Q Q' α β hα hβ
  apply integralOperationsRoosQuasiIsoInvariant l E W
  intro n
  change QuasiIso ((integralOperationsTensorLevel l E W n).map
    (X := (P.obj, Q.obj)) (Y := (P'.obj, Q'.obj)) (α, β))
  let φ := (integralOperationsForgetSheaf.{max u (t + 1)}
    (AlgebraicGeometry.Scheme.ProEt.topology W)).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)
  exact coefficientRestriction_quasiIso φ _
    (finiteTensor_quasiIso l E W n α β P.property P'.property Q.property Q'.property hα hβ)

end IntegralOperationsTensorQuasiIsoInvariantProof

section IntegralOperationsGoodLocalizationProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Good completed-coefficient complexes localize to the entire derived category.
Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YT.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: the canonical functorial flat cover gives a reduced left resolution functor.
Its filtered-colimit construction has flat terms and is K-flat, and its natural
augmentation is a quasi-isomorphism. The inclusion of good complexes is fully
faithful. The augmentation and its restriction to good complexes give inverse
localized functors, so the inclusion is a localized equivalence. Composing with
the standard derived localization gives the claimed localization. -/
private theorem goodComplexes_isLocalization
    {C : Type a} [Category.{b} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose WeilConjectures.integralOperationsRingForget.{u}]
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory (SheafOfModules.{u}
      ((integralOperationsForgetSheaf.{u} J).obj R))]
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((integralOperationsForgetSheaf.{u} J).obj R)) ℤ))
    (hp : ∀ K, P K ↔ CochainComplex.IsKFlatIndependentCoefficients (R := R) K ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (K.X i)) :
    (P.ι ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage P.ι) := by
  have hP : P = CategoryTheory.TensorFlatRepresentative (J := J) (R := R) := by
    funext K
    exact propext (hp K)
  subst P
  exact CategoryTheory.flat_representative_localization J R

private theorem integralOperationsGoodLocalization_isLocalization
    (W : AlgebraicGeometry.Scheme.{t}) :
    (integralOperationsGoodLocalization l E W).IsLocalization
      ((HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
        (integralOperationsGoodComplex l E W).ι) := by
  exact goodComplexes_isLocalization
    (completedIntegralCommRingSheafUnrestricted l E W) (integralOperationsGoodComplex l E W)
    (fun _ ↦ Iff.rfl)

end IntegralOperationsGoodLocalizationProof

private theorem localization_factor_exists
    {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
    {V : Type a'} [Category.{b'} V] (L : A ⥤ B) (W : MorphismProperty A)
    [L.IsLocalization W] (F : A ⥤ V) (hF : W.IsInvertedBy F) :
    ∃ G : B ⥤ V, Nonempty (L ⋙ G ≅ F) :=
  ⟨Localization.lift F hF L, ⟨Localization.fac F hF L⟩⟩

private theorem localization_product_factor_exists
    {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
    {V : Type a'} [Category.{b'} V] (L : A ⥤ B) (W : MorphismProperty A)
    [L.IsLocalization W] [W.ContainsIdentities]
    (F : A × A ⥤ V) (hF : (W.prod W).IsInvertedBy F) :
    ∃ G : B × B ⥤ V, Nonempty ((L.prod L) ⋙ G ≅ F) :=
  localization_factor_exists (L.prod L) (W.prod W) F hF

section IntegralOperationsTensorDescentProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsPullbackOnGood

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open CategoryTheory

/-- The strict integral tensor descends to the product of the derived categories.
Source: Stacks Project, Cohomology on Sites, Tags 06YT and 0G7E.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: good completed-coefficient complexes localize to the derived category, hence
pairs of good complexes localize to its product. Tensor quasi-isomorphism invariance
shows that the strict Roos tensor followed by derived localization inverts the
product class of quasi-isomorphisms. Apply the universal property of localization;
its factorization isomorphism gives the natural representative comparison. -/
private theorem integralOperationsTensorDescent (W : AlgebraicGeometry.Scheme.{t}) :
    ∃ G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W),
      Nonempty (((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W) := by
  have := integralOperationsGoodLocalization_isLocalization l E W
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E W).ι
  let L := integralOperationsGoodLocalization l E W
  let T := integralOperationsTensorOnGood l E W
  have hT : (V.prod V).IsInvertedBy T := by
    intro P Q f hf
    have h := integralOperationsTensorQuasiIsoInvariant l E W
      P.1 Q.1 P.2 Q.2 f.1.hom f.2.hom hf.1 hf.2
    change IsIso (DerivedCategory.Q.map
      ((integralOperationsTensorComplexFunctor l E W).map
        (X := (P.1.obj, P.2.obj)) (Y := (Q.1.obj, Q.2.obj)) (f.1.hom, f.2.hom)))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h
  exact localization_product_factor_exists L V T hT

end IntegralOperationsTensorDescentProof

section IntegralOperationsComparisonExistsProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open CategoryTheory

/-- Existence of the natural localization comparisons for strict integral operations.
Source: Stacks Project, sites-cohomology.tex Tags 06YS, 06YT and 0G7E;
derived.tex Tags 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: good complexes localize to the derived category using functorial flat
resolutions. The strict pullback functor sends quasi-isomorphisms between good
complexes to quasi-isomorphisms by exact finite pullback, finite reduction and
Roos invariance. Its derived localization therefore inverts the defining class,
and the localization universal property gives F with its natural comparison.
The separately proved tensor descent gives G with its natural comparison. -/
private theorem integralOperationsComparisonExists
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{t}) :
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W)),
      Nonempty (integralOperationsGoodLocalization l E Y ⋙ F ≅
        integralOperationsPullbackOnGood l E f) ∧
      Nonempty (((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W) := by
  have := integralOperationsGoodLocalization_isLocalization l E Y
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  let L := integralOperationsGoodLocalization l E Y
  let T := integralOperationsPullbackOnGood l E f
  have hT : V.IsInvertedBy T := by
    intro P Q a ha
    have h := integralOperationsPullbackQuasiIsoInvariant l E f P Q a.hom ha
    change IsIso (DerivedCategory.Q.map
      ((integralOperationsPullbackComplexFunctor l E f).map a.hom))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h
  obtain ⟨G, d⟩ := integralOperationsTensorDescent l E W
  obtain ⟨F, e⟩ := localization_factor_exists L V T hT
  exact ⟨F, G, e, d⟩

end IntegralOperationsComparisonExistsProof

section IntegralOperationsNormalizedDescentProof

attribute [local irreducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood integralOperationsPullbackOnGood

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

private theorem good_whisker_fullyFaithful (W : AlgebraicGeometry.Scheme.{t})
    (D : Type a) [Category.{b} D] :
    Nonempty (((whiskeringLeft _ _ D).obj
      (integralOperationsGoodLocalization l E W)).FullyFaithful) := by
  have := integralOperationsGoodLocalization_isLocalization l E W
  exact ⟨Localization.fullyFaithfulWhiskeringLeft
    (integralOperationsGoodLocalization l E W)
    ((HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E W).ι) D⟩

private theorem good_prod_whisker_fullyFaithful (W : AlgebraicGeometry.Scheme.{t})
    (D : Type a) [Category.{b} D] :
    Nonempty (((whiskeringLeft _ _ D).obj
      ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W))).FullyFaithful) := by
  have := integralOperationsGoodLocalization_isLocalization l E W
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E W).ι
  exact ⟨Localization.fullyFaithfulWhiskeringLeft
    ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) (V.prod V) D⟩

private theorem unique_comparison
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (L : C ⥤ D) (hL : ((whiskeringLeft _ _ H).obj L).FullyFaithful)
    {T : C ⥤ H} {F F' : D ⥤ H} (e : L ⋙ F ≅ T) (e' : L ⋙ F' ≅ T) :
    ∃! i : F ≅ F', isoWhiskerLeft L i ≪≫ e' = e := by
  let i : F ≅ F' := hL.isoEquiv.symm (e ≪≫ e'.symm)
  have hi : isoWhiskerLeft L i = e ≪≫ e'.symm := hL.isoEquiv.apply_symm_apply _
  refine ⟨i, ?_, ?_⟩
  · change isoWhiskerLeft L i ≪≫ e' = e
    rw [hi]
    simp
  · intro j hj
    apply hL.isoEquiv.injective
    change isoWhiskerLeft L j = isoWhiskerLeft L i
    rw [hi]
    have h := congrArg (fun k ↦ k ≪≫ e'.symm) hj
    simpa using h

/-- Compatibility with every other normalized pullback comparison. -/
private def integralOperationsPullbackComparisonSpec
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)
    (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (e : integralOperationsGoodLocalization l E Y ⋙ F ≅
        integralOperationsPullbackOnGood l E f) : Prop :=
  ∀ (F' : DerivedCategory (integralTowerModules l E Y) ⥤
          DerivedCategory (integralTowerModules l E X))
        (e' : integralOperationsGoodLocalization l E Y ⋙ F' ≅
          integralOperationsPullbackOnGood l E f),
        ∃! ι : F ≅ F',
          isoWhiskerLeft (integralOperationsGoodLocalization l E Y) ι ≪≫ e' = e

/-- Compatibility with every other normalized tensor comparison. -/
private def integralOperationsTensorComparisonSpec
    (W : AlgebraicGeometry.Scheme.{t})
    (G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W))
      (d : ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W) : Prop :=
  ∀ (G' : (DerivedCategory (integralTowerModules l E W)) ×
          (DerivedCategory (integralTowerModules l E W)) ⥤
            DerivedCategory (integralTowerModules l E W))
        (d' : ((integralOperationsGoodLocalization l E W).prod
          (integralOperationsGoodLocalization l E W)) ⋙ G' ≅
            integralOperationsTensorOnGood l E W),
        ∃! ι : G ≅ G', isoWhiskerLeft
          ((integralOperationsGoodLocalization l E W).prod
            (integralOperationsGoodLocalization l E W)) ι ≪≫ d' = d

set_option backward.isDefEq.respectTransparency true in
/-- Localization descent comparison for strict integral operations.
Source: Stacks Project, sites-cohomology.tex Tags 06YS, 06YT and 0G7E;
derived.tex Tags 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: take the two descended functors and natural comparisons from
integralOperationsComparisonExists. The functorial flat resolution proves that good
complexes localize to the derived category. Precomposition with this localization
and with its product is fully faithful by the localization universal property.
For two representative
comparisons e and e', the image of the required isomorphism must be e followed by
the inverse of e'. The fully faithful whiskering functor lifts this isomorphism;
cancellation proves the compatibility equation, and faithfulness proves uniqueness.
Apply the same argument to the tensor product localization. -/
private theorem integralOperationsNormalizedDescent
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{t}) :
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (e : integralOperationsGoodLocalization l E Y ⋙ F ≅
        integralOperationsPullbackOnGood l E f)
      (G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W))
      (d : ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W),
      integralOperationsPullbackComparisonSpec l E f F e ∧
      integralOperationsTensorComparisonSpec l E W G d := by
  obtain ⟨F, G, ⟨e⟩, ⟨d⟩⟩ := integralOperationsComparisonExists l E f W
  refine ⟨F, e, G, d, ?_, ?_⟩
  · intro F' e'
    obtain ⟨hL⟩ := good_whisker_fullyFaithful l E Y
      (DerivedCategory (integralTowerModules l E X))
    exact unique_comparison _ hL e e'
  · intro G' d'
    obtain ⟨hL⟩ := good_prod_whisker_fullyFaithful l E W
      (DerivedCategory (integralTowerModules l E W))
    exact unique_comparison _ hL d d'

end IntegralOperationsNormalizedDescentProof

section IntegralOperationsRoosDerivedLimitProof

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

/-- Transport a distinguished triangle's product vertices to the chosen product. -/
private theorem derivedLimit_of_product_triangle
    {A : Type a} [Category.{b} A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {K : ℕ → A} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (T : Pretriangulated.Triangle A) (hT : T ∈ distTriang A)
    (e₂ : T.obj₂ ≅ ∏ᶜ K) (e₃ : T.obj₃ ≅ ∏ᶜ K)
    (hs : T.mor₂ ≫ e₃.hom = e₂.hom ≫ towerTransitionEndomorphism f) :
    IsDerivedLimit f T.obj₁ := by
  refine ⟨T.mor₁ ≫ e₂.hom, e₃.inv ≫ T.mor₃, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk T
      (Pretriangulated.Triangle.mk (T.mor₁ ≫ e₂.hom)
        (towerTransitionEndomorphism f) (e₃.inv ≫ T.mor₃))
      (Iso.refl _) e₂ e₃ (by simp) hs (by simp))).mp hT

/-- The localized strict Roos complex has the derived-limit triangle.
Source: Stacks Project, Derived Categories, Tags 07KC and 08TC.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: exact countable products identify the localized product complex, with its
projections, with the product in the derived category. Checking each projection
identifies the localized endomorphism 1-s with the derived-category endomorphism.
The localized mapping-cocone triangle is distinguished. Transport its two product
vertices along this product comparison to get the required Roos triangle. -/
private theorem roos_derivedLimit
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    [HasDerivedCategory A] [CountableAB4Star A]
    [HasCountableProducts (DerivedCategory A)]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    IsDerivedLimit (K := fun n : ℕ ↦ DerivedCategory.Q.obj (C.obj (op n)))
      (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n))
      (DerivedCategory.Q.obj (integralOperationsRoos C)) := by
  classical
  let K := fun n : ℕ ↦ C.obj (op n)
  let P : Fan K := Fan.mk (∏ᶜ K) (Pi.π K)
  have hQ : IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor K))) :=
    (derivedCategory_countableProducts_core.{0} A).choose_spec.1 ℕ K |>.some
  have : PreservesLimit (Discrete.functor K) DerivedCategory.Q :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) hQ
  have hQP : IsLimit (DerivedCategory.Q.mapCone P) :=
    isLimitOfPreserves DerivedCategory.Q (productIsProduct K)
  let KD := fun n : ℕ ↦ DerivedCategory.Q.obj (K n)
  let hQFan := (Fan.isLimitMapConeEquiv DerivedCategory.Q K P) hQP
  let e : DerivedCategory.Q.obj P.pt ≅ ∏ᶜ KD :=
    hQFan.conePointUniqueUpToIso (productIsProduct KD)
  have he (n : ℕ) : e.hom ≫ Pi.π KD n = DerivedCategory.Q.map (P.proj n) :=
    hQFan.conePointUniqueUpToIso_hom_comp (productIsProduct KD) ⟨n⟩
  let s := towerTransitionEndomorphism (K := K) (integralOperationsTowerStep C)
  let sd := towerTransitionEndomorphism (K := KD)
    (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n))
  have hsπ (n : ℕ) : s ≫ P.proj n =
      P.proj n - P.proj (n + 1) ≫ integralOperationsTowerStep C n := by
    change s ≫ Pi.π K n = Pi.π K n - Pi.π K (n + 1) ≫ _
    simp [s, towerTransitionEndomorphism, towerProductShift]
  have hs : DerivedCategory.Q.map s ≫ e.hom = e.hom ≫ sd := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, ← Functor.map_comp, hsπ, Functor.map_sub]
    simp only [sd, towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, Pi.lift_comp_π, he]
    rw [Functor.map_comp, ← Category.assoc, he]
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle s)
  have hT : T ∈ distTriang (DerivedCategory A) :=
    DerivedCategory.mappingCocone_triangle_distinguished s
  exact derivedLimit_of_product_triangle (K := KD)
    (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n)) T hT e e hs

private theorem integralOperationsRoosDerivedLimit (W : AlgebraicGeometry.Scheme.{t})
    (C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) :
    integralOperationsDerivedLimitProperty l E W C
      (DerivedCategory.Q.obj (integralOperationsRoos C)) := by
  have := integralOperationsExactProducts l E W
  let : HasFiniteBiproducts (integralTowerModules l E W) := Abelian.hasFiniteBiproducts
  have := CountableAB4Star.of_hasExactLimitsOfShape_nat (integralTowerModules l E W)
  exact roos_derivedLimit C

end IntegralOperationsRoosDerivedLimitProof

section IntegralOperationsDerivedDescentProof

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsGoodComplex
  completedIntegralCoefficientSheafUnrestricted

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

set_option backward.isDefEq.respectTransparency false in
private theorem derivedLimit_of_iso
    {A : Type*} [Category* A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {K : ℕ → A} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    {L L' : A} (e : L ≅ L') (h : IsDerivedLimit f L') : IsDerivedLimit f L := by
  obtain ⟨p, δ, h⟩ := h
  refine ⟨e.hom ≫ p, δ ≫ (shiftFunctor A (1 : ℤ)).map e.inv, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk (e.hom ≫ p) (towerTransitionEndomorphism f)
        (δ ≫ (shiftFunctor A (1 : ℤ)).map e.inv))
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f) δ)
      e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp))).mpr h

set_option backward.isDefEq.respectTransparency true in
/-- Localization descent comparison for strict integral operations.
Source: Stacks Project, sites-cohomology.tex Tags 06YS, 06YT and 0G7E;
derived.tex Tags 08TC and 014A.
(blueprint: lem-pur-integral-operations-well-defined).

Proof: obtain the descended functors, natural comparisons, and both uniqueness
assertions from integralOperationsNormalizedDescent. For any chosen representative
isomorphism, apply the descended functor to its inverse and compose with the
comparison at that representative. This identifies the functor's value with the
localized strict Roos complex. The latter satisfies the derived-limit property by
integralOperationsRoosDerivedLimit. Transport its distinguished triangle along the
identification; explicitly precompose the first map by the identification and
postcompose the third map by the shifted inverse. For tensor use the product of
the two representative isomorphisms and repeat the same argument. -/
private theorem integralOperationsDerivedDescent
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{t}) :
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (e : integralOperationsGoodLocalization l E Y ⋙ F ≅
        integralOperationsPullbackOnGood l E f)
      (G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W))
      (d : ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W),
      integralOperationsPullbackComparisonSpec l E f F e ∧
      integralOperationsTensorComparisonSpec l E W G d ∧
      (∀ (K : DerivedCategory (integralTowerModules l E Y))
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (_e : DerivedCategory.Q.obj P.obj ≅ K),
        integralOperationsDerivedLimitProperty l E X
          ((integralOperationsPullbackTowerFunctor l E f).obj P.obj)
          (F.obj K)) ∧
      (∀ (M N : DerivedCategory (integralTowerModules l E W))
        (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
        (_e : DerivedCategory.Q.obj P.obj ≅ M) (_d : DerivedCategory.Q.obj Q.obj ≅ N),
        integralOperationsDerivedLimitProperty l E W
          ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
          (G.obj (M, N))) := by
  obtain ⟨F, e, G, d, hF, hG⟩ := integralOperationsNormalizedDescent l E f W
  refine ⟨F, e, G, d, hF, hG, ?_, ?_⟩
  · intro K P i
    let C := (integralOperationsPullbackTowerFunctor l E f).obj P.obj
    have h := integralOperationsRoosDerivedLimit l E X C
    let j : F.obj (DerivedCategory.Q.obj P.obj) ≅
        DerivedCategory.Q.obj (integralOperationsRoos C) := by
      have j := e.app P
      dsimp only [integralOperationsGoodLocalization, integralOperationsPullbackOnGood,
        Functor.comp_obj] at j
      unfold integralOperationsPullbackComplexFunctor at j
      exact j
    exact derivedLimit_of_iso (A := DerivedCategory (integralTowerModules l E X))
      (K := fun n : ℕ ↦ DerivedCategory.Q.obj (C.obj (op n)))
      (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n))
      ((F.mapIso i.symm) ≪≫ j) h
  · intro M N P Q i j
    let C := (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)
    have h := integralOperationsRoosDerivedLimit l E W C
    let ij : (M, N) ≅ (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) :=
      i.symm.prod j.symm
    let k : G.obj (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≅
        DerivedCategory.Q.obj (integralOperationsRoos C) := by
      have k := d.app (P, Q)
      dsimp only [integralOperationsGoodLocalization, integralOperationsTensorOnGood,
        Functor.comp_obj] at k
      unfold integralOperationsTensorComplexFunctor at k
      exact k
    exact derivedLimit_of_iso (A := DerivedCategory (integralTowerModules l E W))
      (K := fun n : ℕ ↦ DerivedCategory.Q.obj (C.obj (op n)))
      (fun n ↦ DerivedCategory.Q.map (integralOperationsTowerStep C n))
      ((G.mapIso ij) ≪≫ k) h

end IntegralOperationsDerivedDescentProof

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor integralOperationsDerivedLimitProperty
  integralOperationsGoodComplex integralOperationsGoodLocalization
  integralOperationsPullbackOnGood

/-- The two integral complex constructions preserve quasi-isomorphisms on K-flat
complexes with flat terms, descend to functors with natural representative comparisons,
and are unique up to the unique isomorphism compatible with those comparisons.
Their values are derived limits of the specified finite-level towers.
Source: Stacks Tags 06YS, 06YT, 0G7E, 08TC; Bhatt--Scholze,
Definition 3.4.10 and Lemma 6.5.9(4)
(blueprint: lem-pur-integral-operations-well-defined).

Proof:
1. Apply lem-pur-change-of-rings-kflat-quasi-iso to each completed coefficient
projection. The induced reductions of u,v are quasi-isomorphisms; by
lem-pur-kflat-change-of-rings all reduced complexes remain K-flat with flat terms.
No flatness of the coefficient projection is required.
2. prop-weil-pbc-proetale-constant-exact makes finite-level module pullback exact,
so it preserves these quasi-isomorphisms for every scheme morphism f. The site
version lem-weil-pbc-site-derived-tensor-descent identifies total tensors on K-flat
representatives with derived tensors; functoriality then proves the same assertion
for the tensor of the two reduced quasi-isomorphisms.
3. Restriction of scalars leaves the abelian sheaf and its cohomology unchanged.
The maps are strict maps of towers: on a tensor generator reducing then applying
u is the same as applying u then reducing, and similarly for v. The pullback
structure maps commute with reduction since their adjoints are the constant-section
maps. Thus the displayed pullback and tensor transition formulas commute with u,v.
4. Exact countable products on pro-etale module sheaves identify the termwise
products with derived products (lem-weil-proetale-countable-products-exact and
lemma-reduction-derived-nakayama). The shifted cone triangle is the Roos triangle
of def-weil-derived-limit, so each displayed value is a derived limit. The diagonal
product map is a morphism of Roos triangles. Its two product components are
isomorphisms; lem-weil-derived-limit-levelwise-iso makes its shifted-cone component
an isomorphism. Taking cohomology proves clause (1).
5. The complex constructions preserve identities and compositions. They respect
homotopies: additive coefficient change and inverse image preserve dh+hd. The total
tensor homotopy between u⊗v and u'⊗v' is h⊗v+(-1)^p u'⊗k on first degree p;
the mixed terms cancel. These homotopies commute with reduction. For the shifted
cone differential d(b,a)=(-db-(1-s)a,da), the product homotopy h gives
H(b,a)=(-hb,ha), and dH+Hd is the diagonal product difference.
6. lem-weil-pbc-site-derived-tensor-descent identifies localization of the good
homotopy representatives with the full derived category. Descend by
lem-weil-pbc-localization-universal-property, once for pullback and separately in
each variable for tensor. It extends natural transformations uniquely, giving the
natural comparisons e,d and their stated uniqueness. Inverting quasi-isomorphisms
in each tensor variable suffices since (u,v)=(u,1) followed by (1,v).
7. For any objectwise K-flat resolutions with flat terms from lem-pc-kflat-resolution,
Q(q_K) is invertible. Its inverse under F, followed by e on P_K, identifies F(K)
with Q(T_f(P_K)); use d in both variables for tensor. Transport the action on maps
by these identifications, i_L F(a) i_K⁻¹. Thus the displayed chosen-resolution
values themselves form functors without chosen chain-map lifts. For a second choice
use i'_K i_K⁻¹. The uniqueness just proved is uniqueness compatible with e,d,
not uniqueness of arbitrary morphisms completing triangles. The derived-limit
assertions are step 4 transported through the representative comparisons. -/
theorem integralOperationsWellDefined
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)
    (W : AlgebraicGeometry.Scheme.{t}) :
    (∀ (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (α : P.obj ⟶ P'.obj), QuasiIso α →
      QuasiIso ((integralOperationsPullbackComplexFunctor l E f).map α)) ∧
    (∀ (P P' Q Q' : (integralOperationsGoodComplex l E W).FullSubcategory)
      (α : P.obj ⟶ P'.obj) (β : Q.obj ⟶ Q'.obj), QuasiIso α → QuasiIso β →
      QuasiIso ((integralOperationsTensorComplexFunctor l E W).map
        (X := (P.obj, Q.obj)) (Y := (P'.obj, Q'.obj)) (α, β))) ∧
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (e : integralOperationsGoodLocalization l E Y ⋙ F ≅
        integralOperationsPullbackOnGood l E f)
      (G : (DerivedCategory (integralTowerModules l E W)) ×
        (DerivedCategory (integralTowerModules l E W)) ⥤
          DerivedCategory (integralTowerModules l E W))
      (d : ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ G ≅
          integralOperationsTensorOnGood l E W),
      (∀ (F' : DerivedCategory (integralTowerModules l E Y) ⥤
          DerivedCategory (integralTowerModules l E X))
        (e' : integralOperationsGoodLocalization l E Y ⋙ F' ≅
          integralOperationsPullbackOnGood l E f),
        ∃! ι : F ≅ F',
          isoWhiskerLeft (integralOperationsGoodLocalization l E Y) ι ≪≫ e' = e) ∧
      (∀ (G' : (DerivedCategory (integralTowerModules l E W)) ×
          (DerivedCategory (integralTowerModules l E W)) ⥤
            DerivedCategory (integralTowerModules l E W))
        (d' : ((integralOperationsGoodLocalization l E W).prod
          (integralOperationsGoodLocalization l E W)) ⋙ G' ≅
            integralOperationsTensorOnGood l E W),
        ∃! ι : G ≅ G', isoWhiskerLeft
          ((integralOperationsGoodLocalization l E W).prod
            (integralOperationsGoodLocalization l E W)) ι ≪≫ d' = d) ∧
      (∀ (K : DerivedCategory (integralTowerModules l E Y))
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (_e : DerivedCategory.Q.obj P.obj ≅ K),
        integralOperationsDerivedLimitProperty l E X
          ((integralOperationsPullbackTowerFunctor l E f).obj P.obj)
          (F.obj K)) ∧
      (∀ (M N : DerivedCategory (integralTowerModules l E W))
        (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
        (_e : DerivedCategory.Q.obj P.obj ≅ M) (_d : DerivedCategory.Q.obj Q.obj ≅ N),
        integralOperationsDerivedLimitProperty l E W
          ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
          (G.obj (M, N))) := by
  refine And.intro (integralOperationsPullbackQuasiIsoInvariant l E f) ?_
  refine And.intro (integralOperationsTensorQuasiIsoInvariant l E W) ?_
  exact integralOperationsDerivedDescent l E f W

end WeilConjectures
