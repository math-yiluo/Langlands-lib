/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.AlgebraicGeometry.SixFunctors.BundledTensorComparison
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-! # Uniqueness from ordinary tensor comparison

Source: Stacks 06YN and 07A4 (blueprint: lem-sf-tensor-comparison-model-uniqueness).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits
open WeilConjectures.SemilinearSections
namespace WeilConjectures.TensorModelUniqueness
variable {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf K CommRingCat.{max c v r})
  (F : WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} K S)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (A : WeilConjectures.SemilinearSections.Closed.{c, v, r} J R)
  (B : WeilConjectures.SemilinearSections.Closed.{c, v, r} K S)
  (TA : Models.{c, v, r} J R A) (TB : Models.{c, v, r} K S B)
  (mu nu : A.tensor ⋙ F.mapDerivedCategory ≅
    (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor)
  (M : TensorComparisonModel.{c, v, r} J K R S F A B TA TB mu)
  (N : TensorComparisonModel.{c, v, r} J K R S F A B TA TB nu)
private theorem chain_eq (ho : M.ordinary = N.ordinary)
    (P Q : CochainComplex
      (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) :
    M.chain P Q = N.chain P Q := by
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  apply HomologicalComplex.Hom.ext
  funext k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change tensorSummand.{c, v, r} K S _ _ p q k hpq ≫ _ =
    tensorSummand.{c, v, r} K S _ _ p q k hpq ≫ _
  rw [M.summand, N.summand, ho]

private theorem derived_eq (ho : M.ordinary = N.ordinary) : mu = nu := by
  suffices he : mu.inv = nu.inv by
    have hi : mu.symm = nu.symm := Iso.ext he
    exact congrArg Iso.symm hi
  obtain ⟨_, _, _, h⟩ := SheafOfModules.cochain_tensor_model_rigidity J R
  apply (h (DerivedCategory
    (WeilConjectures.SemilinearSections.Mod.{c, v, max c v r} K S)) inferInstance _ _).1
  apply NatTrans.ext
  funext X
  rcases X with ⟨P, Q⟩
  change mu.inv.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
    nu.inv.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
  have hm := M.derived P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2
  have hn := N.derived P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2
  have hc := chain_eq.{c, v, r} J K R S F A B TA TB mu nu M N ho P.obj Q.obj
  rw [hc] at hm
  have he := hm.trans hn.symm
  let a := tensorModelIso.{c, v, r} K S B TB _ _
    (M.kflat P.obj P.property.1 P.property.2)
    (M.kflat Q.obj Q.property.1 Q.property.2)
  let b := B.tensor.mapIso (Iso.prod ((Functor.mapDerivedCategoryFactors F).app P.obj)
    ((Functor.mapDerivedCategoryFactors F).app Q.obj)).symm
  let d := F.mapDerivedCategory.mapIso
    (tensorModelIso.{c, v, r} J R A TA P.obj Q.obj P.property.1 Q.property.1).symm
  let e := (Functor.mapDerivedCategoryFactors F).app
    ((totalTensor.{c, v, r} J R).obj (P.obj, Q.obj))
  have he' : a.hom ≫ b.hom ≫ mu.inv.app (DerivedCategory.Q.obj P.obj,
        DerivedCategory.Q.obj Q.obj) ≫ d.hom ≫ e.hom =
      a.hom ≫ b.hom ≫ nu.inv.app (DerivedCategory.Q.obj P.obj,
        DerivedCategory.Q.obj Q.obj) ≫ d.hom ≫ e.hom := he
  have hi := congrArg (fun z ↦ b.inv ≫ a.inv ≫ z ≫ e.inv ≫ d.inv) he'
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using hi

/-- The ordinary map determines its total and derived comparison.
Source: Stacks 06YN and 07A4 (blueprint: lem-sf-tensor-comparison-model-uniqueness).
Proof: the summand formula and the universal property of the total direct sum
identify the chain maps. Substitute in the two representative equations and
cancel all four invertible comparison factors. Cochain tensor rigidity extends
the resulting equality of derived natural transformations to every pair of
objects. Finally proof irrelevance identifies the remaining model fields. -/
theorem tensorComparisonModel_unique (ho : M.ordinary = N.ordinary) :
    mu = nu ∧ HEq M N := by
  have hm := derived_eq.{c, v, r} J K R S F A B TA TB mu nu M N ho
  refine ⟨hm, ?_⟩
  subst nu
  have hc : M.chain = N.chain := by
    funext P Q
    exact chain_eq.{c, v, r} J K R S F A B TA TB mu mu M N ho P Q
  cases M
  cases N
  dsimp only at ho hc
  cases ho
  cases hc
  rfl
/-- Bundle extensionality is checked with an abstract exact functor. -/
private theorem bundled_unique
    (M' N' : BundledTensorComparison.{c, v, r} J K R S F A B TA TB)
    (ho : M'.model.ordinary = N'.model.ordinary) : M' = N' := by
  obtain ⟨hm, hmodel⟩ := tensorComparisonModel_unique.{c, v, r}
    J K R S F A B TA TB M'.mu N'.mu M'.model N'.model ho
  cases M'
  cases N'
  dsimp only at hm hmodel
  cases hm
  cases hmodel
  rfl

end WeilConjectures.TensorModelUniqueness
