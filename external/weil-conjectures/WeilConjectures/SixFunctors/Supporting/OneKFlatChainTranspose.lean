/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Chain transposition with one K-flat tensor factor

Source: Stacks Project, Cohomology on Sites, Tags 08J9, 06YP, 06YT, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose).
The comparison extends the fixed two-K-flat normalization. The first complex is
arbitrary and unbounded. Hom uses the recorded product projections, and the pure
sections are the actual sheafification-unit and direct-sum generators.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
  (T : CoefficientTensorModels.{u, c, v, w} J R S)

/-- The arbitrary-first-factor tensor comparison.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainComparison :=
  ∀ (A P : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ),
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P.X n)) →
  (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (A, P)) ≅
    S.tensor.obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj P))

/-- Agreement with the fixed normalization on two K-flat representatives.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainComparisonNormalization
    (comparison : OneKFlatChainComparison.{c, v, u, w} J R S) : Prop :=
  ∀ (A P : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (hA : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) A)
  (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P)
  (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P.X n)),
  comparison A P hP hflat = T.iso J R S A P hA hP

/-- Naturality in the arbitrary first factor and the allowed second factor.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainComparisonNaturality
    (comparison : OneKFlatChainComparison.{c, v, u, w} J R S) : Prop :=
  ∀ (A A' P P' : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P)
  (hP' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P')
  (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P.X n))
  (hflat' : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P'.X n))
  (a : A ⟶ A') (b : P ⟶ P'),
  DerivedCategory.Q.map ((coefficientTotalTensor.{u, c, v} J R).map (Prod.mkHom a b)) ≫
      (comparison A' P' hP' hflat').hom =
    (comparison A P hP hflat).hom ≫
      S.tensor.map (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b))

/-- Ordinary chain uncurrying into a K-injective target.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainUncurry :=
  ∀ (A P : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ),
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P.X n)) →
  ∀ E : CochainComplex (SheafOfModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ,
    E.IsKInjective →
  (A ⟶ homComplex.{c, v, max c v u, max c v u} (R := R) P E) →
  ((coefficientTotalTensor.{u, c, v} J R).obj (A, P) ⟶ E)

/-- No sign is introduced in the ordered tensor A,P.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainUncurryPure
    (uncurry : OneKFlatChainUncurry.{c, v, u} J R) : Prop :=
  ∀ (A P E : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P)
  (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P.X n))
  (hE : E.IsKInjective) (f : A ⟶ homComplex.{c, v, max c v u, max c v u} (R := R) P E)
  (n m k : ℤ) (h : n + m = k) (h' : m + n = k) (U : Cᵒᵖ)
  (x : (A.X n).val.obj U) (y : (P.X m).val.obj U),
  ((uncurry A P hP hflat E hE f).f k).val.app U
      (coefficientTensorGenerator.{u, c, v} J R A P n m k h U x y) =
    (((coefficientHomComponent.{u, c, v} J R P E n m k h').val.app U
      ((f.f n).val.app U x)).app (op (Over.mk (𝟙 U.unop)))).hom y

/-- The fixed derived transpose is represented by this chain map.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainTransposeEquation
    (comparison : OneKFlatChainComparison.{c, v, u, w} J R S)
    (uncurry : OneKFlatChainUncurry.{c, v, u} J R) : Prop :=
  ∀ (A P E : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P)
  (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P.X n))
  (hE : E.IsKInjective) (f : A ⟶ homComplex.{c, v, max c v u, max c v u} (R := R) P E),
  (comparison A P hP hflat).hom ≫
      (S.transpose (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj E)).symm
          (DerivedCategory.Q.map f ≫
            DerivedCategory.Q.map
              (((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op P)).map
                (CategoryTheory.coefficientHomAugmentation.{c, v, u} J R E)) ≫
            (coefficientHomResolutionIso.{u, c, v, w} J R P E).inv) =
    DerivedCategory.Q.map (uncurry A P hP hflat E hE f)

/-- Simultaneous chain naturality, with the Hom source contravariant.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainUncurryNaturality
    (uncurry : OneKFlatChainUncurry.{c, v, u} J R) : Prop :=
  ∀ (A' A P' P E E' : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P)
  (hP' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P')
  (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P.X n))
  (hflat' : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R)
    (P'.X n))
  (hE : E.IsKInjective) (hE' : E'.IsKInjective)
  (a : A' ⟶ A) (b : P' ⟶ P) (e : E ⟶ E')
  (f : A ⟶ homComplex.{c, v, max c v u, max c v u} (R := R) P E),
  uncurry A' P' hP' hflat' E' hE'
      (a ≫ f ≫ ((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).map b.op).app E ≫
        ((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op P')).map e) =
    (coefficientTotalTensor.{u, c, v} J R).map (Prod.mkHom a b) ≫
      uncurry A P hP hflat E hE f ≫ e

/-- All tensor representative quasi-isomorphisms become invertible, even in P.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainTensorInverts : Prop :=
  ∀ (A A' P P' : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (a : A ⟶ A') (b : P ⟶ P'),
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P →
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P' →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P.X n)) →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P'.X n)) →
  QuasiIso a → QuasiIso b →
  IsIso (DerivedCategory.Q.map
    ((coefficientTotalTensor.{u, c, v} J R).map (Prod.mkHom a b)))

/-- Hom representative quasi-isomorphisms become invertible.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainHomInverts : Prop :=
  ∀ (P P' E E' : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
  (b : P' ⟶ P) (e : E ⟶ E'),
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P →
  CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (R := R) P' →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P.X n)) →
  (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := R) (P'.X n)) →
  E.IsKInjective → E'.IsKInjective → QuasiIso b → QuasiIso e →
  IsIso (DerivedCategory.Q.map
    (((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).map b.op).app E ≫
      ((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op P')).map e))

/-- The Hom identification used in transpose_eq is itself an isomorphism.
Source: Stacks 08J9, 06YU and 0A90
(blueprint: lem-sfb-hom-kflat-chain-transpose). -/
def OneKFlatChainHomComparisonIsIso : Prop :=
  ∀ (P E : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ),
  E.IsKInjective → IsIso
    (DerivedCategory.Q.map
        (((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op P)).map
          (CategoryTheory.coefficientHomAugmentation.{c, v, u} J R E)) ≫
      (coefficientHomResolutionIso.{u, c, v, w} J R P E).inv)

/-- The simultaneous one-K-flat comparison and its chain representatives, with their
normalization and all representative compatibility equations. This structure only
packages the conclusion; it supplies no additional hypothesis on a complex.
Source: Stacks 08J9, 06YU and 0A90 (blueprint: lem-sfb-hom-kflat-chain-transpose). -/
structure OneKFlatChainTransposeData where
  /-- The arbitrary-first-factor tensor comparison. -/
  comparison : OneKFlatChainComparison.{c, v, u, w} J R S
  /-- Agreement with the fixed normalization on two K-flat representatives. -/
  comparison_normalization : OneKFlatChainComparisonNormalization.{c, v, u, w} J R S T comparison
  /-- Naturality in the arbitrary first factor and the allowed second factor. -/
  comparison_naturality : OneKFlatChainComparisonNaturality.{c, v, u, w} J R S comparison
  /-- Ordinary chain uncurrying into a K-injective target. -/
  uncurry : OneKFlatChainUncurry.{c, v, u} J R
  /-- No sign is introduced in the ordered tensor A,P. -/
  uncurry_pure : OneKFlatChainUncurryPure.{c, v, u} J R uncurry
  /-- The fixed derived transpose is represented by this chain map. -/
  transpose_eq : OneKFlatChainTransposeEquation.{c, v, u, w} J R S comparison uncurry
  /-- Simultaneous chain naturality, with the Hom source contravariant. -/
  uncurry_naturality : OneKFlatChainUncurryNaturality.{c, v, u} J R uncurry
  /-- All tensor representative quasi-isomorphisms become invertible, even in P. -/
  tensor_inverts : OneKFlatChainTensorInverts.{c, v, u, w} J R
  /-- Hom representative quasi-isomorphisms become invertible. -/
  hom_inverts : OneKFlatChainHomInverts.{c, v, u, w} J R
  /-- The Hom identification used in transpose_eq is itself an isomorphism. -/
  hom_comparison_isIso : OneKFlatChainHomComparisonIsIso.{c, v, u, w} J R
  /-- Factor interchange is the actual Koszul braiding, with sign (-1)^(n*m). -/
  interchange_sign : CategoryTheory.RingedDerivedNative.symmetryPure.{c, v, u} J R

section

set_option maxRecDepth 1024
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace OneKFlatAux

open CategoryTheory.RingedDerivedNative

attribute [local instance 1000001] CategoryTheory.RingedDerivedNative.cachedCompose
attribute [local irreducible] SheafOfModules.monoidalCategory homComplexFunctor

private abbrev Mod := SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)

private abbrev Complex := CochainComplex (Mod.{c, v, u} J R) ℤ

private noncomputable def rawTensor (P : Complex.{c, v, u} J R) :=
  Prod.sectL (Complex.{c, v, u} J R) P ⋙ coefficientTotalTensor.{u, c, v} J R ⋙
    DerivedCategory.Q.{w}

private noncomputable def derivedTensor (P : Complex.{c, v, u} J R) :=
  DerivedCategory.Q.{w} ⋙
    Prod.sectL (DerivedCategory (Mod.{c, v, u} J R)) (DerivedCategory.Q.obj P) ⋙ S.tensor

private theorem rawTensor_inverts (P : Complex.{c, v, u} J R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    (HomologicalComplex.quasiIso (Mod.{c, v, u} J R) (.up ℤ)).IsInvertedBy
      (rawTensor.{c, v, u, w} J R P) := by
  intro A B a ha
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let F := (CategoryTheory.MonoidalCategory.curriedTensor (Mod.{c, v, u} J R)).map₂CochainComplex
  change QuasiIso ((F.map a).app P ≫ (F.obj B).map (𝟙 P))
  rw [(F.obj B).map_id, Category.comp_id]
  exact kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP a ha

private noncomputable def restrictRight
    {K A B D : Type*} [Category K] [Category A] [Category B] [Category D]
    (I : K ⥤ A) (Q : A ⥤ B) (H : A × A ⥤ D) (G : B × B ⥤ D)
    (e : (I.prod I) ⋙ H ≅ ((I ⋙ Q).prod (I ⋙ Q)) ⋙ G) (P : K) :
    I ⋙ Prod.sectL A (I.obj P) ⋙ H ≅
      I ⋙ Q ⋙ Prod.sectL B (Q.obj (I.obj P)) ⋙ G :=
  NatIso.ofComponents (fun X ↦ e.app (X, P)) (by
    intro X Y f
    have h := e.hom.naturality (X := (X, P)) (Y := (Y, P)) (f, 𝟙 P)
    dsimp only [Functor.comp_map, Functor.prod_map] at h
    rw [I.map_id, Q.map_id] at h
    exact h)

private theorem restrictLeft_naturality
    {K A B D : Type*} [Category K] [Category A] [Category B] [Category D]
    (I : K ⥤ A) (Q : A ⥤ B) (H : A × A ⥤ D) (G : B × B ⥤ D)
    (e : (I.prod I) ⋙ H ≅ ((I ⋙ Q).prod (I ⋙ Q)) ⋙ G)
    (P X Y : K) (f : X ⟶ Y) :
    H.map (Prod.mkHom (𝟙 (I.obj P)) (I.map f)) ≫ (e.app (P, Y)).hom =
      (e.app (P, X)).hom ≫
        G.map (Prod.mkHom (𝟙 (Q.obj (I.obj P))) (Q.map (I.map f))) := by
  have h := e.hom.naturality (X := (P, X)) (Y := (P, Y)) (𝟙 P, f)
  dsimp only [Functor.comp_map, Functor.prod_map] at h
  rw [I.map_id, Q.map_id] at h
  exact h

private theorem map_pair_square
    {A B D : Type*} [Category A] [Category B] [Category D]
    (G : A × B ⥤ D) {X X' : A} {Y Y' : B} (f : X ⟶ X') (g : Y ⟶ Y') :
    G.map (Prod.mkHom (𝟙 X) g) ≫ G.map (Prod.mkHom f (𝟙 Y')) =
      G.map (Prod.mkHom f (𝟙 Y)) ≫ G.map (Prod.mkHom (𝟙 X') g) := by
  rw [← G.map_comp, ← G.map_comp]
  congr 1
  apply Prod.hom_ext
  · exact (Category.id_comp f).trans (Category.comp_id f).symm
  · exact (Category.comp_id g).trans (Category.id_comp g).symm

private theorem map_pair_factor
    {A B D : Type*} [Category A] [Category B] [Category D]
    (G : A × B ⥤ D) {X X' : A} {Y Y' : B} (f : X ⟶ X') (g : Y ⟶ Y') :
    G.map (Prod.mkHom f (𝟙 Y)) ≫ G.map (Prod.mkHom (𝟙 X') g) =
      G.map (Prod.mkHom f g) := by
  rw [← G.map_comp]
  congr 1
  apply Prod.hom_ext
  · exact Category.comp_id f
  · exact Category.id_comp g

private noncomputable def restrictedComparison (P : Complex.{c, v, u} J R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    coefficientKFlatInclusion.{u, c, v} J R ⋙ rawTensor.{c, v, u, w} J R P ≅
      coefficientKFlatInclusion.{u, c, v} J R ⋙ derivedTensor.{c, v, u, w} J R S P :=
  restrictRight (coefficientKFlatInclusion.{u, c, v} J R) DerivedCategory.Q
    (coefficientTotalTensor.{u, c, v} J R ⋙ DerivedCategory.Q) S.tensor T.comparison ⟨P, hP⟩

@[no_expose, irreducible]
private noncomputable def extendIso
    {A B E K : Type*} [Category A] [Category B] [Category E] [Category K]
    (W : MorphismProperty A) (Q : A ⥤ B) [Q.IsLocalization W]
    (I : K ⥤ A) [(I ⋙ Q).IsLocalization (W.inverseImage I)]
    (F : B ⥤ E) (H : A ⥤ E) (hH : W.IsInvertedBy H)
    (e : I ⋙ H ≅ I ⋙ Q ⋙ F) :
    { c : H ≅ Q ⋙ F // ∀ X, c.app (I.obj X) = e.app X } := by
  let H' := Localization.lift H hH Q
  let φ := Localization.fac H hH Q
  let b : (I ⋙ Q) ⋙ H' ≅ (I ⋙ Q) ⋙ F := Functor.isoWhiskerLeft I φ ≪≫ e
  let ff := Localization.fullyFaithfulWhiskeringLeft (I ⋙ Q) (W.inverseImage I) E
  let b' := ff.preimageIso b
  refine ⟨φ.symm ≪≫ Functor.isoWhiskerLeft Q b', ?_⟩
  intro X
  apply Iso.ext
  have hb := congr_app (ff.map_preimage b.hom) X
  change φ.inv.app (I.obj X) ≫ b'.hom.app (Q.obj (I.obj X)) = (e.app X).hom
  rw [show b'.hom.app (Q.obj (I.obj X)) = b.hom.app X from hb]
  simp [b]

@[no_expose, irreducible]
private noncomputable def extendedComparison (P : Complex.{c, v, u} J R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    { c : rawTensor.{c, v, u, w} J R P ≅ derivedTensor.{c, v, u, w} J R S P //
      ∀ A : ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)),
        c.app A.obj = T.iso J R S A.obj P A.property hP } := by
  let := kFlatLocalization.{c, v, u, w} J R
  exact extendIso
    (HomologicalComplex.quasiIso (Mod.{c, v, u} J R) (.up ℤ)) DerivedCategory.Q
    (coefficientKFlatInclusion.{u, c, v} J R)
    (Prod.sectL (DerivedCategory (Mod.{c, v, u} J R)) (DerivedCategory.Q.obj P) ⋙ S.tensor)
    (rawTensor.{c, v, u, w} J R P) (rawTensor_inverts.{c, v, u, w} J R P hP)
    (restrictedComparison.{c, v, u, w} J R S T P hP)

@[no_expose, irreducible]
private noncomputable def comparison : OneKFlatChainComparison.{c, v, u, w} J R S :=
  fun A P hP _ ↦ (extendedComparison.{c, v, u, w} J R S T P hP).val.app A

private theorem comparison_normalization :
    OneKFlatChainComparisonNormalization.{c, v, u, w} J R S T
      (comparison.{c, v, u, w} J R S T) := by
  intro A P hA hP hflat
  unfold comparison
  exact (extendedComparison.{c, v, u, w} J R S T P hP).property ⟨A, hA⟩

private theorem comparison_left (A A' P : Complex.{c, v, u} J R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n))
    (a : A ⟶ A') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{u, c, v} J R).map
      (X := (A, P)) (Y := (A', P)) (a, 𝟙 P)) ≫
        (comparison.{c, v, u, w} J R S T A' P hP hflat).hom =
      (comparison.{c, v, u, w} J R S T A P hP hflat).hom ≫
        S.tensor.map (Prod.mkHom (DerivedCategory.Q.map a) (𝟙 (DerivedCategory.Q.obj P))) := by
  unfold comparison
  exact (extendedComparison.{c, v, u, w} J R S T P hP).val.hom.naturality a

private theorem comparison_right (A P P' : Complex.{c, v, u} J R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P')
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X n))
    (hflat' : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P'.X n))
    (b : P ⟶ P') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{u, c, v} J R).map
      (X := (A, P)) (Y := (A, P')) (𝟙 A, b)) ≫
        (comparison.{c, v, u, w} J R S T A P' hP' hflat').hom =
      (comparison.{c, v, u, w} J R S T A P hP hflat).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj A)) (DerivedCategory.Q.map b)) := by
  obtain ⟨F, q, hF, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients A
  let Q := DerivedCategory.Q.{w} (C := Mod.{c, v, u} J R)
  let B := coefficientTotalTensor.{u, c, v} J R
  let c := comparison.{c, v, u, w} J R S T
  have hi : IsIso (Q.map (B.map (X := (F, P)) (Y := (A, P)) (q, 𝟙 P))) :=
    rawTensor_inverts.{c, v, u, w} J R P hP q hq
  have sq :
      Q.map (B.map (X := (F, P)) (Y := (A, P)) (q, 𝟙 P)) ≫
        Q.map (B.map (X := (A, P)) (Y := (A, P')) (𝟙 A, b)) =
      Q.map (B.map (X := (F, P)) (Y := (F, P')) (𝟙 F, b)) ≫
        Q.map (B.map (X := (F, P')) (Y := (A, P')) (q, 𝟙 P')) := by
    rw [← Q.map_comp, ← Q.map_comp, ← B.map_comp, ← B.map_comp]
    congr 2
  have hn : Q.map (B.map (X := (F, P)) (Y := (F, P')) (𝟙 F, b)) ≫
        (c F P' hP' hflat').hom =
      (c F P hP hflat).hom ≫ S.tensor.map (Prod.mkHom (𝟙 (Q.obj F)) (Q.map b)) := by
    dsimp only [c]
    rw [comparison_normalization.{c, v, u, w} J R S T F P' hF hP' hflat',
      comparison_normalization.{c, v, u, w} J R S T F P hF hP hflat]
    exact restrictLeft_naturality (coefficientKFlatInclusion.{u, c, v} J R)
      Q (B ⋙ Q) S.tensor T.comparison ⟨F, hF⟩ ⟨P, hP⟩ ⟨P', hP'⟩
      (ObjectProperty.homMk b)
  apply (cancel_epi (Q.map (B.map (X := (F, P)) (Y := (A, P)) (q, 𝟙 P)))).1
  change _ ≫ (_ ≫ (c A P' hP' hflat').hom) =
    _ ≫ ((c A P hP hflat).hom ≫ _)
  calc
    _ = Q.map (B.map (X := (F, P)) (Y := (F, P')) (𝟙 F, b)) ≫
        (Q.map (B.map (X := (F, P')) (Y := (A, P')) (q, 𝟙 P')) ≫
          (c A P' hP' hflat').hom) := by
      rw [← Category.assoc, sq, Category.assoc]
    _ = Q.map (B.map (X := (F, P)) (Y := (F, P')) (𝟙 F, b)) ≫
        ((c F P' hP' hflat').hom ≫
          S.tensor.map (Prod.mkHom (Q.map q) (𝟙 (Q.obj P')))) := by
      rw [comparison_left.{c, v, u, w} J R S T F A P' hP' hflat' q]
    _ = (c F P hP hflat).hom ≫
        (S.tensor.map (Prod.mkHom (𝟙 (Q.obj F)) (Q.map b)) ≫
          S.tensor.map (Prod.mkHom (Q.map q) (𝟙 (Q.obj P')))) := by
      rw [← Category.assoc, hn, Category.assoc]
    _ = (c F P hP hflat).hom ≫
        (S.tensor.map (Prod.mkHom (Q.map q) (𝟙 (Q.obj P))) ≫
          S.tensor.map (Prod.mkHom (𝟙 (Q.obj A)) (Q.map b))) := by
      exact congrArg (fun t ↦ (c F P hP hflat).hom ≫ t)
        (map_pair_square S.tensor (Q.map q) (Q.map b))
    _ = _ := by
      rw [← Category.assoc,
        ← comparison_left.{c, v, u, w} J R S T F A P hP hflat q, Category.assoc]

private theorem comparison_naturality :
    OneKFlatChainComparisonNaturality.{c, v, u, w} J R S
      (comparison.{c, v, u, w} J R S T) := by
  intro A A' P P' hP hP' hflat hflat' a b
  let B := coefficientTotalTensor.{u, c, v} J R
  have hmap : B.map (Prod.mkHom a b) =
      B.map (X := (A, P)) (Y := (A', P)) (a, 𝟙 P) ≫
        B.map (X := (A', P)) (Y := (A', P')) (𝟙 A', b) := by
    rw [← B.map_comp]
    congr 1
  rw [hmap, Functor.map_comp, Category.assoc,
    comparison_right.{c, v, u, w} J R S T A' P P' hP hP' hflat hflat' b,
    ← Category.assoc, comparison_left.{c, v, u, w} J R S T A A' P hP hflat a]
  rw [Category.assoc, map_pair_factor]

include S T in
private theorem tensor_inverts : OneKFlatChainTensorInverts.{c, v, u, w} J R := by
  intro A A' P P' a b hP hP' hflat hflat' ha hb
  have := ha
  have := hb
  have : IsIso (DerivedCategory.Q.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 ha
  have : IsIso (DerivedCategory.Q.map b) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hb
  have hn := comparison_naturality.{c, v, u, w} J R S T
    A A' P P' hP hP' hflat hflat' a b
  have : IsIso (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (S.tensor.map
      (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b))) :=
    S.tensor.map_isIso _
  have : IsIso (DerivedCategory.Q.map
      ((coefficientTotalTensor.{u, c, v} J R).map (Prod.mkHom a b)) ≫
        (comparison.{c, v, u, w} J R S T A' P' hP' hflat').hom) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (comparison.{c, v, u, w} J R S T A' P' hP' hflat').hom

private theorem hom_inverts : OneKFlatChainHomInverts.{c, v, u, w} J R := by
  intro P P' E E' b e hP hP' hflat hflat' hE hE' hb he
  have := hE
  have := hE'
  have := hb
  have := he
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_homComplex_mapOfUniverses.{c, v, u} e b)

private theorem hom_comparison_isIso : OneKFlatChainHomComparisonIsIso.{c, v, u, w} J R := by
  intro P E hE
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J R).1
  have := hE
  have : ((coefficientHomResolution.{u, c, v} J R).obj E).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v u} _ E
  have : QuasiIso (CategoryTheory.coefficientHomAugmentation.{c, v, u} J R E) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ E).2
  have h := quasiIso_homComplex_mapOfUniverses.{c, v, u}
    (CategoryTheory.coefficientHomAugmentation.{c, v, u} J R E) (𝟙 P)
  rw [op_id, (homComplexFunctor (R := R)).map_id, NatTrans.id_app,
    Category.id_comp] at h
  have : IsIso (DerivedCategory.Q.map
      (((homComplexFunctor.{c, v, max c v u, max c v u} (R := R)).obj (op P)).map
        (CategoryTheory.coefficientHomAugmentation.{c, v, u} J R E))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h
  infer_instance

private theorem augmentation_eq (E : Complex.{c, v, u} J R) :
    (WeilConjectures.coefficientHomAugmentation.{u, c, v} J R).app E =
      CategoryTheory.coefficientHomAugmentation.{c, v, u} J R E := by
  unfold WeilConjectures.coefficientHomAugmentation
    CategoryTheory.coefficientHomAugmentation
  rfl

end OneKFlatAux

end

end WeilConjectures
