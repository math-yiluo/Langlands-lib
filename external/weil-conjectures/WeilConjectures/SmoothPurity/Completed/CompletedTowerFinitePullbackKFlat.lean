/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
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
import all WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
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
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleEnoughPoints
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.Sites.FinitarySliceEnoughPoints
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.AlgebraicGeometry.FinitarySiteEnoughPoints
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import WeilConjectures.CategoryTheory.Sites.PointSystemSaturation
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.PointSystemRefineAll
import WeilConjectures.CategoryTheory.PointSystemRefinementMap
import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.AlgebraicGeometry.PointSystemRefine
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.PointSystemRefinementChainExists
import WeilConjectures.CategoryTheory.PointSystemChain
import Mathlib.Order.Directed
import WeilConjectures.CategoryTheory.PointSystemExtensions
import WeilConjectures.CategoryTheory.PointSystemDiagram
import Mathlib.Order.Category.PartOrdEmb
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.Order.Hom.Set
import WeilConjectures.CategoryTheory.PointSystemPosetalRefine
import WeilConjectures.CategoryTheory.PointSystemPosetalReplacement
import Mathlib.Order.Antisymmetrization
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.PointSystemSchedule
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.CategoryTheory.Filtered.Grothendieck
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Sites.PointFamilyConservative
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import WeilConjectures.TraceFormula.InverseSystemSitePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.Algebra.Homology.AlgebraicInverseImageKFlat
import WeilConjectures.Algebra.Homology.RingedSiteKFlatStalkCriterion
import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Homology.RingedSitePointUniversalTensor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.Algebra.Homology.RingedSitePointTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.PUnit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Homology.RingedSitePointExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Homology.RingedSitePointFinitePresentationRetract
import Mathlib.CategoryTheory.Retract
import WeilConjectures.CategoryTheory.Sites.InverseImageFreeModule
import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
import WeilConjectures.CategoryTheory.Sites.NormalizedFreeModuleComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Finsupp.Pi
import WeilConjectures.Algebra.Homology.RingedSitePointKFlatResolution
import WeilConjectures.Algebra.Homology.RingedSitePointFlat
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Algebra.Homology.RingedSitePointAcyclic
import WeilConjectures.Algebra.Homology.UniversalAcyclicModuleKFlat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.ModuleDirectedColimitFinitePresentation
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

/-! # Arbitrary K-flatness for the actual finite tower pullback

Source: Stacks Project, Cohomology on Sites, Tags 0DEN and 0DEP.
(blueprint: lem-pur-completed-tower-finite-pullback-kflat)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- The actual finite pullback in the strict tower preserves every K-flat complex.
Source: Stacks 0DEN and 0DEP
(blueprint: lem-pur-completed-tower-finite-pullback-kflat).
Proof: use the specified algebraic inverse image on the pro-etale topoi. The
conservative family of target points and the stalk criterion preserve K-flatness.
Scalar extension along the constant-ring comparison also preserves K-flatness.
The right adjoint of this composite has exactly the constant-section coefficient
map used by coefficientProEtaleModuleDirectImage. The adjunction Hom equivalence
identifies these maps. Uniqueness of left adjoints therefore compares the
composite with integralOperationsLevelPullback. Apply that natural isomorphism
degreewise and transport acyclicity of every total tensor test. No flat-term,
boundedness, constructibility or invertibility hypothesis is used. -/
theorem completedTowerFinitePullbackKFlat {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y n) P) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology X) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : HasSheafify (ProEt.topology Y) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
      u + 1, u + 1, u + 2, u + 1} _
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
      u + 1, u + 1, u + 2, u + 1} _
  let A : Type u := Padic.coefficientExtensionRing l E (n + 1)
  let R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1} :=
    integralCoefficientCommRingSheaf l E Y n
  let S : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
    integralCoefficientCommRingSheaf l E X n
  let RI : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
  let c : RI ≅ S := proEtaleConstantRingComparison.{u} f A
  let geom : GeometricMorphism
      (Sheaf (ProEt.topology X) (Type (u + 1)))
      (Sheaf (ProEt.topology Y) (Type (u + 1))) :=
    { inverse := proEtaleSheafInverseImage f (Type (u + 1))
      direct := proEtaleSheafDirectImage f (Type (u + 1))
      adj := proEtaleSheafAdjunction f (Type (u + 1))
      leftExact := (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1 }
  let I := SheafOfModules.inverseImageOfUniverses (normalizedAlgebraicLift f R)
  let : Limits.PreservesFiniteLimits (proEtaleModuleInverseImage f R) :=
    proEtaleModuleInverseImage_preservesFiniteLimits f R
  have : (proEtaleModuleInverseImage f R).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : I.modules.Additive := inferInstanceAs (proEtaleModuleInverseImage f R).Additive
  obtain ⟨ι, p, hp⟩ := proEtale_enoughPoints.{u, u} X
  let s : ∀ i, RingedSitePoint RI (p i) :=
    fun i ↦ Classical.choice (RingedSitePoint.nonempty _ (p i))
  have hcons : JointlyReflectIsomorphisms (fun i ↦ (p i).inverse) := by
    constructor
    intro M N a _
    exact hp a (fun i ↦ (isIso_iff_bijective ((p i).inverse.map a)).1 inferInstance)
  have hI := SheafOfModules.AlgebraicInverseImageOfUniverses.isKFlat_of_points
    (ProEt.topology Y) (ProEt.topology X) geom I ι p s hcons P hP
  let F := proEtaleRingExtension f R S c
  let : Limits.PreservesFiniteLimits F := proEtaleRingExtension_preservesFiniteLimits f R S c
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have hF := SheafOfModules.changeOfRings_isKFlat_independentCoefficients c.hom
    ((I.modules.mapHomologicalComplex (.up ℤ)).obj P) F
    (fun _ ↦ rfl) (fun g ↦ by
      change F.map g = 𝟙 _ ≫ SheafOfModules.changeOfRingsHom c.hom _ g ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      rfl) hI
  have hc : proEtaleRingDirectImageMap f R S c =
      proEtaleCoefficientDirectImageMap f A :=
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
      (proEtaleCoefficientDirectImageMap f A)
  let d : proEtaleRingModuleDirectImage f R S c ≅
      coefficientProEtaleModuleDirectImage.{u, u} f
        (CommRingCat.of (ULift.{u + 1} A)) :=
    SheafOfModules.pushforwardCongr (by rw [hc]; rfl)
  let adj := (proEtaleRingModuleAdjunction f R S c).ofNatIsoRight d
  let e₀ : proEtaleRingModulePullback f R S c ≅ integralOperationsLevelPullback l E f n :=
    adj.leftAdjointUniq (coefficientProEtaleModuleAdjunction.{u, u} f
      (CommRingCat.of (ULift.{u + 1} A)))
  have : (integralOperationsLevelPullback l E f n).Additive :=
    integralOperationsLevelPullback_additive l E f n
  let : (integralOperationsLevelPullback l E f n).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let e : ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P ≅
      ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj P :=
    HomologicalComplex.Hom.isoOfComponents (fun k ↦ e₀.app (P.X k))
      (fun i j _ ↦ (e₀.hom.naturality (P.d i j)).symm)
  let B := S
  let := SheafOfModules.isMonoidal_W_independentCoefficients B
  let := SheafOfModules.monoidalCategory B
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients B
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients B
  intro Q hQ i
  exact (hF Q hQ i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj Q).mapIso e)

end WeilConjectures
