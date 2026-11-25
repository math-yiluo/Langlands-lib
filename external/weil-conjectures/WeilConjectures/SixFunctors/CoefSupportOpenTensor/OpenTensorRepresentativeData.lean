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
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Normalized one-K-flat open tensor representative data

Source: Stacks 0E8I, 0GL1, 07A4 and 06YT; blueprint main-20261015,
prop-coef-integral-dualizing.proof.md paragraph 2, support-open-tensor subargument
(blueprint: def-sf-open-tensor-representative-data).

This is data for the representative clauses, with no existence assertion. The ordinary
and derived tensors, one-K-flat comparisons and their normalizations are reused.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

section Representatives
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
  (A : SemilinearSections.Closed.{c, v, r} J R) (T : SemilinearSections.Models.{c, v, r} J R A)

variable {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C') (R' : Sheaf J' CommRingCat.{max c v r})
  (A' : SemilinearSections.Closed.{c, v, r} J' R')
  (T' : SemilinearSections.Models.{c, v, r} J' R' A')
  (F : SemilinearSections.Mod.{c, v, max c v r} J' R' ⥤
    SemilinearSections.Mod.{c, v, max c v r} J R)
  (G : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    SemilinearSections.Mod.{c, v, max c v r} J' R')
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (adj : F ⊣ G)
  (H : C ⥤ C')
  (sectionPull : ∀ (N : SemilinearSections.Mod.{c, v, max c v r} J R) (V : Cᵒᵖ),
    N.val.obj V → (G.obj N).val.obj (H.op.obj V))

/-- The representative characterization of the canonical open tensor isomorphism.
The restriction comparison is fixed on actual sheafified pure tensors, the inverse
open comparison by the open unit, and the chain map on every signed total summand.
All maps are morphisms on the entire ringed site; for a sequence site this includes
commutation with every horizontal quotient-semilinear transition.
Source: Stacks 0E8I, 0GL1, 07A4; support-open-tensor proof steps 5--6
(blueprint: def-sf-open-tensor-representative-data). -/
structure OpenTensorModel where
  restriction : A.tensor ⋙ G.mapDerivedCategory ≅
    (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ A'.tensor
  restrictionModel : TensorComparisonModel.{c, v, r} J J' R R' G A A' T T' restriction
  restrictionPure : ∀ (M N : SemilinearSections.Mod.{c, v, max c v r} J R) (V : Cᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V),
    (restrictionModel.ordinary M N).hom.val.app (H.op.obj V)
        (sectionPull (ordinaryTensor.{c, v, r} J R M N) V
          (tensorSection.{c, v, r} J R M N V x y)) =
      tensorSection.{c, v, r} J' R' (G.obj M) (G.obj N) (H.op.obj V)
        (sectionPull M V x) (sectionPull N V y)
  ordinary : ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J' R')
    (N : SemilinearSections.Mod.{c, v, max c v r} J R),
    ordinaryTensor.{c, v, r} J R (F.obj M) N ≅
      F.obj (ordinaryTensor.{c, v, r} J' R' M (G.obj N))
  ordinary_inverse : ∀ M N,
    adj.homEquiv _ _ (ordinary M N).inv =
      ordinaryTensorHom.{c, v, r} J' R' (adj.unit.app M) (𝟙 (G.obj N)) ≫
        (restrictionModel.ordinary (F.obj M) N).inv
  chain : ∀ (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ),
    (totalTensor.{c, v, r} J R).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj C, P) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj ((totalTensor.{c, v, r} J' R').obj
        (C, (G.mapHomologicalComplex (.up ℤ)).obj P))
  summand : ∀ C P (a b k : ℤ) (h : a + b = k),
    tensorSummand.{c, v, r} J R ((F.mapHomologicalComplex (.up ℤ)).obj C) P a b k h ≫
        (chain C P).hom.f k =
      (ordinary (C.X a) (P.X b)).hom ≫
        F.map (tensorSummand.{c, v, r} J' R' C
          ((G.mapHomologicalComplex (.up ℤ)).obj P) a b k h)
  ambientModel : RingedDerivedTensorComparison.{c, v, r, (max c v r)+1} J R A
  ambientBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r)+1} J R A T ambientModel
  ambientNaturality : RingedDerivedTensorNaturality.{c, v, r, (max c v r)+1} J R A ambientModel
  openModel : RingedDerivedTensorComparison.{c, v, r, (max c v r)+1} J' R' A'
  openBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r)+1} J' R' A' T' openModel
  openNaturality : RingedDerivedTensorNaturality.{c, v, r, (max c v r)+1} J' R' A' openModel
  restrictionFlat : ∀ (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    flatTerms.{c, v, r} J R P →
    flatTerms.{c, v, r} J' R' ((G.mapHomologicalComplex (.up ℤ)).obj P)
  gamma : (F.mapDerivedCategory.prod (𝟭 _)) ⋙ A.tensor ≅
    (𝟭 _).prod G.mapDerivedCategory ⋙ A'.tensor ⋙ F.mapDerivedCategory
  gamma_inverse : ∀ M N,
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).homEquiv _ _
        (gamma.inv.app (M, N)) =
      A'.tensor.map (Prod.mkHom
          ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj).unit.app M)
          (𝟙 (G.mapDerivedCategory.obj N))) ≫
        restriction.inv.app (F.mapDerivedCategory.obj M, N)
  derived_model : ∀ (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (flatP : flatTerms.{c, v, r} J R P),
    (ambientModel ((F.mapHomologicalComplex (.up ℤ)).obj C) P (Or.inr hP)).hom ≫
        A.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 _)) ≫
        gamma.hom.app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map (chain C P).hom ≫
        F.mapDerivedCategoryFactors.inv.app ((totalTensor.{c, v, r} J' R').obj
          (C, (G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        F.mapDerivedCategory.map ((openModel C ((G.mapHomologicalComplex (.up ℤ)).obj P)
          (Or.inr (restrictionModel.kflat P hP flatP))).hom) ≫
        F.mapDerivedCategory.map (A'.tensor.map
          (Prod.mkHom (𝟙 _) (G.mapDerivedCategoryFactors.inv.app P)))

end Representatives

end WeilConjectures.CoefSupportOpenTensor
