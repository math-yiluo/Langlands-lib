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

/-! # Ordinary input to open tensor descent

Source: Stacks 0E8I, 0GL1, 07A4, 0G7E and Homology 012Z
(blueprint: def-sf-open-tensor-cochain-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})

variable {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C') (R' : Sheaf J' CommRingCat.{max c v r})
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

/-- Ordinary and cochain data for an exact open adjunction. No derived tensor is
chosen here. The projection and its total are natural in both variables, and the
ordinary inverse is the specified unit transpose. Source: Stacks 0E8I, 0GL1, 07A4,
0G7E and Homology 012Z (blueprint: def-sf-open-tensor-cochain-data). -/
structure OpenTensorCochainData where
  right : SemilinearSections.Mod.{c, v, max c v r} J' R' ⥤
    SemilinearSections.Mod.{c, v, max c v r} J R
  pullAdjunction : G ⊣ right
  pullTensor : ∀ M N : SemilinearSections.Mod.{c, v, max c v r} J R,
    G.obj (ordinaryTensor.{c, v, r} J R M N) ≅
      ordinaryTensor.{c, v, r} J' R' (G.obj M) (G.obj N)
  pullNaturality : ∀ {M M' N N' : SemilinearSections.Mod.{c, v, max c v r} J R}
    (f : M ⟶ M') (g : N ⟶ N'),
    G.map (ordinaryTensorHom.{c, v, r} J R f g) ≫ (pullTensor M' N').hom =
      (pullTensor M N).hom ≫ ordinaryTensorHom.{c, v, r} J' R' (G.map f) (G.map g)
  pullPure : ∀ (M N : SemilinearSections.Mod.{c, v, max c v r} J R) (V : Cᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V),
    (pullTensor M N).hom.val.app (H.op.obj V)
        (sectionPull (ordinaryTensor.{c, v, r} J R M N) V
          (tensorSection.{c, v, r} J R M N V x y)) =
      tensorSection.{c, v, r} J' R' (G.obj M) (G.obj N) (H.op.obj V)
        (sectionPull M V x) (sectionPull N V y)
  pullKFlat : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    flatTerms.{c, v, r} J R P →
    CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R')
      ((G.mapHomologicalComplex (.up ℤ)).obj P)
  pullFlat : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    flatTerms.{c, v, r} J R P →
    flatTerms.{c, v, r} J' R' ((G.mapHomologicalComplex (.up ℤ)).obj P)
  ordinary : ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J' R')
    (N : SemilinearSections.Mod.{c, v, max c v r} J R),
    ordinaryTensor.{c, v, r} J R (F.obj M) N ≅
      F.obj (ordinaryTensor.{c, v, r} J' R' M (G.obj N))
  ordinaryInverse : ∀ M N,
    adj.homEquiv _ _ (ordinary M N).inv =
      ordinaryTensorHom.{c, v, r} J' R' (adj.unit.app M) (𝟙 (G.obj N)) ≫
        (pullTensor (F.obj M) N).inv
  ordinaryNaturality : ∀ {M M' : SemilinearSections.Mod.{c, v, max c v r} J' R'}
    {N N' : SemilinearSections.Mod.{c, v, max c v r} J R} (f : M ⟶ M') (g : N ⟶ N'),
    ordinaryTensorHom.{c, v, r} J R (F.map f) g ≫ (ordinary M' N').hom =
      (ordinary M N).hom ≫ F.map (ordinaryTensorHom.{c, v, r} J' R' f (G.map g))
  chain : ∀ (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ),
    (totalTensor.{c, v, r} J R).obj ((F.mapHomologicalComplex (.up ℤ)).obj P, Q) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj ((totalTensor.{c, v, r} J' R').obj
        (P, (G.mapHomologicalComplex (.up ℤ)).obj Q))
  summand : ∀ P Q (a b k : ℤ) (h : a + b = k),
    tensorSummand.{c, v, r} J R ((F.mapHomologicalComplex (.up ℤ)).obj P) Q a b k h ≫
        (chain P Q).hom.f k =
      (ordinary (P.X a) (Q.X b)).hom ≫
        F.map (tensorSummand.{c, v, r} J' R' P
          ((G.mapHomologicalComplex (.up ℤ)).obj Q) a b k h)
  chainNaturality : ∀ {P P' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ}
    {Q Q' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q'),
    (totalTensor.{c, v, r} J R).map
        (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f) g) ≫ (chain P' Q').hom =
      (chain P Q).hom ≫ (F.mapHomologicalComplex (.up ℤ)).map
        ((totalTensor.{c, v, r} J' R').map
          (Prod.mkHom f ((G.mapHomologicalComplex (.up ℤ)).map g)))

end WeilConjectures.CoefSupportOpenTensor
