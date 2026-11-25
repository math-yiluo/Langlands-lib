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
import all WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat

/-! # Totalization of an ordinary open tensor comparison

The direct-sum totalization is natural in both complexes and retains its specified
summand formula. Source: Stacks 0GL1 and Homology 012Z
(blueprint: lem-coef-native-open-tensor-totalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall
attribute [local irreducible] SheafOfModules.monoidalCategory

/-- Totalize an ordinary natural extension/tensor isomorphism, with its summand equation.
Source: Stacks, sites-cohomology.tex Tag 0GL1 and Homology Tag 012Z.
(blueprint: lem-coef-native-open-tensor-totalization).

Proof: use the existing map-bifunctor totalization of the inverse ordinary
comparison. The left adjoint preserves the coproducts in each total degree;
naturality for the differentials makes the component maps a chain map.
Invert this comparison. Cancel its invertible component in the insertion
identity to obtain the stated summand equation. Invert its simultaneous
naturality square to get naturality of the resulting chain comparison. -/
theorem nativeOpenTensor_totalization_exists
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C') (R' : Sheaf J' CommRingCat.{max c v r})
    (F : SemilinearSections.Mod.{c, v, max c v r} J' R' ⥤
      SemilinearSections.Mod.{c, v, max c v r} J R)
    (G : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
      SemilinearSections.Mod.{c, v, max c v r} J' R')
    [hF : F.Additive] [hG : G.Additive] (adj : F ⊣ G)
    (ordinary : ∀ (M : SemilinearSections.Mod.{c, v, max c v r} J' R')
      (N : SemilinearSections.Mod.{c, v, max c v r} J R),
      ordinaryTensor.{c, v, r} J R (F.obj M) N ≅
        F.obj (ordinaryTensor.{c, v, r} J' R' M (G.obj N)))
    (hn : ∀ {M M' : SemilinearSections.Mod.{c, v, max c v r} J' R'}
      {N N' : SemilinearSections.Mod.{c, v, max c v r} J R} (f : M ⟶ M') (g : N ⟶ N'),
      ordinaryTensorHom.{c, v, r} J R (F.map f) g ≫ (ordinary M' N').hom =
        (ordinary M N).hom ≫ F.map (ordinaryTensorHom.{c, v, r} J' R' f (G.map g))) :
    ∃ chain : ∀ (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
        (Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ),
      (totalTensor.{c, v, r} J R).obj ((F.mapHomologicalComplex (.up ℤ)).obj P, Q) ≅
        (F.mapHomologicalComplex (.up ℤ)).obj ((totalTensor.{c, v, r} J' R').obj
          (P, (G.mapHomologicalComplex (.up ℤ)).obj Q)),
      (∀ P Q (a b k : ℤ) (h : a + b = k),
        tensorSummand.{c, v, r} J R ((F.mapHomologicalComplex (.up ℤ)).obj P) Q a b k h ≫
            (chain P Q).hom.f k =
          (ordinary (P.X a) (Q.X b)).hom ≫
            F.map (tensorSummand.{c, v, r} J' R' P
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) a b k h)) ∧
      (∀ {P P' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ}
        {Q Q' : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ}
        (f : P ⟶ P') (g : Q ⟶ Q'),
        (totalTensor.{c, v, r} J R).map
            (Prod.mkHom ((F.mapHomologicalComplex (.up ℤ)).map f) g) ≫ (chain P' Q').hom =
          (chain P Q).hom ≫ (F.mapHomologicalComplex (.up ℤ)).map
            ((totalTensor.{c, v, r} J' R').map
              (Prod.mkHom f ((G.mapHomologicalComplex (.up ℤ)).map g)))) := by
  let A := SemilinearSections.Mod.{c, v, max c v r} J' R'
  let B := SemilinearSections.Mod.{c, v, max c v r} J R
  let : MonoidalCategory A := SheafOfModules.cochainModulesMonoidal R'
  let : MonoidalCategory B := SheafOfModules.cochainModulesMonoidal R
  let : MonoidalPreadditive A := SheafOfModules.cochainModulesPreadditive R'
  let : MonoidalPreadditive B := SheafOfModules.cochainModulesPreadditive R
  let : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
  let H := MonoidalCategory.curriedTensor A
  let H' := MonoidalCategory.curriedTensor B
  let : H.PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R'
  let : ∀ M, (H.obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R'
  let : H'.PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let : ∀ M, (H'.obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.precompose_preservesZero H G
  let := SheafOfModules.precompose_obj_preservesZero H G
  let : ∀ (P Q : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor P Q H (.up ℤ) :=
    SheafOfModules.ringedOpenHasTotalTensor.{c, v, r} R'
  let : ∀ (P Q : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P Q H' (.up ℤ) :=
    SheafOfModules.ringedOpenHasTotalTensor.{c, v, r} R
  let : ∀ (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P Q
        (H ⋙ (Functor.whiskeringLeft B A A).obj G) (.up ℤ) :=
    SheafOfModules.precompose_hasTotal H G
  obtain ⟨Φ, hi, hnat⟩ := SheafOfModules.comparisonFromComponents_exists F G H H'
    (fun M N ↦ (ordinary M N).symm) (by
      intro M M' N N' f g
      dsimp only [H, H', MonoidalCategory.curriedTensor_map_app,
        MonoidalCategory.curriedTensor_obj_map]
      simpa only [ordinaryTensorHom, ordinaryTensor, SheafOfModules.cochainModulesMonoidal,
        MonoidalCategory.curriedTensor_obj_obj, Iso.symm_hom,
        MonoidalCategory.tensorHom_def, Category.assoc] using
        SheafOfModules.inverse_square _ _ _ _ (hn f g))
    (SheafOfModules.ringedOpenTotalTensor.{c, v, r} R')
    (SheafOfModules.ringedOpenTotalTensor.{c, v, r} R)
    (SheafOfModules.ringedOpenTensorι.{c, v, r} R')
    (SheafOfModules.ringedOpenTensorι.{c, v, r} R)
    (SheafOfModules.ringedOpenTotalTensor_presentation.{c, v, r} R')
    (SheafOfModules.ringedOpenTotalTensor_presentation.{c, v, r} R)
  refine ⟨fun P Q ↦ (Φ P Q).symm, ?_, ?_⟩
  · intro P Q a b k h
    exact SheafOfModules.inverse_square (ordinary (P.X a) (Q.X b)).symm
      ((HomologicalComplex.eval B (.up ℤ) k).mapIso (Φ P Q)) _ _ (hi P Q a b k h)
  · intro P P' Q Q' f g
    exact SheafOfModules.inverse_square (Φ P Q) (Φ P' Q') _ _ (hnat P P' Q Q' f g)

end WeilConjectures.CoefSupportOpenTensor
