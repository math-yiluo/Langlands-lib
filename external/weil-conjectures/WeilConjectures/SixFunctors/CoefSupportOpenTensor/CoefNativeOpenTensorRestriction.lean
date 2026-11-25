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
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingTensorComparison
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
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
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
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

/-! # Unit-normalized ordinary restriction tensor data

Source: Stacks 03EL and 0G7E
(blueprint: lem-coef-native-open-tensor-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open WeilConjectures.SemilinearSections
open SheafOfModules.GeometricConstruction (mset rset)
open SheafOfModules.OpenTensorNormalization.GeneralizedRinged
open AlgebraicGeometry.ProEtale.VaryingRing
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall
attribute [local irreducible] SheafOfModules.monoidalCategory Functor.leftAdjoint

/-- Construct the restriction tensorator normalized by the given module-adjunction unit,
and preserve flat-term K-flat complexes along the same functor.
Source: Stacks, sites-modules.tex Tag 03EL; sites-cohomology.tex Tag 0G7E.
(blueprint: lem-coef-native-open-tensor-restriction).

Proof: compose the given algebraic inverse image with scalar extension along c.
Its normalized adjunction identifies it with F by uniqueness of left adjoints.
Transport the normalized tensorator through this isomorphism. Apply the set
adjunction's unit naturality to the sheaf of pairs of sections and its pure
pairing. The normalized Hom-equivalence equation identifies scalar insertion
with the specified module-adjunction unit; the transported pairing therefore
has exactly the displayed pure formula. Transport the tensorator's naturality,
and transport flatness and K-flatness along the same functor isomorphism. -/
theorem nativeOpenTensor_restriction_exists
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (g : C ⥤ D) [g.IsContinuous J K]
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (φ : R ⟶ (g.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj S)
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)))
    (a : L ⊣ g.sheafPushforwardContinuous (Type (u + 1)) J K)
    [PreservesFiniteLimits L]
    (RI : Sheaf K CommRingCat.{u + 1})
    (I : SheafOfModules.AlgebraicInverseImage L R RI) (c : RI ⟶ S)
    (hc : (sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).map c =
      I.ringUnderlying.inv ≫ (a.homEquiv
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj R)
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})).obj S)).symm
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).map φ))
    (F : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} J R ⥤
      WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} K S)
    (adj : F ⊣ SheafOfModules.pushforward.{u + 1} (F := g) (J := J) (K := K)
      (R := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      (S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ))
    [hAdd : F.Additive] :
    ∃ rho : ∀ M N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} J R,
      F.obj (ordinaryTensor.{u + 1, u, u + 1} J R M N) ≅
        ordinaryTensor.{u + 1, u, u + 1} K S (F.obj M) (F.obj N),
      (∀ {M M' N N'} (f : M ⟶ M') (h : N ⟶ N'),
        F.map (ordinaryTensorHom.{u + 1, u, u + 1} J R f h) ≫ (rho M' N').hom =
          (rho M N).hom ≫ ordinaryTensorHom.{u + 1, u, u + 1} K S (F.map f) (F.map h)) ∧
      (∀ M N (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
        (rho M N).hom.val.app (g.op.obj U)
          ((adj.unit.app _).val.app U (tensorSection.{u + 1, u, u + 1} J R M N U x y)) =
        tensorSection.{u + 1, u, u + 1} K S (F.obj M) (F.obj N) (g.op.obj U)
          ((adj.unit.app M).val.app U x) ((adj.unit.app N).val.app U y)) ∧
      (∀ P : CochainComplex (WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} J R) ℤ,
        P.IsKFlatIndependentCoefficients → flatTerms.{u + 1, u, u + 1} J R P →
        CochainComplex.IsKFlatIndependentCoefficients
          ((F.mapHomologicalComplex (.up ℤ)).obj P) ∧
        flatTerms.{u + 1, u, u + 1} K S ((F.mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨a₀, ha₀⟩ := normalizedAdjunction g L a S R φ RI I c hc
  let F₀ := I.modules ⋙ tensorFunctor c
  let e : F₀ ≅ F := Adjunction.leftAdjointUniq a₀ adj
  have : F₀.Additive := Functor.additive_of_iso e.symm
  obtain ⟨k, hkn, hkp⟩ := SheafOfModules.CochainTensorComparison.normalizedTensorator_exists
    R S RI L I c F₀ (fun _ ↦ rfl)
    (g.sheafPushforwardContinuous (Type (u + 1)) J K) a (by intros; rfl)
  let rho := transportedOrdinary J K R S F₀ F e k
  have hn := @transportedOrdinary_natural _ _ _ _ _ _ J K R S F₀ F e k hkn
  let ins := fun T : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} J R ↦
    I.moduleUnderlying.inv.app T ≫
      SheafOfModules.CochainTensorComparison.scalarInsertion R S RI L I c F₀
        (fun _ ↦ rfl) T
  have transpose (T : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} J R)
      (H : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1} K S) (b : F.obj T ⟶ H) :
      (mset R).map (adj.homEquiv T H b) =
        a.homEquiv _ _ (ins T ≫ (mset S).map (e.hom.app T ≫ b)) := by
    rw [← leftAdjointUniq_transpose a₀ adj T H b]
    exact ha₀ T H (e.hom.app T ≫ b)
  refine ⟨rho, hn, ?_, ?_⟩
  · intro M N U x y
    let Z := (mset R).obj M ⊗ (mset R).obj N
    let z := SheafOfModules.CochainInversePairing.pureSheaf R M N
    let v := (a.unit.app Z).hom.app U (x, y)
    have hp := hkp M N Z (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _) z (fun _ _ ↦ rfl) (g.op.obj U) v
    have he := transportedOrdinary_cancel J K R S F₀ F e k M N
    have ht := transpose _ _ (rho M N).hom
    have huM := transpose M (F.obj M) (𝟙 _)
    have huN := transpose N (F.obj N) (𝟙 _)
    have hNat (T : Sheaf J (Type (u + 1))) (w : Z ⟶ T) :
        (L.map w).hom.app (g.op.obj U) v =
          (a.unit.app T).hom.app U (w.hom.app U (x, y)) := by
      exact (congrArg (fun q ↦ q.hom.app U (x, y)) (a.unit.naturality w)).symm
    have ht' := congrArg (fun q ↦ q.hom.app U
      (tensorSection.{u + 1, u, u + 1} J R M N U x y)) ht
    have huM' := congrArg (fun q ↦ q.hom.app U x) huM
    have huN' := congrArg (fun q ↦ q.hom.app U y) huN
    simp only [Adjunction.homEquiv_id, Category.comp_id] at huM' huN'
    simp only [Adjunction.homEquiv_unit] at ht' huM' huN'
    change (k M N).hom.val.app (g.op.obj U)
        ((ins _).hom.app (g.op.obj U) ((L.map z).hom.app (g.op.obj U) v)) =
      tensorSection.{u + 1, u, u + 1} K S (F₀.obj M) (F₀.obj N) (g.op.obj U)
        ((ins M).hom.app (g.op.obj U)
          ((L.map (CartesianMonoidalCategory.fst _ _)).hom.app (g.op.obj U) v))
        ((ins N).hom.app (g.op.obj U)
          ((L.map (CartesianMonoidalCategory.snd _ _)).hom.app (g.op.obj U) v)) at hp
    rw [hNat, hNat, hNat] at hp
    change (rho M N).hom.val.app (g.op.obj U)
        ((adj.unit.app _).val.app U (tensorSection.{u + 1, u, u + 1} J R M N U x y)) =
      (rho M N).hom.val.app (g.op.obj U)
        ((e.hom.app _).val.app (g.op.obj U)
          ((ins _).hom.app (g.op.obj U)
            ((a.unit.app ((mset R).obj
              (ordinaryTensor.{u + 1, u, u + 1} J R M N))).hom.app U
                (tensorSection.{u + 1, u, u + 1} J R M N U x y)))) at ht'
    change (adj.unit.app M).val.app U x =
      (e.hom.app M).val.app (g.op.obj U) ((ins M).hom.app (g.op.obj U)
        ((a.unit.app ((mset R).obj M)).hom.app U x)) at huM'
    change (adj.unit.app N).val.app U y =
      (e.hom.app N).val.app (g.op.obj U) ((ins N).hom.app (g.op.obj U)
        ((a.unit.app ((mset R).obj N)).hom.app U y)) at huN'
    have he' := congrArg (fun q ↦ q.val.app (g.op.obj U)
      ((ins _).hom.app (g.op.obj U)
        ((a.unit.app ((mset R).obj
          (ordinaryTensor.{u + 1, u, u + 1} J R M N))).hom.app U
            (tensorSection.{u + 1, u, u + 1} J R M N U x y)))) he
    change (rho M N).hom.val.app _ ((e.hom.app _).val.app _ _) =
      (MonoidalCategory.tensorIso (e.app M) (e.app N)).hom.val.app _
        ((k M N).hom.val.app _ _) at he'
    rw [ht', he']
    change (MonoidalCategory.tensorIso (e.app M) (e.app N)).hom.val.app _
      ((k M N).hom.val.app _ _) = _
    change (k M N).hom.val.app (g.op.obj U)
        ((ins _).hom.app (g.op.obj U)
          ((a.unit.app ((mset R).obj
            (ordinaryTensor.{u + 1, u, u + 1} J R M N))).hom.app U
              (tensorSection.{u + 1, u, u + 1} J R M N U x y))) =
      tensorSection.{u + 1, u, u + 1} K S (F₀.obj M) (F₀.obj N) (g.op.obj U)
        ((ins M).hom.app (g.op.obj U) ((a.unit.app ((mset R).obj M)).hom.app U x))
        ((ins N).hom.app (g.op.obj U) ((a.unit.app ((mset R).obj N)).hom.app U y)) at hp
    erw [hp]
    refine (SheafOfModules.CochainScalarConstruction.pure_map S
      (e.app M).hom (e.app N).hom (g.op.obj U) _ _).trans ?_
    exact congrArg₂ (tensorSection.{u + 1, u, u + 1} K S
      (F.obj M) (F.obj N) (g.op.obj U)) huM'.symm huN'.symm
  · intro P hP hf
    have h := SheafOfModules.isKFlat_ringedToposPullback L
      (g.sheafPushforwardContinuous (Type (u + 1)) J K) a I c F₀
      (fun _ ↦ rfl) (by intros; rfl) P hP hf
    refine ⟨SheafOfModules.kFlat_iso_independent S
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app P) h.1, ?_⟩
    intro n
    exact SheafOfModules.flatOnSite_of_iso S (e.app (P.X n)) (h.2 n)

end WeilConjectures.CoefSupportOpenTensor
