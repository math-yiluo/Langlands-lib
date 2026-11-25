/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSite
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Frobenius action sites and unbounded resolutions

Source: latest blueprint, prose-10-20, internal-Hom/evaluation
paragraph; native action-site refinement, steps 1--7; Stacks 015F, 06YS, 079P, 0G7E,
and 08BJ (blueprint: lem-sf-weil-frobenius-action-resolutions).

The small site is the existing bounded pro-etale category with lifted hom types.
It retains every bounded object, and hence all integer translates. Coefficients
and K-flatness reuse the recorded section-ring and module-sheaf interfaces.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u wA wB
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures.WeilFrobeniusAction

/-- Postcomposition on the actual bounded weakly etale site.
Source: native action-site proof, step 1
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def postcompose {T : Scheme.{u}} (g : T ≅ T) : T.ProEt ≌ T.ProEt :=
  MorphismProperty.Comma.mapRightIso (P := @WeaklyEtale) (Q := ⊤) (W := ⊤)
    (𝟭 Scheme.{u}) ((Functor.const _).mapIso g)

/-- A small model containing every bounded object and every integer translate.
Source: native action-site proof, step 1; the size convention
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev Site (T : Scheme.{u}) := AsSmall.{u + 1} T.ProEt

/-- The topology transported from the recorded small pro-etale site.
Source: native action-site proof, steps 1--2
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev topology (T : Scheme.{u}) : GrothendieckTopology (Site T) :=
  AsSmall.down.inducedTopology (Scheme.ProEt.topology T)

/-- Inverse Frobenius translation, so inverse reindexing is geometric Frobenius pullback.
Source: native action-site proof, step 1
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def translation {T : Scheme.{u}} (g : T ≅ T) : Site T ≌ Site T :=
  AsSmall.equiv.symm.trans ((postcompose g.symm).trans AsSmall.equiv)

/-- The finite-subextension coefficient ring, reconstructed from its existing
sheafification and restricted to the small model.
Source: native action-site proof, step 2; Bhatt--Scholze 6.8
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def coefficient (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    Sheaf (topology T) CommRingCat.{u + 1} :=
  (AsSmall.down.sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology T) (Scheme.ProEt.topology T)).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l))

/-- The generating finite-field-valued continuous sections of the sheafified ring.
Source: native action-site proof, step 2
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def generator (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (U : Site T)
    (f : PadicAlgCl.finiteIntermediateFieldValued l (AsSmall.down.obj U).left) :
    (coefficient T l).obj.obj (op U) :=
  (toSheafify (Scheme.ProEt.topology T)
    (ProEtale.padicAlgClRingPresheaf T l ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})).app
      (op (AsSmall.down.obj U)) (ULift.up f)

/-- The existing module-sheaf category over this coefficient ring.
Source: native action-site proof, step 3
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev Modules (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :=
  TwistedActionRingedSite.Modules (coefficient T l)

/-- Return to the original site, with its unchanged ring and module sections.
Source: native action-site proof, step 2
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def ambientModules (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    Modules T l ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (ProEtale.padicAlgClSheaf T l) := by
  have : (AsSmall.equiv : T.ProEt ≌ Site T).functor.IsDenseSubsite
      (Scheme.ProEt.topology T) (topology T) := by
    change (AsSmall.equiv : T.ProEt ≌ Site T).functor.IsDenseSubsite
      (Scheme.ProEt.topology T)
      ((AsSmall.equiv : T.ProEt ≌ Site T).inverse.inducedTopology (Scheme.ProEt.topology T))
    infer_instance
  have : AsSmall.up.IsContinuous (Scheme.ProEt.topology T) (topology T) :=
    inferInstanceAs ((AsSmall.equiv : T.ProEt ≌ Site T).functor.IsContinuous
      (Scheme.ProEt.topology T) (topology T))
  exact SheafOfModules.pushforward (F := AsSmall.up)
    (𝟙 ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l)))) ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l)).inverse

/-- The finite locally closed stratification with locally finite free restrictions,
expressed on the original site by the recorded scheme-cover predicate
`AlgebraicGeometry.ProEtale.CondensedRing.LocallyFree`, owned by
`def-sf-proetale-locally-finite-free-module`.
Source: native action-site proof, step 5; Bhatt--Scholze 6.8
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def Constructible (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (M : Modules T l) : Prop :=
  ∃ S : Scheme.FiniteLocallyClosedStratification T, ∀ i : Fin S.n,
    ProEtale.CondensedRing.LocallyFree
      ((ProEtale.upperStar Ab.{u + 1} (S.immersion i)).obj (ProEtale.padicAlgClSheaf T l))
      (((ProEtale.upperStar Ab.{u + 1} (S.immersion i)).mapMod
        (ProEtale.padicAlgClSheaf T l)).obj ((ambientModules T l).obj M))

/-- The normalized ordinary Frobenius action-site realization.
Source: native action-site proof, steps 1--3
(blueprint: lem-sf-weil-frobenius-action-resolutions).
No realization is selected from a mere existence statement. Its presentation is
exactly the recorded twisted ringed-site presentation, including tensor, Hom,
symmetry, evaluation, created limits/colimits, and normalized orbit induction. -/
structure Realization (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (g : T ≅ T) where
  /-- The concrete restriction model has exactly the original module category. -/
  ambientEquivalence : (ambientModules T l).IsEquivalence
  /-- The comparison with original modules is additive. -/
  ambientAdditive : (ambientModules T l).Additive
  /-- Covering sieves are preserved by the translation. -/
  covering : CoverPreserving (topology T) (topology T) (translation g).functor
  /-- Covering sieves are preserved by its inverse. -/
  inverseCovering : CoverPreserving (topology T) (topology T) (translation g).inverse
  /-- Postcomposition and its inverse preserve the topology. -/
  [continuous : (translation g).functor.IsContinuous (topology T) (topology T)]
  /-- The inverse translation preserves the topology. -/
  [inverseContinuous : (translation g).inverse.IsContinuous (topology T) (topology T)]
  /-- The chosen coefficient identification. -/
  a : ((translation g).inverse.sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology T) (topology T)).obj (coefficient T l) ≅ coefficient T l
  /-- On generating functions, postcomposition leaves the domain and function unchanged.
  In particular the very same finite coefficient field is preserved. -/
  functions (U : Site T)
      (f : PadicAlgCl.finiteIntermediateFieldValued l (AsSmall.down.obj U).left) :
    a.hom.hom.app (op U) (generator T l ((translation g).inverse.obj U) f) =
      generator T l U f
  /-- The explicitly defined pullback is an additive autoequivalence. -/
  [sigmaEquivalence : (TwistedActionRingedSite.sigma
    (topology T) (translation g) (coefficient T l) a).IsEquivalence]
  /-- Additivity is on the original module maps. -/
  [sigmaAdditive : (TwistedActionRingedSite.sigma
    (topology T) (translation g) (coefficient T l) a).Additive]
  /-- The full ordinary presentation, including all canonical comparisons. -/
  presentation : TwistedActionRingedSite.Presentation
    (topology T) (translation g) (coefficient T l) a

/-- The normalized pullback, with its topology witnesses fixed by the realization.
Source: native action-site proof, step 3
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev pullback {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) : Modules T l ⥤ Modules T l :=
  letI := D.continuous
  letI := D.inverseContinuous
  TwistedActionRingedSite.sigma (topology T) (translation g) (coefficient T l) D.a

/-- Pullback is additive on ordinary module maps.
Source: native action-site proof, step 3
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
instance pullbackAdditive {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) : (pullback D).Additive := D.sigmaAdditive

/-- Pullback is the autoequivalence asserted in the realization.
Source: native action-site proof, step 3
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
instance pullbackEquivalence {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) : (pullback D).IsEquivalence := D.sigmaEquivalence

/-- The recorded fixed-pair category for the explicit module pullback.
Source: native action-site proof, step 3
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev Pairs {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) :=
  Endofunctor.IsoAlgebra (pullback D)

/-- Forget only the invertible Frobenius structure.
Source: native action-site proof, steps 3--4
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev forget {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) : Pairs D ⥤ Modules T l :=
  Endofunctor.IsoAlgebra.forget (pullback D)

/-- The actual inverse action-site equivalence applied termwise to complexes.
Source: native action-site proof, step 6
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev onActionSite {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) :=
  letI := D.continuous
  letI := D.inverseContinuous
  D.presentation.modules.inverse.mapHomologicalComplex (ComplexShape.up ℤ)

/-- K-flatness in fixed pairs, transported by the specified additive tensor equivalence.
Source: native action-site proof, step 6; Stacks 06YN
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def KFlat {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) (K : CochainComplex (Pairs D) ℤ) : Prop :=
  letI := D.continuous
  letI := D.inverseContinuous
  letI := D.presentation.category
  CochainComplex.IsKFlatIndependentCoefficients
    (J := D.presentation.topology) (R := D.presentation.coefficient) ((onActionSite D).obj K)

/-- Flat terms in fixed pairs, under the same normalized tensor equivalence.
Source: native action-site proof, step 6; Stacks 03ER
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def FlatTerms {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) (K : CochainComplex (Pairs D) ℤ) : Prop :=
  letI := D.continuous
  letI := D.inverseContinuous
  letI := D.presentation.category
  ∀ n : ℤ, SheafOfModules.IsFlatOnSite
    (J := D.presentation.topology) (R := D.presentation.coefficient)
    (((onActionSite D).obj K).X n)

private theorem presieve_map_comp {C D E : Type*}
    [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E)
    {X : C} (R : Presieve X) : (R.map F).map G = R.map (F ⋙ G) := by
  funext Y f
  apply propext
  constructor
  · rintro ⟨⟨h⟩⟩
    exact ⟨h⟩
  · rintro ⟨h⟩
    exact ⟨⟨h⟩⟩

private theorem postcompose_continuous {T : Scheme.{u}} (g : T ≅ T) :
    (postcompose g).functor.IsContinuous (Scheme.ProEt.topology T)
      (Scheme.ProEt.topology T) := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy (postcompose g).functor
    (Scheme.ProEt.precoverage T) (Scheme.ProEt.precoverage T)
  intro X R hR
  change (R.map (postcompose g).functor).map (Scheme.ProEt.forget T ⋙ Over.forget T) ∈
    Scheme.proetalePrecoverage _
  change R.map (Scheme.ProEt.forget T ⋙ Over.forget T) ∈
    Scheme.proetalePrecoverage _ at hR
  rw [presieve_map_comp]
  exact hR

private theorem translation_continuous {T : Scheme.{u}} (g : T ≅ T) :
    (translation g).functor.IsContinuous (topology T) (topology T) ∧
    (translation g).inverse.IsContinuous (topology T) (topology T) := by
  have : (AsSmall.equiv : T.ProEt ≌ Site T).functor.IsDenseSubsite
      (Scheme.ProEt.topology T) (topology T) := by
    change (AsSmall.equiv : T.ProEt ≌ Site T).functor.IsDenseSubsite
      (Scheme.ProEt.topology T)
      ((AsSmall.equiv : T.ProEt ≌ Site T).inverse.inducedTopology (Scheme.ProEt.topology T))
    infer_instance
  have : AsSmall.up.IsContinuous (Scheme.ProEt.topology T) (topology T) :=
    inferInstanceAs ((AsSmall.equiv : T.ProEt ≌ Site T).functor.IsContinuous _ _)
  have : AsSmall.down.IsContinuous (topology T) (Scheme.ProEt.topology T) := inferInstance
  have := postcompose_continuous g
  have := postcompose_continuous g.symm
  have : (postcompose g.symm).inverse.IsContinuous (Scheme.ProEt.topology T)
      (Scheme.ProEt.topology T) := postcompose_continuous g
  have h₁ : ((postcompose g.symm).trans
      (AsSmall.equiv : T.ProEt ≌ Site T)).functor.IsContinuous
      (Scheme.ProEt.topology T) (topology T) :=
    Functor.isContinuous_comp (postcompose g.symm).functor AsSmall.up
    (Scheme.ProEt.topology T) (Scheme.ProEt.topology T) (topology T)
  have h₂ : ((postcompose g.symm).trans
      (AsSmall.equiv : T.ProEt ≌ Site T)).inverse.IsContinuous
      (topology T) (Scheme.ProEt.topology T) :=
    Functor.isContinuous_comp AsSmall.down (postcompose g.symm).inverse
    (topology T) (Scheme.ProEt.topology T) (Scheme.ProEt.topology T)
  exact ⟨Functor.isContinuous_comp AsSmall.down _ _ (Scheme.ProEt.topology T) _,
    Functor.isContinuous_comp _ AsSmall.up _ (Scheme.ProEt.topology T) _⟩

private theorem small_up_continuous {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) : AsSmall.up.IsContinuous J
      (AsSmall.down.inducedTopology J : GrothendieckTopology (AsSmall.{u + 1} C)) := by
  have : (AsSmall.equiv : C ≌ AsSmall.{u + 1} C).functor.IsDenseSubsite J
      ((AsSmall.equiv : C ≌ AsSmall.{u + 1} C).inverse.inducedTopology J) := inferInstance
  exact inferInstanceAs ((AsSmall.equiv : C ≌ AsSmall.{u + 1} C).functor.IsContinuous J
    ((AsSmall.equiv : C ≌ AsSmall.{u + 1} C).inverse.inducedTopology J))

private theorem postcompose_cocontinuous {T : Scheme.{u}} (g : T ≅ T) :
    (postcompose g).functor.IsCocontinuous
      (Scheme.ProEt.topology T) (Scheme.ProEt.topology T) := by
  let _ := postcompose_continuous g.symm
  have : (postcompose g).inverse.IsContinuous
      (Scheme.ProEt.topology T) (Scheme.ProEt.topology T) := postcompose_continuous g.symm
  exact ((postcompose g).toAdjunction.isCocontinuous_iff_coverPreserving
      (Scheme.ProEt.topology T) (Scheme.ProEt.topology T)).mpr
    (CoverPreserving.of_isContinuous _ _ _)

private theorem sectionRingIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F : C ⥤ C) [F.IsContinuous J J]
    (A : Mon (Sheaf J Ab.{u + 1})) [IsCommMonObj A.X]
    (c : A ≅ (F.sheafPushforwardContinuous Ab.{u + 1} J J).mapMon.obj A) :
    ∃ e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A.X ≅
      (F.sheafPushforwardContinuous CommRingCat.{u + 1} J J).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A.X),
    ∀ (V : Cᵒᵖ) (x : A.X.obj.obj V), e.hom.hom.app V x = c.hom.hom.hom.app V x := by
  let _ := Sheaf.monoidalCategory J Ab.{u + 1}
  let U := sheafToPresheaf J Ab.{u + 1}
  let W := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj F.op
  let S := F.sheafPushforwardContinuous Ab.{u + 1} J J
  let e := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    F Ab.{u + 1} J J
  let z : U.mapMon.obj (S.mapMon.obj A) ≅
      W.mapMon.obj (U.mapMon.obj A) :=
    (Functor.mapMonCompIso (F := S) (G := U)).symm.app A ≪≫
      (Functor.mapMonNatIso e).symm.app A ≪≫
      (Functor.mapMonCompIso (F := U) (G := W)).app A
  let m : U.mapMon.obj A ⟶ W.mapMon.obj (U.mapMon.obj A) :=
    U.mapMon.map c.hom ≫ z.hom
  have hm : m.hom = c.hom.hom.hom := by
    have hm₀ : m.hom = c.hom.hom.hom ≫ z.hom.hom := rfl
    rw [hm₀]
    have hz : z.hom.hom = 𝟙 _ ≫ e.inv.app A.X ≫ 𝟙 _ := rfl
    rw [hz, Category.id_comp, Category.comp_id]
    have heh : e.hom.app A.X = 𝟙 _ :=
      Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app
        F Ab.{u + 1} J J A.X
    have hh := e.inv_hom_id_app A.X
    rw [heh, Category.comp_id] at hh
    rw [hh]
    exact Category.comp_id c.hom.hom.hom
  let q := (Monoidal.monFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}).functor.map m
  let φ : InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u} J A.X ⟶
      F.op ⋙ InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u} J A.X :=
    { app := fun V ↦ ConcreteCategory.ofHom (C := CommRingCat)
        (InternalAbelianSheafModule.ringHom (q.app V).hom)
      naturality := fun V V' f ↦ by
        ext x
        exact ConcreteCategory.congr_hom (m.hom.naturality f) x }
  have hφ (V : Cᵒᵖ) : (φ.app V).hom.toAddMonoidHom = (c.hom.hom.hom.app V).hom :=
    congrArg (fun a ↦ (a.app V).hom) hm
  let f : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A.X ⟶
      (F.sheafPushforwardContinuous CommRingCat.{u + 1} J J).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A.X) := ⟨φ⟩
  have hφ' (V : Cᵒᵖ) (x : A.X.obj.obj V) : φ.app V x = c.hom.hom.hom.app V x :=
    congrArg (fun a ↦ a x) (hφ V)
  have : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hb := (ConcreteCategory.bijective_of_isIso (c.hom.hom.hom.app V))
    constructor
    · intro x y h
      apply hb.1
      exact (hφ' V x).symm.trans ((congrArg id h).trans (hφ' V y))
    · intro y
      obtain ⟨x, hx⟩ := hb.2 y
      exact ⟨x, (hφ' V x).trans hx⟩
  have : IsIso ((sheafToPresheaf J CommRingCat.{u + 1}).map f) :=
    inferInstanceAs (IsIso φ)
  have : IsIso f := isIso_of_reflects_iso f (sheafToPresheaf J CommRingCat.{u + 1})
  exact ⟨asIso f, hφ'⟩

private theorem section_inverse_additive
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R).inverse.Additive :=
  by
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  have : E.functor.Additive := { map_add := by intros; ext U x; rfl }
  infer_instance

private theorem small_ambient_additive
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (S : Sheaf J Ab.{u + 1}) [MonObj S] [IsCommMonObj S] :
    let _ := small_up_continuous J
    let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J S
    let B := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
    let K := (AsSmall.down.inducedTopology J : GrothendieckTopology (AsSmall.{u + 1} C))
    (SheafOfModules.pushforward.{u + 1} (F := AsSmall.up)
      (R := (AsSmall.down.sheafPushforwardContinuous RingCat K J).obj B) (𝟙 B) ⋙
      (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        J S).inverse).Additive := by
  let _ := small_up_continuous J
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J S
  let B := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let K := (AsSmall.down.inducedTopology J : GrothendieckTopology (AsSmall.{u + 1} C))
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J S
  have : E.inverse.Additive := section_inverse_additive J S
  let P := SheafOfModules.pushforward.{u + 1} (F := AsSmall.up)
    (R := (AsSmall.down.sheafPushforwardContinuous RingCat K J).obj B) (𝟙 B)
  have : P.Additive := { map_add := by intros; ext U x; rfl }
  exact inferInstanceAs (P ⋙ E.inverse).Additive

private theorem ambient_additive (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    (ambientModules T l).Additive :=
  small_ambient_additive (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l)

private theorem constructible_of_iso {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {M N : Modules T l} (e : M ≅ N) (h : Constructible T l M) : Constructible T l N := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun i ↦ ?_⟩
  exact ProEtale.CondensedRing.locallyFree_of_iso
    (((ProEtale.upperStar Ab.{u + 1} (S.immersion i)).mapMod
      (ProEtale.padicAlgClSheaf T l)).mapIso ((ambientModules T l).mapIso e)) (hS i)

private theorem action_additive {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {g : T ≅ T} (D : Realization T l g) :
    let _ := D.continuous
    let _ := D.inverseContinuous
    D.presentation.modules.functor.Additive := by
  let _ := D.continuous
  let _ := D.inverseContinuous
  let _ := D.presentation.category
  let E : TwistedActionRingedSite.Modules D.presentation.coefficient ≌ Pairs D :=
    D.presentation.modules
  change E.functor.Additive
  constructor
  intro M N f g
  apply (forget D).map_injective
  exact D.presentation.modules_add f g

private theorem kflat_iso {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    {K L : CochainComplex (TwistedActionRingedSite.Modules R) ℤ} (e : K ≅ L)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) L := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  let _ := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let _ := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF i
  exact (hK F hF i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso e)

set_option backward.isDefEq.respectTransparency false in
private theorem flat_iso {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)} (e : M ≅ N)
    (hM : SheafOfModules.IsFlatOnSite (J := J) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) N := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  change exactFunctor _ _ (SheafOfModules.siteSheafTensorRight.{u + 1, u + 1, u + 1, u + 1}
      (J := J) (A := R) M) at hM
  change exactFunctor _ _ (SheafOfModules.siteSheafTensorRight.{u + 1, u + 1, u + 1, u + 1}
      (J := J) (A := R) N)
  exact (exactFunctor _ _).prop_of_iso
    ((SheafOfModules.siteSheafTensorRightIso R M) ≪≫
      ((MonoidalCategory.curriedTensor _).flip.mapIso e) ≪≫
      (SheafOfModules.siteSheafTensorRightIso R N).symm) hM

set_option backward.isDefEq.respectTransparency false in
private theorem flat_comparison {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    SheafOfModules.IsFlat M ↔ SheafOfModules.IsFlatOnSite (J := J) (R := R) M := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  change exactFunctor _ _ (MonoidalCategory.tensorRight M) ↔
    exactFunctor _ _ (SheafOfModules.siteSheafTensorRight.{u + 1, u + 1, u + 1, u + 1}
      (J := J) (A := R) M)
  exact ⟨fun h ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R M).symm h,
    fun h ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R M) h⟩

private theorem preserves_flat {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {g : T ≅ T} (D : Realization T l g) (K : CochainComplex (Pairs D) ℤ)
    (hk : KFlat D K) (hf : FlatTerms D K) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((forget D).mapHomologicalComplex (.up ℤ)).obj K) ∧
      ∀ n, SheafOfModules.IsFlatOnSite (J := topology T) (R := coefficient T l)
        ((((forget D).mapHomologicalComplex (.up ℤ)).obj K).X n) := by
  let _ := D.continuous
  let _ := D.inverseContinuous
  let _ := D.presentation.category
  let E : TwistedActionRingedSite.Modules D.presentation.coefficient ≌ Pairs D :=
    D.presentation.modules
  have : E.functor.Additive := action_additive D
  let Ec := E.mapHomologicalComplex (.up ℤ)
  obtain ⟨F, hF, adj, hflat, _⟩ := RingedToposMorphism.exists_kFlatPullback
    (topology T) D.presentation.topology (coefficient T l)
    D.presentation.coefficient D.presentation.geometric
  let _ := hF
  let G : TwistedActionRingedSite.Modules D.presentation.coefficient ⥤ Modules T l :=
    E.functor ⋙ forget D
  have adjG : G ⊣ D.presentation.geometric.modules := D.presentation.modulePullback
  let e : F ≅ G := adj.leftAdjointUniq adjG
  obtain ⟨h₁, h₂⟩ := hflat (Ec.inverse.obj K)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp hk)
    (fun n ↦ (flat_comparison _).mpr (hf n))
  let c : (F.mapHomologicalComplex (.up ℤ)).obj (Ec.inverse.obj K) ≅
      ((forget D).mapHomologicalComplex (.up ℤ)).obj K :=
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app (Ec.inverse.obj K)) ≪≫
      ((forget D).mapHomologicalComplex (.up ℤ)).mapIso (Ec.counitIso.app K)
  refine ⟨kflat_iso c
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr h₁), fun n ↦ ?_⟩
  exact flat_iso ((HomologicalComplex.eval _ (.up ℤ) n).mapIso c)
    ((flat_comparison _).mp (h₂ n))

private theorem flat_resolution {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {g : T ≅ T} (D : Realization T l g) (K : CochainComplex (Pairs D) ℤ) :
    ∃ (L : CochainComplex (Pairs D) ℤ) (f : L ⟶ K),
      QuasiIso f ∧ KFlat D L ∧ FlatTerms D L ∧
        QuasiIso (((forget D).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  let _ := D.continuous
  let _ := D.inverseContinuous
  let _ := D.presentation.category
  let E : TwistedActionRingedSite.Modules D.presentation.coefficient ≌ Pairs D :=
    D.presentation.modules
  have : E.functor.Additive := action_additive D
  have : E.inverse.Additive := inferInstance
  let Ec := E.mapHomologicalComplex (.up ℤ)
  obtain ⟨P, p, hP, hflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (Ec.inverse.obj K)
  have : QuasiIso p := hp
  let f : Ec.functor.obj P ⟶ K := Ec.functor.map p ≫ Ec.counitIso.hom.app K
  have hq : QuasiIso f := by
    have : QuasiIso (Ec.functor.map p) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology p E.functor
    exact quasiIso_comp _ _
  refine ⟨Ec.functor.obj P, f, hq, ?_, ?_, ?_⟩
  · exact kflat_iso ((Ec.unitIso.app P)) hP
  · intro n
    let _ := SheafOfModules.isMonoidal_W_independentCoefficients D.presentation.coefficient
    let _ := SheafOfModules.monoidalCategory D.presentation.coefficient
    have h : SheafOfModules.IsFlatOnSite (J := D.presentation.topology)
        (R := D.presentation.coefficient) (P.X n) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso D.presentation.coefficient (P.X n)).symm
        (hflat n)
    exact flat_iso ((HomologicalComplex.eval _ (.up ℤ) n).mapIso (Ec.unitIso.app P)) h
  · have := hq
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f (forget D)

end WeilConjectures.WeilFrobeniusAction
