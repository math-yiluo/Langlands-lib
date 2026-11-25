/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
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
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionConstantModelConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Open extension preserves constructibility and specified Tor bounds

Source: blueprint main-20261015, chap-Construction-of-f,
sk-thm-sf-comp-composition/det-sf-comp-composition-interchange.proof.md, proof (3)
(blueprint: lem-sfb-open-extension-zero-constructible-finite-tor).

The categories are the ordinary unbounded derived categories of internal modules.
Constant scalar-model constructibility and general ring-object constructibility are
kept distinct. The cohomology and Tor intervals are independent.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem torAmplitudeIn_iff_derivedTensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (a b : ℤ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    DerivedCategory.torAmplitudeIn _ a b K ↔ ∀ N,
      DerivedCategory.homologyConcentratedIn a b
        (((derivedTensor Λ X).obj K).obj ((DerivedCategory.singleFunctor _ 0).obj N)) := by
  delta DerivedCategory.torAmplitudeIn derivedTensor CategoryTheory.Mod.derivedMonoidalCategory
    DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  rfl

private theorem finiteStratification_models {X : Scheme.{u}}
    (S : Scheme.Stratification X) (P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop)
    (hP : ∀ t : Fin S.n, P (S.domain t) (S.immersion t)) :
    ∃ T : Scheme.FiniteLocallyClosedStratification X,
      (∀ t : Fin T.n, Topology.IsConstructible (T.stratum t)) ∧
      ∀ t : Fin T.n, P (T.domain t) (T.immersion t) := by
  let T : Scheme.FiniteLocallyClosedStratification X :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  exact ⟨T, S.isConstructible_stratum, hP⟩

attribute [local irreducible] derivedTensor

/-- Exact open extension preserves bounded constant-model constructibility, finite Tor
amplitude, the supplied cohomological interval, and the supplied Tor interval. Its output
is also bounded constructible in the general locally-finitely-presented ring-object sense.
No admissibility or completeness hypothesis is imposed on the condensed coefficient ring.

Source: blueprint main-20261015, det-sf-comp-composition-interchange.proof.md, proof (3);
lem-sfb-dc-open-lower-shriek-preserves.proof.md; det-lem-int-tensor-projection.proof.md,
open immersions and derived version
(blueprint: lem-sfb-open-extension-zero-constructible-finite-tor).

Proof: finite type over the field and quasi-compactness make U and X Noetherian.
For every cohomology module use the proved module-level extension theorem, which
adjoins the reduced closed complement with its zero scalar model. Transport the
resulting models through the exact-functor homology isomorphism; exactness also
preserves boundedness and the specified cohomology interval. For any test module N,
the open projection isomorphism and the exact pullback comparison on N[0] identify
the tensor of the extended complex with the extension of A tensor j^*N. Exactness
preserves its cohomology interval [a,b], giving the stated Tor interval. Finally,
finite constant local models imply local finite presentation. Restriction along
the inverse coefficient isomorphism transports this to the general ring-object
constructibility predicate on the same stratification. -/
theorem openExtension_constructible_finiteTor
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left]
    (A : ConstantModelConstructibleFiniteTor Λ U.left)
    (m n a b : ℤ)
    (hcoh : DerivedCategory.homologyConcentratedIn m n A.obj)
    (htor : DerivedCategory.torAmplitudeIn _ a b A.obj) :
    (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
      ((openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj A.obj) ∧
    DerivedCategory.homologyConcentratedIn m n
      ((openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj A.obj) ∧
    DerivedCategory.torAmplitudeIn _ a b
      ((openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj A.obj) ∧
    boundedConstructible (condensedRingObj Λ X.left)
      ((openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj A.obj) := by
  classical
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have : IsNoetherian U.left := ⟨⟩
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := ⟨⟩
  let : U.left.Over (Spec (.of k)) := ⟨U.hom⟩
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (U.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType U.hom›
  have : QuasiCompact (U.left ↘ Spec (.of k)) := ‹QuasiCompact U.hom›
  have : IsSeparated (U.left ↘ Spec (.of k)) := ‹IsSeparated U.hom›
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  have : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  have : j.left.IsOver (Spec (.of k)) := ⟨j.w⟩
  let F := openImmersionLowerShriek Λ j.left
  have extend (M) (hM : IsConstantModelConstructible Λ U.left M) :
      IsConstantModelConstructible Λ X.left (F.obj M) := by
    obtain ⟨S, hS⟩ := (show IsConstantModelConstructible Λ U.left M =
      IsFiniteConstantStratified Λ U.left M from
        ite_eq_left ⟨inferInstance, inferInstance⟩).mp hM
    obtain ⟨T, hT, hmodels⟩ := finiteStratification_models S
      (fun Y f ↦ HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M)) hS
    have h := constantModelConstructible_openImmersionLowerShriek ℓ (ringChar k)
      (Fact.out : ringChar k ≠ ℓ) k Λ (U := U.left) (X := X.left) j.left M T hT hmodels
    set_option backward.isDefEq.respectTransparency true in
      exact h.1
  have hc : constantModelBoundedConstructible Λ X.left
      (F.mapDerivedCategory.obj A.obj) := by
    refine ⟨F.bounded_mapDerivedCategory_obj A.property.1.1, fun q ↦ ?_⟩
    let e := (F.mapDerivedCategoryHomologyFunctorIso q).app A.obj
    have h := extend _ (A.property.1.2 q)
    obtain ⟨S, hS⟩ := (show IsConstantModelConstructible Λ X.left _ =
      IsFiniteConstantStratified Λ X.left _ from
        ite_eq_left ⟨inferInstance, inferInstance⟩).mp h
    apply (show IsConstantModelConstructible Λ X.left _ =
      IsFiniteConstantStratified Λ X.left _ from ite_eq_left ⟨inferInstance, inferInstance⟩).mpr
    refine ⟨S, fun t ↦ ?_⟩
    obtain ⟨C, hC⟩ := hS t
    refine ⟨C, fun r ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := hC r
    exact ⟨P, hP, ⟨(upperStar Λ (C.f r)).mapIso
      ((upperStar Λ (S.immersion t)).mapIso e.symm) ≪≫ eP⟩⟩
  have hp := openImmersionTensorProjection (S := U.left) (X := X.left) Λ k j.left
  let projection := Classical.choice hp
  have ht : DerivedCategory.torAmplitudeIn _ a b (F.mapDerivedCategory.obj A.obj) := by
    apply (torAmplitudeIn_iff_derivedTensor Λ X.left a b _).mpr
    intro N
    have eN := (projection.app A.obj).app ((DerivedCategory.singleFunctor _ 0).obj N)
    change ((derivedTensor Λ X.left).obj (F.mapDerivedCategory.obj A.obj)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      F.mapDerivedCategory.obj (((derivedTensor Λ U.left).obj A.obj).obj
        ((upperStar Λ j.left).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj N))) at eN
    let es := ((upperStar Λ j.left).mapDerivedCategorySingleFunctor 0).app N
    have h := F.homologyConcentratedIn_mapDerivedCategory_obj
      ((torAmplitudeIn_iff_derivedTensor Λ U.left a b A.obj).mp htor
        ((upperStar Λ j.left).obj N))
    exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (eN ≪≫ F.mapDerivedCategory.mapIso
        (((derivedTensor Λ U.left).obj A.obj).mapIso es)).symm h
  refine ⟨⟨hc, a, b, ht⟩,
    F.homologyConcentratedIn_mapDerivedCategory_obj hcoh, ht, hc.1, ?_⟩
  intro q
  obtain ⟨S, hS⟩ := (show IsConstantModelConstructible Λ X.left _ =
    IsFiniteConstantStratified Λ X.left _ from
      ite_eq_left ⟨inferInstance, inferInstance⟩).mp (hc.2 q)
  refine ⟨S, fun t ↦ ?_⟩
  let α := condensedPullbackHom Λ (S.immersion t)
  apply localFinitePresentation_of_comap (inv α)
  have h := HasFiniteConstantLocalModel.isLocallyFinitelyPresented Λ _ (hS t)
  let e := (Mod.extendScalarsIsoComapInv α).app
    (((ProEtale.upperStar Ab.{u + 1} (S.immersion t)).mapMod
      (condensedRingObj Λ X.left)).obj
      ((DerivedCategory.homologyFunctor _ q).obj (F.mapDerivedCategory.obj A.obj)))
  unfold upperStar at h
  exact localFinitePresentation_of_iso e h

end AlgebraicGeometry.ProEtale.CondensedRing
