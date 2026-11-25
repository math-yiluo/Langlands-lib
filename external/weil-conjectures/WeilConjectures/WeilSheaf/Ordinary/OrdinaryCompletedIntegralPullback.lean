/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
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
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.ProperBaseChange.ProperIntegralStrictModelComparison
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryIntegralLocalModels
import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization

/-!
# Ordinary and completed integral pullback

Source: Bhatt--Scholze, Lemma 6.5.9, Proposition 6.6.11 and Remark 6.8.15;
Stacks Project, Tags 06YY and 08TC
(blueprint: lem-tw-ordinary-completed-integral-pullback).

The ordinary pullback uses the adjoint of the completed coefficient map fixed by
all finite projections. The comparison is fixed on flat-term K-flat representatives
by the quotient augmentation and the zero second coordinate of the strict Roos cone.

## Main definitions

* `ordinaryIntegralDerivedPull`: ordinary unbounded ringed pullback before completion.
* `ordinaryIntegralCompletionChain`: the prescribed (quotients, zero) cone map.
* `ordinaryIntegralCompletionComparison`: its uniquely normalized derived descent.

## Main statements

* `ordinaryCompletedIntegralPullback`: constructibility and invertibility of this comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.scalarReductionSourceDerived
attribute [-instance] WeilConjectures.scalarReductionTargetDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem ordinaryIntrinsicComplete_iso
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {K L : PbcCompletedDerived T d} (e : K ≅ L)
    (hK : PbcIsIntrinsicallyComplete T d K) : PbcIsIntrinsicallyComplete T d L := by
  obtain ⟨r, a, ha, C, eC, hC⟩ := hK
  refine ⟨r, a, ha, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison T d).inv).mapIso e, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

private theorem ordinaryComparison_isIso_of_detailed
    (K : DerivedCategory (integralTowerModules.{u, u} l E Y))
    (hK : PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)
      ((integralDetailedTransport Y l E).obj K))
    (hL : PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E)
      ((integralDetailedTransport X l E).obj
        ((ordinaryIntegralDerivedPull l E f).obj K))) :
    IsIso ((ordinaryIntegralCompletionComparison l E f).app K) := by
  obtain ⟨a, b, _, hab⟩ := pbc_proper_integral_strict_model_comparison l E f
  let d := pbcIntegralDatum l E
  let M := (integralDetailedTransport Y l E).obj K
  let L := (completedOrdinaryPullback f d).obj M
  have hcomplete : PbcIsIntrinsicallyComplete X d L :=
    ordinaryIntrinsicComplete_iso X d (a.derivedIso.app K) hL
  let J : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y d) := ⟨M, hK⟩
  obtain ⟨q, hq, _⟩ := pbcActualCompletedPullback_tower d f
  have hu : IsIso ((pbcActualCompletionUnit d X).app L) :=
    (Adjunction.ofIsRightAdjoint
      (ObjectProperty.ι (PbcIsIntrinsicallyComplete X d))).isIso_unit_app_iff_mem_essImage.mpr
        ⟨⟨L, hcomplete⟩, ⟨Iso.refl _⟩⟩
  have hv : IsIso ((pbcActualStrictCompletedPullUnit d f).app M ≫ q.hom.app J) := by
    rw [hq J]
    exact hu
  have heq : (pbcActualStrictCompletedPullUnit d f).app M =
      completedPullbackComparison f d M := by
    simp only [pbcActualStrictCompletedPullUnit, completedPullbackComparison,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.map_comp,
      Category.id_comp]
  rw [heq] at hv
  let := hv
  have : IsIso (completedPullbackComparison f d M) :=
    IsIso.of_isIso_comp_right _ (q.hom.app J)
  have hw : IsIso ((integralDetailedTransport X l E).map
      ((ordinaryIntegralCompletionComparison l E f).app K) ≫ b.hom.app K) := by
    rw [hab K]
    infer_instance
  have : IsIso ((integralDetailedTransport X l E).map
      ((ordinaryIntegralCompletionComparison l E f).app K)) :=
    let := hw
    IsIso.of_isIso_comp_right _ (b.hom.app K)
  exact isIso_of_reflects_iso _ (integralDetailedTransport X l E)

private theorem ordinaryIntegralStratifiedPerfectPullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
    (K : DerivedCategory (integralTowerModules.{u, u} l E Y))
    (hK : IsIntegralStratifiedPerfect Y (pbcIntegralDatum l E)
      ((integralDetailedTransport Y l E).obj K)) :
    IsIntegralStratifiedPerfect X (pbcIntegralDatum l E)
      ((integralDetailedTransport X l E).obj ((ordinaryIntegralDerivedPull l E f).obj K)) := by
  obtain ⟨a, _, _, _⟩ := pbc_proper_integral_strict_model_comparison l E f
  let c := a.derivedIso.app K ≪≫
    (pullbackDatumOrdinaryTransport f (pbcIntegralDatum l E)).app
      ((integralDetailedTransport Y l E).obj K)
  obtain ⟨s, hs⟩ := integralStratifiedPerfect_pullback (pbcIntegralDatum l E) f _ hK
  refine ⟨s, fun i ↦ ?_⟩
  obtain ⟨V, hV, hm⟩ := hs i
  refine ⟨V, hV, fun U v hv ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hm U v hv
  exact ⟨P, hP, ⟨localMapIso (s.immersion i) (pbcAdicCompletion X (pbcIntegralDatum l E))
    U c ≪≫ e⟩⟩

/-- Ordinary pullback of an integral constructible object is constructible, and its
specified completion map is invertible, naturally and independently of its resolution.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.5.9 and Remark 6.8.15
(blueprint: lem-tw-ordinary-completed-integral-pullback).
Proof:
1. By integral-stratified-perfect-characterization (detailed form) on Y, the transport of K
to the completed-coefficient presentation has finite constructible stratified pro-etale
local models by bounded perfect R-complexes, and is intrinsically complete.
2. The normalized strict-model comparison gives a natural isomorphism a from the transported
ordinary pullback to completedOrdinaryPullback, which is the datum pullback d.pull f.
By integral-local-model-pullback, d.pull f carries the stratified local models of K to
stratified local models on X; transport them back along a. The characterization on X then
gives sfIntegralConstructible of the ordinary pullback, including intrinsic completeness.
3. Intrinsic completeness is invariant under isomorphism, so completedOrdinaryPullback of
the transport of K is intrinsically complete. Hence the completion reflector unit there is
invertible (essential image of the fully faithful complete inclusion). The actual strict
tower theorem identifies this unit with completedPullbackComparison followed by an
isomorphism, so completedPullbackComparison is invertible.
4. The strict-model comparison equation says transport of the specified comparison followed
by the isomorphism b equals a followed by completedPullbackComparison. Cancel b and reflect
isomorphisms through the detailed coefficient transport, an equivalence.
No separatedness or base-field structure is used. -/
theorem ordinaryCompletedIntegralPullback
    [IsNoetherian X] [IsNoetherian Y]
    (_hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hYdim : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (_hXinv : IsUnit (l : Γ(X, ⊤))) (_hYinv : IsUnit (l : Γ(Y, ⊤)))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l E X ((ordinaryIntegralDerivedPull l E f).obj K) ∧
      IsIso ((ordinaryIntegralCompletionComparison l E f).app K) := by
  have hsource :=
    (integralStratifiedPerfectCharacterization Y l E _hYdim _hYinv
      ((integralDetailedTransport Y l E).obj K)).1.mp
      ((integralStratifiedPerfectDetailed Y l E _hYdim _hYinv K).mp hK)
  have htarget := ordinaryIntegralStratifiedPerfectPullback l E f K hsource
  have hout :=
    (integralStratifiedPerfectDetailed X l E _hXdim _hXinv _).mpr
      ((integralStratifiedPerfectCharacterization X l E _hXdim _hXinv _).1.mpr htarget)
  refine ⟨hout, ordinaryComparison_isIso_of_detailed l E f K ?_ ?_⟩
  · exact ((integralStratifiedPerfectDetailed Y l E _hYdim _hYinv K).mp hK).1
  · exact ((integralStratifiedPerfectDetailed X l E _hXdim _hXinv _).mp hout).1

end WeilConjectures
