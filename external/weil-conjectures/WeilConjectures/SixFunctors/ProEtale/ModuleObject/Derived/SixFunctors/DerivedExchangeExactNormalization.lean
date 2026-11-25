/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleBaseChange
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
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Canonical ambient exchange and its restriction

Source: blueprint main-20261015, proper-base-change rational proof, paragraph (3)
(blueprint: lem-sfb-derived-exchange-exact-normalization).

The pullback comparison uses the published derived compositors. The exchange is their
mate under the published derived adjunctions, with no cartesianness requirement. Pullback
shifts are transported from the exact termwise functor along its canonical comparison;
pushforward shifts are the canonical K-injective shifts.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem triangle_morphism_of_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
    (B : F ⟶ G) [NatTrans.CommShift B ℤ] (T : Triangle C) :
    ∃ b : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T,
      b.hom₁ = B.app T.obj₁ ∧ b.hom₂ = B.app T.obj₂ ∧ b.hom₃ = B.app T.obj₃ := by
  refine ⟨{ hom₁ := B.app T.obj₁, hom₂ := B.app T.obj₂, hom₃ := B.app T.obj₃
            comm₁ := B.naturality T.mor₁
            comm₂ := B.naturality T.mor₂
            comm₃ := ?_ }, rfl, rfl, rfl⟩
  change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
    (shiftFunctor D (1 : ℤ)).map (B.app T.obj₁) =
      B.app T.obj₃ ≫ G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁
  rw [Category.assoc, NatTrans.shift_app_comm B (1 : ℤ),
    ← Category.assoc, B.naturality T.mor₃, Category.assoc]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical integer shifts on the actual K-flat pullback, transported along its
canonical comparison with the exact termwise pullback. This fixes the shift structure,
rather than selecting an unspecified one.
Source: blueprint rational proof (3), exact derived factorization
(blueprint: lem-sfb-derived-exchange-exact-normalization). -/
instance moduleObjectDerivedPullbackCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleObjectDerivedPullback Λ f).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

/-- The canonical K-injective integer shifts on the total derived module pushforward.
Source: Stacks Tag 015F, blueprint rational proof (3)
(blueprint: lem-sfb-derived-exchange-exact-normalization). -/
instance moduleObjectDerivedPushforwardCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleObjectDerivedPushforward Λ f).CommShift ℤ :=
  Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt (lowerStar Λ f)

/-- Use this equality before evaluating components: unfolding the exchange under
`NatTrans.app` also unfolds the whiskered functor constructions. -/
private theorem exchange_eq_mate {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) :
    moduleObjectDerivedExchange Λ sq =
      (mateEquiv (derivedUpperStarLowerStarAdjunction Λ p)
        (derivedUpperStarLowerStarAdjunction Λ p')
        (TwoSquare.mk _ _ _ _
          (moduleObjectDerivedPullbackSquareComparison Λ sq).hom)) := rfl

section ShiftProofs

@[instance_reducible]
private noncomputable def pullback_commShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar Λ f).leftDerivedFunctor.CommShift ℤ :=
  moduleObjectDerivedPullbackCommShift Λ f

attribute [local instance] pullback_commShift

private theorem pullbackComparison_inv_shift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm.hom ℤ :=
  Functor.CommShift.ofIso_compatibility
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

private theorem pullbackComparison_hom_shift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom ℤ := by
  have := pullbackComparison_inv_shift Λ f
  exact NatTrans.CommShift.of_iso_inv
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

private theorem pullback_triangulated {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleObjectDerivedPullback Λ f).IsTriangulated := by
  have := pullbackComparison_inv_shift Λ f
  exact Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm

private theorem pullbackComp_shift {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.CommShift (leftDerivedUpperStarComp Λ f g).hom ℤ := by
  have := pullbackComparison_hom_shift Λ f
  have := pullbackComparison_hom_shift Λ g
  have := pullbackComparison_hom_shift Λ (f ≫ g)
  have := pullbackComparison_inv_shift Λ f
  have := pullbackComparison_inv_shift Λ g
  have e : (leftDerivedUpperStarComp Λ f g).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g)).hom ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp Λ f g)).hom ≫
        (Functor.mapDerivedCategoryCompIso (upperStar Λ g) (upperStar Λ f)).inv ≫
        Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g).inv
          (upperStar Λ f).mapDerivedCategory ≫
        Functor.whiskerLeft (moduleObjectDerivedPullback Λ g)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv := by
    simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
      moduleObjectDerivedPullback]
  rw [e]
  infer_instance

private theorem pullbackSquare_shift {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) :
    NatTrans.CommShift (moduleObjectDerivedPullbackSquareComparison Λ sq).hom ℤ := by
  have := pullbackComp_shift Λ p' g
  have := pullbackComp_shift Λ g' p
  have := NatTrans.CommShift.of_iso_inv (leftDerivedUpperStarComp Λ p' g) ℤ
  have heq (a b : X' ⟶ Y) (h : a = b) :
      NatTrans.CommShift (eqToIso (congrArg (moduleObjectDerivedPullback Λ) h)).hom ℤ := by
    cases h
    change NatTrans.CommShift (𝟙 _) ℤ
    infer_instance
  have := heq _ _ sq.w.symm
  dsimp only [moduleObjectDerivedPullbackSquareComparison, Iso.trans_hom, Iso.symm_hom]
  infer_instance

private theorem derivedAdjunction_shift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction Λ f).CommShift ℤ := by
  have heq : derivedUpperStarLowerStarAdjunction Λ f =
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm := by
    exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f)
      ((upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac).symm
  rw [heq]
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ f)
  have := pullbackComparison_inv_shift Λ f
  exact Adjunction.commShift_ofNatIsoLeft _ _

private theorem exchange_shift {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) : NatTrans.CommShift (moduleObjectDerivedExchange Λ sq) ℤ := by
  have := derivedAdjunction_shift Λ p
  have := derivedAdjunction_shift Λ p'
  have := pullbackSquare_shift Λ sq
  exact NatTrans.CommShift.mateEquiv _ _ _

end ShiftProofs

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local reducible] Over.forget Comma.fst moduleObjectDerivedPullback
  moduleObjectDerivedPushforward moduleObjectDerivedExchange
attribute [local instance] moduleObjectDerivedPullbackCommShift
  moduleObjectDerivedPushforwardCommShift

set_option allowUnsafeReducibility true in
attribute [local irreducible] mateEquiv ObjectProperty.liftFullSubcategoryAdjunction
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar derivedUpperStarLowerStarAdjunction
  moduleObjectDerivedPullbackSquareComparison

variable (ℓ : ℕ) [hℓPrime : Fact ℓ.Prime] {k : Type u} [Field k]
  [hCharPrime : Fact (ringChar k).Prime] [hCharNe : Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [hXFiniteType : LocallyOfFiniteType X.hom]
  [hXQuasiCompact : QuasiCompact X.hom]
  [hXSeparated : IsSeparated X.hom]
  [hYFiniteType : LocallyOfFiniteType Y.hom]
  [hYQuasiCompact : QuasiCompact Y.hom]
  [hYSeparated : IsSeparated Y.hom]
  [hXPrimeFiniteType : LocallyOfFiniteType X'.hom]
  [hXPrimeQuasiCompact : QuasiCompact X'.hom]
  [hXPrimeSeparated : IsSeparated X'.hom]
  [hYPrimeFiniteType : LocallyOfFiniteType Y'.hom]
  [hYPrimeQuasiCompact : QuasiCompact Y'.hom]
  [hYPrimeSeparated : IsSeparated Y'.hom]
  {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : CommSq g' p' p g)

include ℓ hℓPrime hCharPrime hCharNe
  hXFiniteType hXQuasiCompact hXSeparated hYFiniteType hYQuasiCompact hYSeparated
  hXPrimeFiniteType hXPrimeQuasiCompact hXPrimeSeparated
  hYPrimeFiniteType hYPrimeQuasiCompact hYPrimeSeparated

-- Keep the canonical mate folded while transporting the exchange assertion.
set_option quotPrecheck false in
local notation "ambientMate" =>
  (mateEquiv
      (G := moduleObjectDerivedPullback Λ g.left)
      (H := moduleObjectDerivedPullback Λ g'.left)
      (L₁ := moduleObjectDerivedPullback Λ p.left)
      (R₁ := moduleObjectDerivedPushforward Λ p.left)
      (L₂ := moduleObjectDerivedPullback Λ p'.left)
      (R₂ := moduleObjectDerivedPushforward Λ p'.left)
      (derivedUpperStarLowerStarAdjunction Λ p.left)
      (derivedUpperStarLowerStarAdjunction Λ p'.left)
      (TwoSquare.mk _ _ _ _ (moduleObjectDerivedPullbackSquareComparison Λ
        (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).hom))

set_option linter.unusedSectionVars false

private theorem exchange_triangle
    [NatTrans.CommShift (moduleObjectDerivedExchange Λ
      (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)) ℤ]
    (T : Triangle (DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)))) :
      ∃ b : (moduleObjectDerivedPushforward Λ p.left ⋙
          moduleObjectDerivedPullback Λ g.left).mapTriangle.obj T ⟶
        (moduleObjectDerivedPullback Λ g'.left ⋙
          moduleObjectDerivedPushforward Λ p'.left).mapTriangle.obj T,
        b.hom₁ = (moduleObjectDerivedExchange Λ
          (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).app T.obj₁ ∧
        b.hom₂ = (moduleObjectDerivedExchange Λ
          (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).app T.obj₂ ∧
        b.hom₃ = (moduleObjectDerivedExchange Λ
          (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).app T.obj₃ :=
  triangle_morphism_of_shift _ _ _ T

/-- The ambient exchange has the prescribed counit normalization, both ambient functors
are exact with their fixed canonical shifts, and the exchange commutes with every integer
shift. No cartesian hypothesis is imposed.
Source: blueprint rational proof paragraph (3)
(blueprint: lem-sfb-derived-exchange-exact-normalization).

Proof:
1. The source exactness instances give the canonical comparison between the K-flat
pullback and its termwise derived functor. Transport triangulatedness along this
comparison, compatibly with the prescribed shifts. The K-injective construction makes the
additive module pushforward exact. Compose these exact functors.
2. Apply `lem-sp-canonical-right-derived-adjunction-shift` to the underived adjunction.
The derived-counit factorization of `lem-sc-derived-adjunction-from-underived` identifies
the published K-flat adjunction with its transport along the exact comparison: the two
counits agree on K-injectives, and every derived object is isomorphic to one of these.
Thus the actual unit and counit commute with the fixed shifts.
3. Expand the published compositor through the exact derived comparisons. The source
library's proved shift APIs for derived natural isomorphisms and composition comparisons
show that every factor commutes with shifts. The inverse compositor and the square
equality preserve this compatibility as well.
4. Write a = theta followed by the pullback of the counit. The exchange component is
G'(a) after the unit. Counit naturality and the adjunction triangle identity give
P'(B) followed by the counit = a.
5. The composition and whiskering rules of
`lem-weil-pbc-commshift-nattrans-comp-whisker` apply to the three factors of the mate.
They give the asserted compatibility with every canonical integer shift.
6. Naturality gives the first two squares of the image triangle morphism. Naturality at
its third arrow, followed by the shift equation for n = 1, gives the connecting square.
Exactness makes both image triangles distinguished.
-/
theorem moduleObjectDerivedExchange_exact_normalization :
    (∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left))), (moduleObjectDerivedPullback Λ p'.left).map
        ((moduleObjectDerivedExchange Λ (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).app K) ≫
      (derivedUpperStarLowerStarAdjunction Λ p'.left).counit.app
        ((moduleObjectDerivedPullback Λ g'.left).obj K) =
      (moduleObjectDerivedPullbackSquareComparison Λ
          (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).hom.app
        ((moduleObjectDerivedPushforward Λ p.left).obj K) ≫
      (moduleObjectDerivedPullback Λ g'.left).map
        ((derivedUpperStarLowerStarAdjunction Λ p.left).counit.app K)) ∧
    (moduleObjectDerivedPushforward Λ p.left ⋙
      moduleObjectDerivedPullback Λ g.left).IsTriangulated ∧
    (moduleObjectDerivedPullback Λ g'.left ⋙
      moduleObjectDerivedPushforward Λ p'.left).IsTriangulated ∧
    NatTrans.CommShift (moduleObjectDerivedExchange Λ
      (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)) ℤ ∧
    (∀ (T : Triangle (DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)))),
      T ∈ distTriang _ →
      ∃ b : (moduleObjectDerivedPushforward Λ p.left ⋙
          moduleObjectDerivedPullback Λ g.left).mapTriangle.obj T ⟶
        (moduleObjectDerivedPullback Λ g'.left ⋙
          moduleObjectDerivedPushforward Λ p'.left).mapTriangle.obj T,
        b.hom₁ = (moduleObjectDerivedExchange Λ
          (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).app T.obj₁ ∧
        b.hom₂ = (moduleObjectDerivedExchange Λ
          (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).app T.obj₂ ∧
        b.hom₃ = (moduleObjectDerivedExchange Λ
          (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).app T.obj₃) := by
  have hP (A B : Scheme.{u}) (f : A ⟶ B) := pullback_triangulated Λ f
  have hG (A B : Scheme.{u}) (f : A ⟶ B) :
      (moduleObjectDerivedPushforward Λ f).IsTriangulated :=
    Functor.instIsTriangulatedDerivedCategoryRightDerivedFunctor (lowerStar Λ f)
  have := hP _ _ g.left
  have := hP _ _ g'.left
  have := hG _ _ p.left
  have := hG _ _ p'.left
  have hB := exchange_shift Λ (show CommSq g'.left p'.left p.left g.left from
    (Over.forget _).map_commSq sq)
  refine ⟨?_, inferInstance, inferInstance, hB, fun T _ ↦ exchange_triangle Λ ℓ sq T⟩
  generalize hE : moduleObjectDerivedExchange Λ
    (show CommSq g'.left p'.left p.left g.left from
      (Over.forget _).map_commSq sq) = B
  have hcanonical : B = ambientMate :=
    hE.symm.trans (exchange_eq_mate Λ
      (show CommSq g'.left p'.left p.left g.left from
        (Over.forget _).map_commSq sq))
  rw [hcanonical]
  intro K
  simp only [mateEquiv_counit]

set_option allowUnsafeReducibility true in
attribute [local reducible] PreservesBoundedConstructiblePushforwards

omit hXPrimeFiniteType hXPrimeQuasiCompact hXPrimeSeparated
  hYPrimeFiniteType hYPrimeQuasiCompact hYPrimeSeparated in
private theorem conditional_counit_hom
    (H : PreservesBoundedConstructiblePushforwards Λ k)
    (f : X ⟶ Y) (K : BoundedConstructible (condensedRingObj Λ X.left)) :
    ((boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H f ℓ).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ f.left).counit.app K.obj := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction Λ f.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
    (boundedConstructibleLowerStarOfPreservesCompatibility Λ H f).symm K
  change ((boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H f ℓ).counit.app
      K).hom = 𝟙 _ ≫ (moduleObjectDerivedPullback Λ f.left).map (𝟙 _) ≫
        (derivedUpperStarLowerStarAdjunction Λ f.left).counit.app K.obj at h
  rw [CategoryTheory.Functor.map_id] at h
  simpa only [Category.id_comp] using h

omit hXPrimeFiniteType hXPrimeQuasiCompact hXPrimeSeparated
  hYPrimeFiniteType hYPrimeQuasiCompact hYPrimeSeparated in
private theorem conditional_pullback_map_hom (f : X ⟶ Y)
    {J K : BoundedConstructible (condensedRingObj Λ Y.left)} (v : J ⟶ K) :
    ((boundedConstructibleUpperStar Λ ℓ f).map v).hom =
      (moduleObjectDerivedPullback Λ f.left).map v.hom := rfl

omit hXPrimeFiniteType hXPrimeQuasiCompact hXPrimeSeparated
  hYPrimeFiniteType hYPrimeQuasiCompact hYPrimeSeparated in
private theorem conditional_pullback_obj_val (f : X ⟶ Y)
    (J : BoundedConstructible (condensedRingObj Λ Y.left)) :
    ((boundedConstructibleUpperStar Λ ℓ f).obj J).obj =
      (moduleObjectDerivedPullback Λ f.left).obj J.obj := rfl

omit hXPrimeFiniteType hXPrimeQuasiCompact hXPrimeSeparated
  hYPrimeFiniteType hYPrimeQuasiCompact hYPrimeSeparated in
private theorem conditional_pushforward_obj_val
    (H : PreservesBoundedConstructiblePushforwards Λ k) (f : X ⟶ Y)
    (J : BoundedConstructible (condensedRingObj Λ X.left)) :
    ((boundedConstructibleLowerStarOfPreserves Λ H f).obj J).obj =
      (lowerStar Λ f.left).rightDerivedFunctor.obj J.obj := rfl

private theorem conditional_baseChange_eq_squareExchange
    (H : PreservesBoundedConstructiblePushforwards Λ k) :
    boundedConstructibleBaseChangeOfPreserves Λ ℓ H sq =
      Adjunction.squareExchange
        (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p ℓ)
        (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p' ℓ)
        (boundedConstructibleUpperStar Λ ℓ g) (boundedConstructibleUpperStar Λ ℓ g')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq) := by
  exact (Adjunction.squareExchange_eq_unit_square_counit
    (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p ℓ)
    (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p' ℓ)
    (boundedConstructibleUpperStar Λ ℓ g) (boundedConstructibleUpperStar Λ ℓ g')
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq)).symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] Adjunction.homEquiv
private theorem conditional_baseChange_counit
    (H : PreservesBoundedConstructiblePushforwards Λ k)
    (K : BoundedConstructible (condensedRingObj Λ X.left)) :
    (boundedConstructibleUpperStar Λ ℓ p').map
        ((boundedConstructibleBaseChangeOfPreserves Λ ℓ H sq).app K) ≫
      (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p' ℓ).counit.app
        ((boundedConstructibleUpperStar Λ ℓ g').obj K) =
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app
        ((boundedConstructibleLowerStarOfPreserves Λ H p).obj K) ≫
      (boundedConstructibleUpperStar Λ ℓ g').map
        ((boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p ℓ).counit.app K) := by
  exact (congrArg (fun B ↦ (boundedConstructibleUpperStar Λ ℓ p').map (B.app K) ≫
    (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p' ℓ).counit.app
      ((boundedConstructibleUpperStar Λ ℓ g').obj K))
    (conditional_baseChange_eq_squareExchange Λ ℓ sq H)).trans
      (Adjunction.squareExchange_map_counit
        (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p ℓ)
        (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p' ℓ)
        (boundedConstructibleUpperStar Λ ℓ g) (boundedConstructibleUpperStar Λ ℓ g')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq) K)

/-- Compare a restricted exchange with an ambient transformation by their counit equations.
Keeping both square comparisons as parameters avoids expanding their constructions
while normalizing the underlying full-subcategory objects. -/
private theorem baseChange_of_counit_equations
    (H : PreservesBoundedConstructiblePushforwards Λ k)
    [(boundedConstructible (condensedRingObj Λ X.left)).IsTriangulated]
    [(boundedConstructible (condensedRingObj Λ Y.left)).IsTriangulated]
    [(boundedConstructible (condensedRingObj Λ X'.left)).IsTriangulated]
    [(boundedConstructible (condensedRingObj Λ Y'.left)).IsTriangulated]
    (B : boundedConstructibleLowerStarOfPreserves Λ H p ⋙
        boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleLowerStarOfPreserves Λ H p')
    (E : moduleObjectDerivedPushforward Λ p.left ⋙
        moduleObjectDerivedPullback Λ g.left ⟶
      moduleObjectDerivedPullback Λ g'.left ⋙ moduleObjectDerivedPushforward Λ p'.left)
    (θ : boundedConstructibleUpperStar Λ ℓ g ⋙
        boundedConstructibleUpperStar Λ ℓ p' ≅
      boundedConstructibleUpperStar Λ ℓ p ⋙ boundedConstructibleUpperStar Λ ℓ g')
    (θα : moduleObjectDerivedPullback Λ g.left ⋙
        moduleObjectDerivedPullback Λ p'.left ≅
      moduleObjectDerivedPullback Λ p.left ⋙ moduleObjectDerivedPullback Λ g'.left)
    (hc : ∀ (K : BoundedConstructible (condensedRingObj Λ X.left)),
      (boundedConstructibleUpperStar Λ ℓ p').map (B.app K) ≫
        (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p' ℓ).counit.app
          ((boundedConstructibleUpperStar Λ ℓ g').obj K) =
      θ.hom.app
          ((boundedConstructibleLowerStarOfPreserves Λ H p).obj K) ≫
        (boundedConstructibleUpperStar Λ ℓ g').map
          ((boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p ℓ).counit.app K))
    (hθ : ∀ (K : BoundedConstructible (condensedRingObj Λ Y.left)),
      (θ.hom.app K).hom =
      θα.hom.app K.obj)
    (hnorm : (∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left))), (moduleObjectDerivedPullback Λ p'.left).map
        (E.app K) ≫
      (derivedUpperStarLowerStarAdjunction Λ p'.left).counit.app
        ((moduleObjectDerivedPullback Λ g'.left).obj K) =
      θα.hom.app
        ((moduleObjectDerivedPushforward Λ p.left).obj K) ≫
      (moduleObjectDerivedPullback Λ g'.left).map
        ((derivedUpperStarLowerStarAdjunction Λ p.left).counit.app K))) :
    ∀ (K : BoundedConstructible (condensedRingObj Λ X.left)),
      (B.app K).hom =
      E.app K.obj := by
  intro K
  have hb := congrArg (fun v ↦ v.hom) (hc K)
  simp only [ObjectProperty.FullSubcategory.comp_hom] at hb
  have hL := congrArg₂ (fun u v ↦ u ≫ v)
    (conditional_pullback_map_hom Λ ℓ p'
      (B.app K))
    (conditional_counit_hom Λ ℓ H p' ((boundedConstructibleUpperStar Λ ℓ g').obj K))
  have hmap := (conditional_pullback_map_hom Λ ℓ g'
    ((boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H p ℓ).counit.app K)).trans
      (congrArg (moduleObjectDerivedPullback Λ g'.left).map
        (conditional_counit_hom Λ ℓ H p K))
  have hR := congrArg₂ (fun u v ↦ u ≫ v)
    (hθ ((boundedConstructibleLowerStarOfPreserves Λ H p).obj K)) hmap
  have h := hL.symm.trans (hb.trans hR)
  simp only [conditional_pullback_obj_val, conditional_pushforward_obj_val Λ ℓ H p] at h
  have hEq := h.trans (hnorm K.obj).symm
  let v :
      (moduleObjectDerivedPullback Λ g.left).obj
        ((moduleObjectDerivedPushforward Λ p.left).obj K.obj) ⟶
      (moduleObjectDerivedPushforward Λ p'.left).obj
        ((moduleObjectDerivedPullback Λ g'.left).obj K.obj) :=
    (B.app K).hom
  dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj] at hEq
  simp only [conditional_pullback_obj_val, conditional_pushforward_obj_val Λ ℓ H p] at hEq
  change v = _
  apply ((derivedUpperStarLowerStarAdjunction Λ p'.left).homEquiv
    ((moduleObjectDerivedPullback Λ g.left).obj
      ((moduleObjectDerivedPushforward Λ p.left).obj K.obj))
    ((moduleObjectDerivedPullback Λ g'.left).obj K.obj)).symm.injective
  simp only [Adjunction.homEquiv_counit]
  dsimp only [v, moduleObjectDerivedPullback, moduleObjectDerivedPushforward,
    boundedConstructibleUpperStar, boundedConstructibleLowerStarOfPreserves,
    ObjectProperty.lift, ObjectProperty.ι, inducedFunctor,
    CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj] at hEq ⊢
  exact hEq

/-- The bounded-constructible instance of the restriction statement, expressed with the
recorded base-change declaration. Triangulatedness and preservation are hypotheses;
the comparison restriction hypothesis is the equality of the actual components.
Source: blueprint rational proof (3), bounded-constructible specialization
(blueprint: lem-sfb-derived-exchange-exact-normalization).

Proof: identify the three-step restricted base-change map with `Adjunction.squareExchange`.
Its counit equation follows from `Adjunction.squareExchange_map_counit`. The fully faithful
restriction API identifies the underlying restricted counits with the ambient counits;
the restricted pullback acts by the ambient map. Apply the square-component hypothesis
to obtain the same ambient counit equation as the normalized exchange. The inverse of
the ambient adjunction hom equivalence is injective, so the two components agree.
All restricted functor and adjunction constructions remain the published ones.
-/
theorem boundedConstructibleBaseChangeOfPreserves_app_eq_moduleObjectDerivedExchange
    (H : PreservesBoundedConstructiblePushforwards Λ k)
    [(boundedConstructible (condensedRingObj Λ X.left)).IsTriangulated]
    [(boundedConstructible (condensedRingObj Λ Y.left)).IsTriangulated]
    [(boundedConstructible (condensedRingObj Λ X'.left)).IsTriangulated]
    [(boundedConstructible (condensedRingObj Λ Y'.left)).IsTriangulated]
    (hθ : ∀ (K : BoundedConstructible (condensedRingObj Λ Y.left)),
      ((boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom.app K).hom =
      (moduleObjectDerivedPullbackSquareComparison Λ
        (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).hom.app K.obj) :
    ∀ (K : BoundedConstructible (condensedRingObj Λ X.left)),
      ((boundedConstructibleBaseChangeOfPreserves Λ ℓ H sq).app K).hom =
      (moduleObjectDerivedExchange Λ (show CommSq g'.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).app K.obj := by
  exact baseChange_of_counit_equations Λ ℓ (@H)
    (boundedConstructibleBaseChangeOfPreserves Λ ℓ H sq)
    (moduleObjectDerivedExchange Λ
      (show CommSq g'.left p'.left p.left g.left from
        (Over.forget _).map_commSq sq))
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq)
    (moduleObjectDerivedPullbackSquareComparison Λ
      (show CommSq g'.left p'.left p.left g.left from
        (Over.forget _).map_commSq sq))
    (conditional_baseChange_counit Λ ℓ sq (@H)) hθ
    (moduleObjectDerivedExchange_exact_normalization Λ ℓ sq).1

end AlgebraicGeometry.ProEtale.CondensedRing
