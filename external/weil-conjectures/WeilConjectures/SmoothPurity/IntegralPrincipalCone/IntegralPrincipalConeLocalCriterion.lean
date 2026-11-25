/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PrincipalConeTower
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
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
public import Mathlib.CategoryTheory.Sites.Equivalence
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.CategoryTheory.Native.NativePrincipalConeCriterion

/-! # The local criterion for a principal cone completion

Source: Stacks Tags 0999, 099B and 0A0E.
(blueprint: lem-pur-integral-principal-cone-local-criterion) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralPrincipalCone

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{t})

/-- The localization test on the actual slice, with independent coefficient size.
Source: Stacks 0999 (blueprint: lem-pur-integral-principal-cone-local-criterion). -/
def localTest (K : IntegralOnSlice.D l E T none) (U : T.ProEt)
    (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections) :
    IntegralOnSlice.D l E T (some U) :=
  letI : HasSheafify (IntegralOnSlice.topology T (some U))
      CommRingCat.{max u (t + 1)} :=
    letI : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T (some U)) :=
      essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  letI := HasDerivedCategory.standard
    (SheafOfModules.{max u (t + 1)} ((IntegralOnSlice.rings l E T none).over U))
  (IntegralOnSlice.hom l E T (some U)).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalizationOfUniverses (IntegralOnSlice.ring l E T (some U)) s)),
      ringedSiteDerivedRestrictionOfUniverses (IntegralOnSlice.rings l E T none) U K)

/-- Vanishing for every locally divisible section on every slice.
Source: Stacks 0999 (blueprint: lem-pur-integral-principal-cone-local-criterion). -/
def locallyComplete
    (σ : ∀ U : T.ProEtᵒᵖ, (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    (K : IntegralOnSlice.D l E T none) : Prop :=
  ∀ (U : T.ProEt)
    (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections),
    (∃ S : Sieve U, S ∈ AlgebraicGeometry.Scheme.ProEt.topology T U ∧
      ∀ (V : T.ProEt) (f : V ⟶ U), S f →
        ∃ c : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj (op V),
          s.val (op (Over.mk f)) = σ (op V) * c) →
      IsZero (localTest l E T K U s)

private def localTestIso {K L : IntegralOnSlice.D l E T none} (e : K ≅ L)
    (U : T.ProEt)
    (s : ((IntegralOnSlice.ring l E T (some U)).obj ⋙ forget CommRingCat).sections) :
    localTest l E T K U s ≅ localTest l E T L U s := by
  letI : HasSheafify (IntegralOnSlice.topology T (some U))
      CommRingCat.{max u (t + 1)} :=
    letI : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site T (some U)) :=
      essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  let R := IntegralOnSlice.rings l E T none
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)} (R.over U))
  let F := SheafOfModules.overFunctor.{max u (t + 1)} R U
  letI : PreservesFiniteLimits F := (SheafOfModules.overFunctor_exact_ofUniverses R U).1
  letI : PreservesFiniteColimits F :=
    (SheafOfModules.overFunctor_exact_ofUniverses R U).2
  let e' := SheafOfModules.overFunctor_derivedRestrictionIso R U K ≪≫
    F.mapDerivedCategory.mapIso e ≪≫
      (SheafOfModules.overFunctor_derivedRestrictionIso R U L).symm
  exact (IntegralOnSlice.hom l E T (some U)).mapIso ((Iso.refl _).prod e')

private theorem locallyComplete_iso
    (σ : ∀ U : T.ProEtᵒᵖ, (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    {K L : IntegralOnSlice.D l E T none} (e : K ≅ L) :
    locallyComplete l E T σ K ↔ locallyComplete l E T σ L := by
  constructor
  · intro h U s hs
    exact (h U s hs).of_iso (localTestIso l E T e U s).symm
  · intro h U s hs
    exact (h U s hs).of_iso (localTestIso l E T e U s)

/-- The principal cone completion is locally complete, and its specified unit is
invertible exactly for locally complete inputs. The scalar is any natural section;
no regularity, boundedness or flatness of the input complex is needed.

Source: Stacks Tags 0999, 099B and 0A0E, the singleton Koszul completion reflector.
(blueprint: lem-pur-integral-principal-cone-local-criterion).

Proof: replace the essentially small ringed site by its small model at coefficient
universe max(u,t+1). Exact module restriction is an equivalence, preserving the scalar,
localizations, internal Hom, products and mapping cones. Apply the ringed Koszul
completion reflector to the singleton scalar. Its negative Koszul tensor complex is
canonically the cone of scalar multiplication on P, and its (scalar,1) transitions and
degree-zero unit are those of PrincipalCone. The image ideal of multiplication by the
scalar consists exactly of the sections locally divisible by that scalar; sheaf image
and local lifting give the displayed covering-sieve formulation, including on every
slice. The reflector gives completeness of its output and the unit criterion. Transport
back through the site equivalence and then through e. For a zero scalar localization
at every ideal section is zero, and the same construction still applies. -/
theorem localCriterion
    (σ : ∀ U : T.ProEtᵒᵖ, (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    (_hσ : ∀ {U V : T.ProEtᵒᵖ} (f : U ⟶ V),
      (completedIntegralCoefficientSheafUnrestricted l E T).obj.map f (σ U) = σ V)
    (P : IntegralOnSlice.Cx l E T none) (μ : End P)
    (_hμ : ∀ (q : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x = σ U • x)
    (K : IntegralOnSlice.D l E T none) (e : DerivedCategory.Q.obj P ≅ K) :
    locallyComplete l E T σ (DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion μ)) ∧
      (locallyComplete l E T σ K ↔
        IsIso (e.inv ≫ DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ))) := by
  let J := IntegralOnSlice.topology T none
  let R := IntegralOnSlice.ring l E T none
  let Rg := IntegralOnSlice.rings l E T none
  let a : (R.obj ⋙ forget CommRingCat).sections := ⟨σ, _hσ⟩
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    IntegralOnSlice.abSheafify.{t, u} T none
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    IntegralOnSlice.abLocallyBijective.{t, u} T none
  let : ∀ U : IntegralOnSlice.Site T none, HasSheafify (J.over U) AddCommGrpCat.{max u (t + 1)} :=
    fun U ↦ IntegralOnSlice.abSheafify.{t, u} T (some U)
  let : ∀ U : IntegralOnSlice.Site T none, (J.over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
    fun U ↦ IntegralOnSlice.abLocallyBijective.{t, u} T (some U)
  let : ∀ U : IntegralOnSlice.Site T none, HasSheafify (J.over U) CommRingCat.{max u (t + 1)} :=
    fun U ↦
      letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
      hasSheafifyEssentiallySmallSite _ _
  let : HasDerivedCategory (SheafOfModules.{max u (t + 1)} Rg) :=
    IntegralOnSlice.hasDerived l E T none
  let : ∀ U : IntegralOnSlice.Site T none,
      HasDerivedCategory (SheafOfModules.{max u (t + 1)} (Rg.over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  have testIso (N : IntegralOnSlice.D l E T none) (U : T.ProEt)
      (s : ((R.over U).obj ⋙ forget CommRingCat).sections) :
      localTest l E T N U s ≅ principalLocalTest.{t + 1, t, u} R N U s := by
    letI := (SheafOfModules.overFunctor_exact_ofUniverses Rg U).1
    letI := (SheafOfModules.overFunctor_exact_ofUniverses Rg U).2
    exact (IntegralOnSlice.hom l E T (some U)).mapIso
      ((Iso.refl _).prod (SheafOfModules.overFunctor_derivedRestrictionIso Rg U N))
  have hpred (N : IntegralOnSlice.D l E T none) :
      locallyComplete l E T σ N ↔ principalLocallyComplete.{t + 1, t, u} R a N := by
    constructor
    · intro h U s hs
      exact (h U s hs).of_iso (testIso N U s).symm
    · intro h U s hs
      exact (h U s hs).of_iso (testIso N U s)
  let F := AsSmall.down.{t, t + 1, max u (t + 1)}
    (C := IntegralOnSlice.Site T none)
  let Js := F.inducedTopology J
  let : F.IsEquivalence :=
    (AsSmall.equiv.{t, t + 1, max u (t + 1)}
      (C := IntegralOnSlice.Site T none)).symm.isEquivalence_functor
  let S := NativeRestriction.restrictedCommRing.{max u (t + 1), t + 1,
    max u (t + 1), t, u} (K := Js) F R
  let H := NativeRestriction.restrictModules.{max u (t + 1), t + 1,
    max u (t + 1), t, u} (K := Js) F R
  let : H.IsEquivalence := NativeRestriction.globalModulesEquivalence
    (K := Js) F R
  let : HasSheafify Js AddCommGrpCat.{max u (t + 1)} := inferInstance
  let : Js.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} := inferInstance
  let : ∀ U : AsSmall.{max u (t + 1)} (IntegralOnSlice.Site T none),
      HasSheafify (Js.over U) AddCommGrpCat.{max u (t + 1)} := fun _ ↦ inferInstance
  let : ∀ U : AsSmall.{max u (t + 1)} (IntegralOnSlice.Site T none),
      (Js.over U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    fun _ ↦ inferInstance
  let : ∀ U : AsSmall.{max u (t + 1)} (IntegralOnSlice.Site T none),
      HasSheafify (Js.over U) CommRingCat.{max u (t + 1)} := fun _ ↦ inferInstance
  let : HasDerivedCategory
      (NativeRestriction.NativeModules.{max u (t + 1), max u (t + 1),
        max u (t + 1)} S) := HasDerivedCategory.standard _
  let Rs := NativeRestriction.NativeRings.{max u (t + 1), max u (t + 1),
    max u (t + 1)} S
  let : ∀ U : AsSmall.{max u (t + 1)} (IntegralOnSlice.Site T none),
      HasDerivedCategory (SheafOfModules.{max u (t + 1)} (Rs.over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : HasDerivedCategory
      (ℕᵒᵖ ⥤ NativeRestriction.NativeModules.{max u (t + 1), max u (t + 1),
        max u (t + 1)} S) := HasDerivedCategory.standard _
  let : HasExactLimitsOfShape (Discrete ℕ) (IntegralOnSlice.Mod l E T none) :=
    AlgebraicGeometry.Scheme.ProEt.products_exact.{t, u, 0} T Rg ℕ
  let : HasExactLimitsOfShape (Discrete ℕ)
      (NativeRestriction.NativeModules.{max u (t + 1), max u (t + 1),
        max u (t + 1)} S) :=
    HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) H.asEquivalence
  obtain ⟨hc, hi⟩ := NativeRestriction.nativePrincipalConeCriterion.{t + 1, t, u}
    R a P μ _hμ
  refine ⟨(hpred _).mpr hc, ?_⟩
  rw [← locallyComplete_iso l E T σ e, hpred, hi]
  exact (isIso_comp_left_iff e.inv _).symm

end WeilConjectures.IntegralPrincipalCone
