/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralScalarOperations.IntegralOperationsScalarExtension

import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomDerivedComplete
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.Native.NativePrincipalCompletenessSmallModel
import WeilConjectures.CategoryTheory.NativeRingedRestrictionDerivedHom
import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Completeness of internal Hom over completed integral coefficients

Source: Bhatt--Scholze 3.4.11; Stacks 08JB, 099B
(blueprint: lem-pur-integral-scalar-internal-hom-complete).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [-instance] IntegralOnSlice.siteCategory IntegralOnSlice.hasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section ScalarHomCompleteness
attribute [local irreducible] IntegralOnSlice.ring
attribute [local instance] IntegralOnSlice.siteCategory IntegralOnSlice.hasDerived
attribute [local semireducible] IntegralOnSlice.ring
universe c r
private theorem scalarSmallHomComplete {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : C, HasSheafify (J.over U) CommRingCat.{u}]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [hSlices : ∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (M N : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hN : principalLocallyComplete.{u,u,u,w} R a N) :
    principalLocallyComplete.{u,u,u,w} R a
      ((derivedInternalHomOfUniverses.{u,u,u,w} J R).obj (op M, N)) := by
  intro U s hs
  obtain ⟨e, _, _⟩ := ringedInternalHom_restriction J R
  let : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))) :=
    hSlices U
  obtain ⟨S, _, β, _⟩ := ringedDerived_closed_symmetric_monoidal.{u,u,u,w}
    (J.over U) (R.over U)
  let A := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalizationOfUniverses (R.over U) s)
  let F := SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U
  let MU := F.mapDerivedCategory.obj M
  let NU := F.mapDerivedCategory.obj N
  have hz := CategoryTheory.isZero_nestedHom
    (derivedInternalHomOfUniverses.{u,u,u,w} (J.over U) (R.over U))
    S β A MU NU (hN U s hs)
  exact hz.of_iso ((derivedInternalHomOfUniverses.{u,u,u,w}
    (J.over U) (R.over U)).mapIso ((Iso.refl (op A)).prod ((e U).app (op M,N))))
section Native
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
set_option hygiene false in
local notation "F" => AsSmall.down.{v, c, max c v r} (C := C)
set_option hygiene false in
local notation "Jsmall" => (F).inducedTopology J
variable [(F).IsEquivalence]
variable (R : Sheaf J CommRingCat.{max c v r})
set_option hygiene false in
local notation "S" =>
  NativeRestriction.restrictedCommRing.{max c v r, c, max c v r, v, r} (K := Jsmall) F R
set_option hygiene false in
local notation "Rg" => NativeRestriction.NativeRings.{max c v r, c, v} R
set_option hygiene false in
local notation "Rs" => NativeRestriction.NativeRings.{max c v r, max c v r, max c v r} S
attribute [local instance] NativeRestriction.sliceDense
  NativeRestriction.globalModulesEquivalence NativeRestriction.sliceModulesEquivalence

private theorem scalarNativeHomComplete
  [HasSheafify J AddCommGrpCat.{max c v r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify Jsmall AddCommGrpCat.{max c v r}] [(Jsmall).WEqualsLocallyBijective
    AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : AsSmall.{max c v r} C, HasSheafify ((Jsmall).over U) AddCommGrpCat.{max c v r}]
  [∀ U : AsSmall.{max c v r} C, ((Jsmall).over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) CommRingCat.{max c v r}]
  [∀ U : AsSmall.{max c v r} C, HasSheafify ((Jsmall).over U) CommRingCat.{max c v r}]
  [HasDerivedCategory.{w} (NativeRestriction.NativeModules.{max c v r, c, v} R)]
  [HasDerivedCategory.{w} (NativeRestriction.NativeModules.{max c v r, max c v r, max c v r} S)]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((Rg).over U))]
  [∀ U : AsSmall.{max c v r} C, HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((Rs).over U))]
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (M N : DerivedCategory (NativeRestriction.NativeModules.{max c v r, c, v} R))
    (hN : principalLocallyComplete.{c,v,r,w} R a N) :
    principalLocallyComplete.{c,v,r,w} R a
      ((derivedInternalHomOfUniverses.{c,v,max c v r,w} J R).obj (op M,N)) := by
  let := NativeRestriction.globalModulesEquivalence.{max c v r,c,max c v r,v,r}
    (K := Jsmall) F R
  apply (NativeRestriction.smallModelComplete.{c,v,r,w} R a _).mpr
  obtain ⟨e⟩ := NativeRestriction.derivedHomRestriction.{max c v r,c,max c v r,v,r,w,w}
    (K := Jsmall) F R (fun _ ↦ inferInstance) M N
  apply (principalLocallyComplete_iso S
    (NativeRestriction.restrictedSection (K := Jsmall) F R a) e).mpr
  exact scalarSmallHomComplete Jsmall S _ _ _
    ((NativeRestriction.smallModelComplete.{c,v,r,w} R a N).mp hN)
end Native

private theorem scalarSfLocalIff (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules.{u, u} l E W)) :
    IsSfDerivedComplete l E W K ↔
      IntegralPrincipalCone.locallyComplete.{u, u} l E W
        (integralCompletionScalarValue.{u, u} l E W) K := by
  classical
  obtain ⟨p,hpl,hp⟩ := Nat.exists_infinite_primes (l+1)
  let : Fact p.Prime := ⟨hp⟩
  let Δ := integralAuxiliaryDatum p
  have hl : l ≠ Δ.p := by dsimp [Δ, integralAuxiliaryDatum]; omega
  obtain ⟨d,hd,_⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  let := IntegralOnSlice.goodLocalization.{u, u} l E W none
  let : (IntegralOnSlice.qGood l E W none).EssSurj :=
    Localization.essSurj _
      ((HomologicalComplex.quasiIso (IntegralOnSlice.Mod l E W none) (.up ℤ)).inverseImage
        (IntegralOnSlice.Good l E W none).ι)
  let P := (IntegralOnSlice.qGood l E W none).objPreimage K
  let e := (IntegralOnSlice.qGood l E W none).objObjPreimageIso K
  have ht := roosIntrinsicCompletenessEquivalence.{u, u} p l (by omega) E W d hd K P e
  have hi : IsSfDerivedComplete l E W K ↔ IntegralOnSlice.IsComplete l E W none K := by
    constructor
    · intro h
      exact ⟨Δ,hl,(sfDerivedComplete_iff_legacy l E W Δ hl K).mp h⟩
    · rintro ⟨Δ',hl',h⟩
      exact (sfDerivedComplete_iff_legacy l E W Δ' hl' K).mpr h
  exact hi.trans (ht.out 1 2)

/-- Ambient internal Hom into a complete object is complete; constructibility of the
Hom is not assumed. Source: Bhatt--Scholze 3.4.11; Stacks 08JB, 099B
(blueprint: lem-pur-integral-scalar-internal-hom-complete).
Proof: restrict to every slice. Tensor-Hom currying identifies Hom from R[1/t]
into Hom(M,N) with Hom from M into Hom(R[1/t],N), which vanishes by completeness
of N. The local Koszul completion reflector identifies this vanishing with
invertibility of the canonical completion unit. Its Roos triangle is the specified
strict reduction-tower triangle, giving precisely IsSfDerivedComplete. -/
theorem integralScalarInternalHomComplete (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (hN : IsSfDerivedComplete l E W N) :
    IsSfDerivedComplete l E W ((integralDerivedInternalHom l E W).obj (op M, N)) := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology W
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W
  let Rg := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let a : (R.obj ⋙ forget CommRingCat).sections := by
    with_unfolding_all exact
      ⟨integralCompletionScalarValue.{u, u} l E W, integralScalar_natural.{u, u} l E W⟩
  let : HasSheafify J AddCommGrpCat.{max u (u + 1)} :=
    IntegralOnSlice.abSheafify.{u, u} W none
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (u + 1)} :=
    IntegralOnSlice.abLocallyBijective.{u, u} W none
  let : ∀ U : W.ProEt, HasSheafify (J.over U) AddCommGrpCat.{max u (u + 1)} :=
    fun U ↦ IntegralOnSlice.abSheafify.{u, u} W (some U)
  let : ∀ U : W.ProEt, (J.over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (u + 1)} :=
    fun U ↦ IntegralOnSlice.abLocallyBijective.{u, u} W (some U)
  let : ∀ U : W.ProEt, HasSheafify (J.over U) CommRingCat.{max u (u + 1)} :=
    fun U ↦
      letI : EssentiallySmall.{max u (u + 1)} (Over U) := essentiallySmallSelf.{0, u, u+1} _
      hasSheafifyEssentiallySmallSite.{u, u+1, u+1} _ _
  let : HasDerivedCategory (SheafOfModules.{max u (u + 1)} Rg) :=
    IntegralOnSlice.hasDerived l E W none
  let : ∀ U : W.ProEt,
      HasDerivedCategory (SheafOfModules.{max u (u + 1)} (Rg.over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  let F := AsSmall.down.{u, u + 1, max u (u + 1)}
    (C := W.ProEt)
  let Js := F.inducedTopology J
  let : F.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max u (u + 1)}
      (C := W.ProEt)).symm.isEquivalence_functor
  let S := NativeRestriction.restrictedCommRing.{max u (u + 1), u + 1,
    max u (u + 1), u, u} (K := Js) F R
  let H := NativeRestriction.restrictModules.{max u (u + 1), u + 1,
    max u (u + 1), u, u} (K := Js) F R
  let : H.IsEquivalence := NativeRestriction.globalModulesEquivalence
    (K := Js) F R
  let : HasSheafify Js AddCommGrpCat.{max u (u + 1)} := inferInstance
  let : Js.WEqualsLocallyBijective AddCommGrpCat.{max u (u + 1)} := inferInstance
  let : ∀ U : AsSmall.{max u (u + 1)} (W.ProEt),
      HasSheafify (Js.over U) AddCommGrpCat.{max u (u + 1)} := fun _ ↦ inferInstance
  let : ∀ U : AsSmall.{max u (u + 1)} (W.ProEt),
      (Js.over U).WEqualsLocallyBijective AddCommGrpCat.{max u (u + 1)} :=
    fun _ ↦ inferInstance
  let : ∀ U : AsSmall.{max u (u + 1)} (W.ProEt),
      HasSheafify (Js.over U) CommRingCat.{max u (u + 1)} := fun _ ↦ inferInstance
  let : HasDerivedCategory
      (NativeRestriction.NativeModules.{max u (u + 1), max u (u + 1),
        max u (u + 1)} S) := HasDerivedCategory.standard _
  let Rs := NativeRestriction.NativeRings.{max u (u + 1), max u (u + 1),
    max u (u + 1)} S
  let : ∀ U : AsSmall.{max u (u + 1)} (W.ProEt),
      HasDerivedCategory (SheafOfModules.{max u (u + 1)} (Rs.over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  have hpred (K : DerivedCategory (integralTowerModules.{u, u} l E W)) :
      IsSfDerivedComplete l E W K ↔ principalLocallyComplete.{u+1,u,u,u+2} R a K := by
    rw [scalarSfLocalIff l E W K]
    with_unfolding_all
      have testIso (U : W.ProEt)
          (s : (((completedIntegralCommRingSheafUnrestricted l E W).over U).obj ⋙
            forget CommRingCat).sections) :
          IntegralPrincipalCone.localTest l E W K U s ≅
            principalLocalTest.{u+1,u,u,u+2} R K U s := by
        letI := (SheafOfModules.overFunctor_exact_ofUniverses Rg U).1
        letI := (SheafOfModules.overFunctor_exact_ofUniverses Rg U).2
        exact (IntegralOnSlice.hom l E W (some U)).mapIso
          ((Iso.refl _).prod (SheafOfModules.overFunctor_derivedRestrictionIso Rg U K))
      constructor
      · intro h U s hs
        exact (h U s hs).of_iso (testIso U s).symm
      · intro h U s hs
        exact (h U s hs).of_iso (testIso U s)
  apply (hpred _).mpr
  exact scalarNativeHomComplete R a M N ((hpred N).mp hN)

end ScalarHomCompleteness

end WeilConjectures
