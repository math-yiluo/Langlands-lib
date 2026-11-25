/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
import all WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedConstantConstructibility
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedLisse.LisseCompletedPointwiseComparison

/-! # Finite-free targets under coefficient isomorphisms

Source: Stacks Project, Modules on Sites, change of rings and Tag 03DM.
(blueprint: lem-sf-adic-finite-free-scalar-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicFiniteRealization

attribute [-instance] hasSheafCompose_of_preservesMulticospan
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory

private instance (priority := 20000) siteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private instance sliceLocallyBijective (T : Scheme.{u}) (U : T.ProEt) :
    GrothendieckTopology.WEqualsLocallyBijective.{u + 1, u + 1, u, u + 2, u + 1, u + 1}
      ((ProEt.topology T).over U) Ab.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
    u + 2, u + 1, u + 1, u + 1} _

private theorem lf_iso {T : Scheme.{u}} {R : Sheaf (ProEt.topology T) RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (e : M ≅ N) :
    M.IsFiniteLocallyFree.{u + 1, u, u + 1} ↔ N.IsFiniteLocallyFree.{u + 1, u, u + 1} := by
  constructor
  · intro h
    let := h
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} e
  · intro h
    let := h
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} e.symm

private theorem lf_restrict {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ≅ S)
    (M : pbcModules T S) :
    ((pbcRestrict c.hom).obj M).IsFiniteLocallyFree.{u + 1, u, u + 1} ↔
      M.IsFiniteLocallyFree.{u + 1, u, u + 1} := by
  let e := (adicLisseForget T).mapIso c
  constructor
  · intro h
    let := h
    have h' := ProEtale.CompletedLisse.restriction_finiteLocallyFree e.symm
      ((pbcRestrict c.hom).obj M)
    exact (lf_iso (((ProEtale.CompletedLisse.restrictionEquivalence e).unitIso.app M).symm)).mp h'
  · intro h
    let := h
    exact ProEtale.CompletedLisse.restriction_finiteLocallyFree e M

private theorem stratum_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (c : R ≅ S)
    (M : pbcModules Y S) :
    ((proEtaleModuleInverseImage f R).obj
      ((pbcRestrict c.hom).obj M)).IsFiniteLocallyFree.{u + 1, u, u + 1} ↔
      ((proEtaleModuleInverseImage f S).obj M).IsFiniteLocallyFree.{u + 1, u, u + 1} := by
  let e := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso c
  exact (lf_iso ((AlgebraicGeometry.Scheme.inverseImageRestriction f c).app M)).trans
    (lf_restrict e _)

private theorem target_iso {T : Scheme.{u}}
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {K L : DerivedCategory (pbcModules T R)} (e : K ≅ L) :
    finiteFreeTarget T R K ↔ finiteFreeTarget T R L := by
  have forward {K L : DerivedCategory (pbcModules T R)} (e : K ≅ L)
      (h : finiteFreeTarget T R K) : finiteFreeTarget T R L := by
    obtain ⟨⟨a, b, hab, ha, hb⟩, hs⟩ := h
    let := ha
    let := hb
    refine ⟨⟨a, b, hab, DerivedCategory.TStructure.t.isGE_of_iso e a,
      DerivedCategory.TStructure.t.isLE_of_iso e b⟩, fun q ↦ ?_⟩
    obtain ⟨S, hS⟩ := hs q
    refine ⟨S, fun i ↦ ?_⟩
    exact (lf_iso ((proEtaleModuleInverseImage (S.immersion i) R).mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso e))).mp (hS i)
  exact ⟨forward e, forward e.symm⟩

private theorem target_restrict {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ≅ S)
    (K : DerivedCategory (pbcModules T S)) :
    finiteFreeTarget T S K ↔
      finiteFreeTarget T R ((pbcDerivedRestrict c.hom).obj K) := by
  let F := pbcRestrict c.hom
  have : F.IsEquivalence := inferInstanceAs
    (ProEtale.CompletedLisse.restrictionEquivalence
      ((adicLisseForget T).mapIso c)).functor.IsEquivalence
  have hq (q : ℤ) (S' : FiniteLocallyClosedStratification T) (i : Fin S'.n) :
      ((proEtaleModuleInverseImage (S'.immersion i) S).obj
        ((DerivedCategory.homologyFunctor _ q).obj K)).IsFiniteLocallyFree.{u + 1, u, u + 1} ↔
      ((proEtaleModuleInverseImage (S'.immersion i) R).obj
        ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcDerivedRestrict c.hom).obj K))).IsFiniteLocallyFree.{u + 1, u, u + 1} := by
    exact (stratum_restrict (S'.immersion i) c _).symm.trans
      (lf_iso ((proEtaleModuleInverseImage (S'.immersion i) R).mapIso
        ((F.mapDerivedCategoryHomologyFunctorIso q).app K)))
  constructor
  · rintro ⟨⟨a, b, hab, ha, hb⟩, hs⟩
    let := ha
    let := hb
    refine ⟨⟨a, b, hab, F.isGE_mapDerivedCategory_obj K a,
      F.isLE_mapDerivedCategory_obj K b⟩, fun q ↦ ?_⟩
    obtain ⟨S', hS⟩ := hs q
    exact ⟨S', fun i ↦ (hq q S' i).mp (hS i)⟩
  · rintro ⟨⟨a, b, hab, ha, hb⟩, hs⟩
    have h := F.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
      (X := K) (a := a) (b := b) ⟨ha, hb⟩
    refine ⟨⟨a, b, hab, h.1, h.2⟩, fun q ↦ ?_⟩
    obtain ⟨S', hS⟩ := hs q
    exact ⟨S', fun i ↦ (hq q S' i).mpr (hS i)⟩

/-- A coefficient isomorphism preserves and reflects the ordinary finite-free target.
Source: Stacks Project, Modules on Sites, change of rings and Tag 03DM
(blueprint: lem-sf-adic-finite-free-scalar-transport).
Proof: restriction along the inverse coefficient is an exact equivalence. It commutes
with module inverse image to every stratum by the scalar-pullback adjunction. On a
trivializing slice it preserves the regular module and all finite coproducts, hence
finite local freeness in both directions. Exact localization commutes with homology
and preserves and reflects both standard degree bounds. Finally the derived scalar
adjunction identifies extension with this inverse restriction. This argument retains
every stratum and applies to zero rank, empty schemes, and arbitrary coefficient rings. -/
theorem finiteFreeTarget_coefficientIso {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ≅ S)
    (K : DerivedCategory (pbcModules T R)) :
    finiteFreeTarget T R K ↔ finiteFreeTarget T S ((pbcDerivedExtend c.hom).obj K) := by
  let E := ProEtale.CompletedLisse.restrictionEquivalence ((adicLisseForget T).mapIso c)
  let := Functor.additive_of_preserves_binary_products E.symm.functor
  let := Functor.additive_of_preserves_binary_products E.symm.inverse
  let d : pbcDerivedExtend c.hom ≅ pbcDerivedRestrict c.inv :=
    (pbcDerivedScalarAdjunction c.hom).leftAdjointUniq E.symm.mapDerivedCategory.toAdjunction
  exact (target_restrict c.symm K).trans (target_iso (d.app K).symm)

end WeilConjectures.AdicFiniteRealization
