/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteModelStratumFiltration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Generation using a fixed ordered reduced stratification -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp lowerStarComp
  openImmersionLowerShriek

/-- Localization on the successive closed tails places a module in the finite
extension closure of its restrictions to a fixed stratification.
Source: Stacks Tags 09AH and 09Y5; blueprint lemma-sections-support-closed-subscheme--3, step 6.
(blueprint: lem-finite-constant-model-fixed-strata-generation).

Proof: the closed tails have images complementary to the open prefixes. Reducedness
factors each next tail through the preceding one, and this factor is a closed
immersion. Its complement is the specified open stratum. Apply the open/closed
short exact sequence to the restriction of the module to that tail. Exact closed
pushforward gives a distinguished triangle on X. Reverse induction starts with
the empty last tail and adds the stratum extensions. The first tail has full image;
the closed adjunction unit identifies its restriction and pushforward with the
original module. This also handles the empty stratification and zero module. -/
theorem finiteConstantModel_fixedStrata_generation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (R : X.FiniteLocallyClosedStratification)
    (Z : Fin (R.n + 1) → Scheme.{u}) (i : ∀ k, Z k ⟶ X)
    (v : ∀ a : Fin R.n, R.domain a ⟶ Z a.castSucc)
    (hi : ∀ k, IsClosedImmersion (i k) ∧ IsReduced (Z k))
    (hv : ∀ a, IsOpenImmersion (v a) ∧ v a ≫ i a.castSucc = R.immersion a)
    (hr : ∀ k, Set.range (i k) =
      (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a)ᶜ)
    (Q : ObjectProperty (DerivedCategory (supportModules Λ X)))
    [Q.IsClosedUnderIsomorphisms]
    (hzero : ∀ M, IsZero M → Q M)
    (hext : ∀ T ∈ distTriang (DerivedCategory (supportModules Λ X)),
      Q T.obj₁ → Q T.obj₃ → Q T.obj₂)
    (M : supportModules Λ X)
    (hpieces : ∀ a : Fin R.n, letI := (hv a).1;
      Q ((DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar Λ (i a.castSucc)).obj
          ((openImmersionLowerShriek Λ (v a)).obj
            ((upperStar Λ (R.immersion a)).obj M))))) :
    Q ((DerivedCategory.singleFunctor _ 0).obj M) := by
  classical
  have hci (k : Fin (R.n + 1)) : IsClosedImmersion (i k) := (hi k).1
  have hZi (k : Fin (R.n + 1)) : IsReduced (Z k) := (hi k).2
  have hvi (a : Fin R.n) : IsOpenImmersion (v a) := (hv a).1
  have hnoeth (k : Fin (R.n + 1)) : TopologicalSpace.NoetherianSpace (Z k) :=
    (i k).isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  let N (k : Fin (R.n + 1)) := (upperStar Λ (i k)).obj M
  let H (k : Fin (R.n + 1)) :=
    (DerivedCategory.singleFunctor _ 0).obj ((lowerStar Λ (i k)).obj (N k))
  have hH (k : Fin (R.n + 1)) : Q (H k) := by
    induction k using Fin.reverseInduction with
    | last =>
      have he : IsEmpty (Z (Fin.last R.n)) := by
        refine ⟨fun z ↦ ?_⟩
        have hz : i (Fin.last R.n) z ∈ Set.range (i (Fin.last R.n)) :=
          Set.mem_range_self z
        rw [hr] at hz
        apply hz
        have hc := R.iUnion_stratum_eq_univ
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hc.symm ▸ Set.mem_univ (i _ z))
        exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨a.isLt, ha⟩⟩
      exact hzero _ ((DerivedCategory.singleFunctor _ 0).map_isZero
        ((lowerStar Λ (i _)).map_isZero (module_zero_of_empty _ (N _))))
    | cast a ih =>
      have hs : Set.range (i a.succ) ⊆ Set.range (i a.castSucc) := by
        rw [hr, hr]
        intro x hx hx'
        apply hx
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx'
        obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hb
        exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨by
          simpa only [Fin.val_castSucc, Fin.val_succ] using Nat.lt_succ_of_lt hb, hxb⟩⟩
      obtain ⟨t, ht⟩ :=
        (reduced_source_factors_through_closed_subscheme (i a.castSucc) (i a.succ)).1.mpr hs
      have : IsClosedImmersion (t ≫ i a.castSucc) := by rw [ht]; infer_instance
      have : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t (i a.castSucc)
      have hcomp : Set.range (v a) = (Set.range t)ᶜ := by
        ext z
        constructor
        · rintro ⟨s, rfl⟩ ⟨z', hz'⟩
          have hz : (R.immersion a) s ∈ Set.range (i a.succ) := by
            refine ⟨z', ?_⟩
            rw [← ht, Scheme.Hom.comp_apply, hz', ← Scheme.Hom.comp_apply, (hv a).2]
          rw [hr] at hz
          exact hz (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
            ⟨by simp, R.range_immersion a ▸ Set.mem_range_self s⟩⟩)
        · intro hz
          have hnot : i a.castSucc z ∉ Set.range (i a.succ) := by
            rintro ⟨z', hz'⟩
            apply hz
            refine ⟨z', (i a.castSucc).isClosedEmbedding.injective ?_⟩
            simpa only [← Scheme.Hom.comp_apply, ht] using hz'
          have hmem : i a.castSucc z ∈ R.stratum a := by
            have hz0 : i a.castSucc z ∈ Set.range (i a.castSucc) := Set.mem_range_self z
            rw [hr] at hz0
            rw [hr] at hnot
            have hx := Classical.not_not.mp hnot
            obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
            obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hb
            have hba : b = a := by
              apply Fin.ext
              have hb' : b.val < a.val + 1 := by simpa only [Fin.val_succ] using hb
              by_contra hne
              exact hz0 (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr
                ⟨by simpa only [Fin.val_castSucc] using (show b.val < a.val by omega), hxb⟩⟩)
            simpa only [hba] using hxb
          obtain ⟨s, hs⟩ := (R.range_immersion a).symm ▸ hmem
          refine ⟨s, (i a.castSucc).isClosedEmbedding.injective ?_⟩
          simpa only [← Scheme.Hom.comp_apply, (hv a).2] using hs
      have : IsImmersion (R.immersion a) := R.isImmersion a
      have : TopologicalSpace.NoetherianSpace (R.domain a) :=
        (R.immersion a).isEmbedding.isInducing.noetherianSpace
      have : QuasiCompact (v a) :=
        ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
      obtain ⟨e⟩ := natural_open_closed_quotient Λ (v a) t hcomp
      let ε := (openImmersionLowerShriekUpperStarAdjunction Λ (v a)).counit.app (N a.castSucc)
      have : Mono ε := mono_condensed_counit Λ (v a) _
      let SC := ShortComplex.mk ε (cokernel.π ε) (cokernel.condition ε)
      have hSC : SC.ShortExact := { exact := ShortComplex.exact_cokernel ε }
      have hcok : cokernel ε ≅ (lowerStar Λ t).obj ((upperStar Λ t).obj (N a.castSucc)) :=
        (PreservesCokernel.iso ((evaluation _ _).obj (N a.castSucc))
          (openImmersionLowerShriekUpperStarAdjunction Λ (v a)).counit).symm ≪≫
            e.app (N a.castSucc)
      let G := lowerStar Λ (i a.castSucc)
      let O : X.Opens := ⟨(Set.range (i a.castSucc))ᶜ,
        (i a.castSucc).isClosedEmbedding.isClosed_range.isOpen_compl⟩
      have : TopologicalSpace.NoetherianSpace O.toScheme :=
        O.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
      have : QuasiCompact O.ι := noetherian_qc O.ι
      have := closedSupport_lowerStarExact Λ (i a.castSucc) O.ι (by
        rw [Scheme.Opens.range_ι]
        change Set.range (i a.castSucc) = (Set.range (i a.castSucc))ᶜᶜ
        exact (compl_compl _).symm)
      have hmap := (hSC.map_of_exact G)
      have e₁ := (DerivedCategory.singleFunctor _ 0).mapIso
        (G.mapIso ((openImmersionLowerShriek Λ (v a)).mapIso
          ((upperStarComp Λ (v a) (i a.castSucc)).symm.app M ≪≫
            (upperStarCongr Λ (hv a).2).app M)))
      have e₃ := (DerivedCategory.singleFunctor _ 0).mapIso
        (G.mapIso hcok ≪≫
          (G.mapIso ((lowerStar Λ t).mapIso
            ((upperStarComp Λ t (i a.castSucc)).symm.app M ≪≫
              (upperStarCongr Λ ht).app M))) ≪≫
          (lowerStarComp Λ t (i a.castSucc)).app ((upperStar Λ (i a.succ)).obj M) ≪≫
          (lowerStarCongr Λ ht).app ((upperStar Λ (i a.succ)).obj M))
      exact hext hmap.singleTriangle hmap.singleTriangle_distinguished
        (Q.prop_of_iso e₁.symm (hpieces a)) (Q.prop_of_iso e₃.symm ih)
  have : QuasiCompact (⊥ : X.Opens).ι := by
    have : TopologicalSpace.NoetherianSpace (⊥ : X.Opens).toScheme :=
      (⊥ : X.Opens).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    exact ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hfirst : IsIso ((upperStarLowerStarAdjunction Λ (i 0)).unit.app M) := by
    apply supported_unit Λ (i 0) (⊥ : X.Opens).ι
    · rw [Scheme.Opens.range_ι, hr]
      simp
    · have : IsEmpty (⊥ : X.Opens).toScheme :=
        ⟨fun x ↦ (show False from x.property)⟩
      exact module_zero_of_empty _ _
  exact Q.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
    (asIso ((upperStarLowerStarAdjunction Λ (i 0)).unit.app M))).symm (hH 0)

end AlgebraicGeometry.ProEtale.CondensedRing
