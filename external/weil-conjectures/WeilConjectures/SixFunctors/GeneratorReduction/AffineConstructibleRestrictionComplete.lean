/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.QcqsOpenClosedTree.Path.QcqsOpenClosedTree
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionExact
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryQuotientRestriction
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionModels
import all WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitRestriction
import WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryQuotientModuleComparison
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionComparisonDescent
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import all WeilConjectures.SixFunctors.Constructible.ConstructibleResidueTree
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleImmersionAlgebraicLimitsOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedPullbackUnderlyingOfUniverses

/-! # Completeness under constructible restriction inside an affine open

Source: Bhatt--Scholze, Lemma 6.5.8; Stacks Tags 09BL, 09BM, and 099M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.scalarReductionSourceDerived
  WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice

-- The existing exactness proof uses no compactness hypotheses on the three schemes.
private theorem restriction_exact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S V T : Scheme.{u}} (s : S ⟶ V) (i : V ⟶ T)
    [WeaklyEtale s] [IsImmersion i] :
    PreservesLimitsOfSize.{0, 0} (ordinaryPull l E (s ≫ i)) ∧
      IsIso (ordinaryCoefficientMap l E (s ≫ i)) := by
  let hf := abelianPush_isRightAdjoint.{u, u} s
  let hg := abelianPush_isRightAdjoint.{u, u} i
  let hc := abelianPush_isRightAdjoint.{u, u} (s ≫ i)
  let Bf := (abelianPush.{u, u} s).leftAdjoint
  let Bg := (abelianPush.{u, u} i).leftAdjoint
  let B := (abelianPush.{u, u} (s ≫ i)).leftAdjoint
  let af := Adjunction.ofIsRightAdjoint (abelianPush.{u, u} s)
  let ag := Adjunction.ofIsRightAdjoint (abelianPush.{u, u} i)
  let a := Adjunction.ofIsRightAdjoint (abelianPush.{u, u} (s ≫ i))
  let rf := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{u, u} s)
  let rg := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{u, u} i)
  let rc := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{u, u} (s ≫ i))
  obtain ⟨hRg, hBg⟩ := proEtale_immersion_algebraicInverse_limits.{u, u} i
    (ordinaryRingInverse.{u, u} i) rg Bg ag
  let := hRg
  let := hBg
  let := weaklyEtale_limits s (ordinaryRingInverse.{u, u} s) rf
  let := weaklyEtale_limits s Bf af
  let := composite_limits s i (ordinaryRingInverse.{u, u} s) rf
    (ordinaryRingInverse.{u, u} i) rg (ordinaryRingInverse.{u, u} (s ≫ i)) rc
  let hB := composite_limits s i Bf af Bg ag B a
  have hcoeff := ordinaryCoefficientMap_isIso_of_preservesLimits l E (s ≫ i)
  let := hcoeff
  let R := completedIntegralCoefficientSheafUnrestricted l E T
  let A := completedIntegralCoefficientSheafUnrestricted l E S
  let F := ordinaryPull l E (s ≫ i)
  have : IsIso ((rc.homEquiv R A).symm (ordinaryCompletedRingMap l E (s ≫ i))) :=
    hcoeff
  obtain ⟨e⟩ := proEtale_ringedPullback_underlying_of_isIso.{u, u} (s ≫ i)
    (ordinaryRingInverse.{u, u} (s ≫ i)) rc B a R A
    (ordinaryCompletedRingMap l E (s ≫ i)) F (ordinaryAdjunction l E (s ≫ i))
  let hR := moduleForget_limits.{u, u} R
  let hA := moduleForget_limits.{u, u} A
  let V := SheafOfModules.toSheaf.{u + 1} A
  let hV : ReflectsLimitsOfSize.{0, 0} V := reflectsLimits_of_reflectsIsomorphisms
  let hcomp : PreservesLimitsOfSize.{0, 0} (SheafOfModules.toSheaf R ⋙ B) :=
    @comp_preservesLimits _ _ _ _ _ _ _ _ hR hB
  let hFV : PreservesLimitsOfSize.{0, 0} (F ⋙ V) :=
    @preservesLimits_of_natIso _ _ _ _ _ _ e.symm hcomp
  exact ⟨@preservesLimits_of_reflects_of_preserves _ _ _ _ _ _ F V hFV hV, hcoeff⟩

private theorem restriction_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S V T : Scheme.{u}} (s : S ⟶ V) (i : V ⟶ T)
    [WeaklyEtale s] [IsImmersion i]
    (K : D l E T none) (hK : IsComplete l E T none K) :
    IsComplete l E S none ((ordinaryDerivedPull l E (s ≫ i)).obj K) := by
  obtain ⟨hlim, hcoeff⟩ := restriction_exact l E s i
  let := hlim
  let := hcoeff
  have hcol : PreservesFiniteColimits (ordinaryPull l E (s ≫ i)) := by
    have : PreservesColimitsOfSize.{0, 0} (ordinaryPull l E (s ≫ i)) :=
      (ordinaryAdjunction l E (s ≫ i)).leftAdjoint_preservesColimits
    infer_instance
  let := hcol
  choose e he using fun n ↦ (ordinaryQuotientModuleComparison l E (s ≫ i) n).exists
  let τ := quotientTowerIso l E (s ≫ i) e he
  have hτ := fun (P : Cx l E T none) (n : ℕ) ↦
    quotientLevelIso_augmentation l E (s ≫ i) e he n P
  obtain ⟨χ, hf, hs⟩ := restrictionRoosModels (ordinaryPull l E (s ≫ i))
    (tower l E T none) (tower l E S none) τ
  have hgood := ordinaryPull_good l E (s ≫ i)
  obtain ⟨α, hα⟩ := ordinaryCompletionComparison_exists l E (s ≫ i) χ hgood
  have hu := ordinaryCompletionComparison_unit l E (s ≫ i) τ χ hτ hf hs
    hgood α hα K
  have hunit := (canonicalCompletionUnitCriterion l E T K).mpr hK
  let := hunit
  have hm : IsIso ((ordinaryDerivedPull l E (s ≫ i)).map
      ((completionUnit l E T none).app K)) := by infer_instance
  have hh := isIso_comp_right_iff
    ((ordinaryDerivedPull l E (s ≫ i)).map ((completionUnit l E T none).app K))
    (α.hom.app K)
  rw [hu] at hh
  exact (canonicalCompletionUnitCriterion l E S _).mp (hh.mpr hm)

end WeilConjectures.IntegralOnSlice

namespace WeilConjectures.GeneratorReduction

private theorem path_immersion {T S : Scheme.{u}} {tree : QcqsOpenClosedTree T}
    (p : tree.Path S) : IsImmersion p.toRoot := by
  induction p with
  | root t =>
    cases t <;> change IsImmersion (𝟙 _) <;> infer_instance
  | openBranch j i h a b p ih =>
    let := ih
    exact inferInstanceAs (IsImmersion (p.toRoot ≫ j))
  | closedBranch j i h a b p ih =>
    let := ih
    exact inferInstanceAs (IsImmersion (p.toRoot ≫ i))

/-- Ordinary restriction of a complete input to a qcqs weakly etale object of a
constructible immersed affine stratum remains complete. The ambient scheme can be
arbitrary. This asserts completeness only, with no constructibility or projective model.

Source: Bhatt--Scholze, Lemma 6.5.8; Stacks Tags 09BL, 09BM, and 099M.
(blueprint: lem-sf-affine-constructible-restriction-complete).

Proof: induction on the path shows that its structural morphism, followed by the
open immersion, is an immersion. Inverse image along an immersion preserves limits;
weakly etale inverse image is over-site restriction and also preserves limits. Use
uniqueness of left adjoints to identify their composite with inverse image along the
composite scheme map. The finite coefficient maps are isomorphisms and preserve all
quotient transitions. Taking their inverse limit identifies the completed coefficient
map, so it too is invertible. The underlying abelian sheaf comparison then proves
that ordinary module pullback preserves limits. As a left adjoint it preserves
colimits and is therefore exact. The generator-normalized quotient comparisons give
one isomorphism of augmented strict towers. Preservation of products gives the Roos
comparison, and localization gives the completion comparison with its unit equation.
The source completeness criterion makes the source unit invertible; its pullback
and the completion comparison are invertible, hence so is the target unit. Apply
the target completeness criterion. Finally the uniqueness isomorphism between the
two ordinary total derived pullback presentations transports completeness to the
displayed functor. Empty schemes and zero inputs need no separate choice. -/
theorem affineConstructibleRestrictionComplete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : IsSfDerivedComplete l E X K)
    (U : X.Opens) [IsAffine U.toScheme]
    (tree : QcqsOpenClosedTree U.toScheme)
    {S : Scheme.{u}} (p : tree.Path S)
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V]
    (r : V ⟶ S) [WeaklyEtale r] :
    IntegralOnSlice.IsComplete l E V none
      ((ordinaryIntegralDerivedPull l E (r ≫ p.toRoot ≫ U.ι)).obj K) := by
  have := path_immersion p
  have : IsImmersion (p.toRoot ≫ U.ι) := inferInstance
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact q.Prime := ⟨hprime⟩
  let F : FiniteFieldDatum.{0} :=
    { p := q
      a := 1
      q := q
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod q
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod q) }
  have hl : l ≠ F.p := by change l ≠ q; omega
  have hc : IntegralOnSlice.IsComplete l E X none K :=
    ⟨F, hl, (sfDerivedComplete_iff_legacy l E X F hl K).mp hK⟩
  have hout : IntegralOnSlice.IsComplete l E V none
      ((IntegralOnSlice.ordinaryDerivedPull l E (r ≫ p.toRoot ≫ U.ι)).obj K) :=
    IntegralOnSlice.restriction_complete l E r (p.toRoot ≫ U.ι) K hc
  have hi : (ordinaryIntegralDerivedPull l E (r ≫ p.toRoot ≫ U.ι)).obj K ≅
      (IntegralOnSlice.ordinaryDerivedPull l E (r ≫ p.toRoot ≫ U.ι)).obj K := by
    exact (ordinaryDerivedIso l E (r ≫ p.toRoot ≫ U.ι)).app K
  exact sliceComplete_iso l E V hi hout

end WeilConjectures.GeneratorReduction
