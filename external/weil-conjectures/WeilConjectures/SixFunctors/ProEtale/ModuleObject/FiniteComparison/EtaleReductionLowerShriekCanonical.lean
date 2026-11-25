/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekIso

/-!
# The canonical reduction comparison for `Rf_!` along a proper morphism

For a proper morphism `p : X ⟶ Y` of separated schemes of finite type over a field `k` of
characteristic `≠ ℓ`, reduction modulo `ℓⁿ` read on the étale site
(`ProEtale.CondensedRing.etaleReduction`, `red = ρ ∘ red^{cond}`) commutes with `Rp_!`. The
existing statement `ProEtale.CondensedRing.exists_etaleReductionLowerShriekIso` only asserts that
*some* such isomorphism with invertible transpose exists. This file makes it canonical:

* `ProEtale.CondensedRing.etaleReductionLowerShriekIso`: the isomorphism
  `Rp_! ⋙ red_Y ≅ red_X ⋙ Rp_!`, the paste of the canonical condensed comparison
  `Rp_*^{𝒪_E} ⋙ red^{cond}_Y ⟶ red^{cond}_X ⋙ Rp_*^{𝒪_E ⧸ ℓⁿ}`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarIntegersModPowReduction`, the mate of the
  pullback comparison, invertible by
  `ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible`)
  with the canonical commutation of the étale reading with the lower shrieks
  (`ProEtale.CondensedRing.finiteEtaleReadingLowerShriekIso`), after replacing `Rp_!` by `Rp_*`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`);
* `ProEtale.CondensedRing.isIso_mateEquiv_etaleReductionLowerShriekIso`: its transpose
  `(Rp^! K)_{𝒪_E ⧸ ℓⁿ} ⟶ Rp^! (K_{𝒪_E ⧸ ℓⁿ})` under `Rp_! ⊣ Rp^!` is an isomorphism.

The proofs are those of
`ProEtale.CondensedRing.hasEtaleReductionLowerShriekIso_of_isProper_of_compatible`
and `ProEtale.CondensedRing.hasEtaleReadingUpperShriekComparison_of_essImage`, with the
isomorphisms kept explicit.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The transpose of the canonical étale-reading comparison for `p^!`**: for a proper `p`, the
pushforward `Rp_*` on bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes has a right adjoint
`H'` for which the transpose `H' ⋙ ρ_X ⟶ ρ_Y ⋙ Rp^!` of the canonical isomorphism
`ProEtale.CondensedRing.finiteEtaleReadingLowerShriekIso` under `Rp_* ⊣ H'` and the étale
`Rp_! ⊣ Rp^!` is an isomorphism. The adjoint `H'` is the étale `Rp^!` transported along the fully
faithful étale readings (`CategoryTheory.Adjunction.restrictFullyFaithful`). -/
theorem exists_isIso_mateEquiv_finiteEtaleReadingLowerShriekIso (p : X ⟶ Y) [IsProper p.left] :
    have := HasCompactification.of_over p
    ∃ (H' : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧ ⥤
        Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧)
      (adjH' : IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n p ⊣ H'),
      IsIso (mateEquiv adjH' (Etale.rightDerivedUpperShriekAdjunction _ p.left)
        (TwoSquare.mk _ _ _ _ (finiteEtaleReadingLowerShriekIso ℓ E n p).inv)) := by
  have := HasCompactification.of_over p
  have hp := essImage_finiteEtaleReading_rightDerivedUpperShriek p (etaleOriginReading ℓ E n Y)
    (boundedConstructibleOfEtale ℓ E n X)
  let hρX := finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E n X)
  let hρY := finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E n Y)
  have := hρX.full
  have := hρX.faithful
  let comm2 := (Functor.essImage.liftFunctorCompIso
    (finiteEtaleReading ℓ E n Y ⋙
      Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) p.left)
    (finiteEtaleReading ℓ E n X) hp).symm
  let γ := finiteEtaleReadingLowerShriekIso ℓ E n p
  refine ⟨_, (Etale.rightDerivedUpperShriekAdjunction
    (integersModPowCoeff.{u} ℓ E n) p.left).restrictFullyFaithful hρX hρY γ.symm comm2, ?_⟩
  have h := mateEquiv_restrictFullyFaithful
    (Etale.rightDerivedUpperShriekAdjunction
      (integersModPowCoeff.{u} ℓ E n) p.left) hρX hρY γ.symm comm2
  rw [Iso.symm_hom] at h
  rw [h]
  exact inferInstanceAs (IsIso comm2.inv)

/-- The canonical condensed reduction square for a proper `p`:
`red^{cond}_X ⋙ Rp_*^{𝒪_E ⧸ ℓⁿ} ⟶ Rp_!^{𝒪_E} ⋙ red^{cond}_Y`, the inverse of the canonical
comparison `ProEtale.CondensedRing.boundedConstructibleLowerStarIntegersModPowReduction` (the mate
of the pullback comparison), with `Rp_!` identified with `Rp_*`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`). -/
noncomputable def boundedConstructibleLowerShriekIntegersModPowReductionSquare (p : X ⟶ Y)
    [IsProper p.left] :
    TwoSquare (boundedConstructibleIntegersModPowReduction X.left ℓ E n)
      (PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E p)
      (IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n p)
      (boundedConstructibleIntegersModPowReduction Y.left ℓ E n) :=
  have := isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible ℓ E n p
    (integersModPowPullUnitCompatible ℓ E n p.left) (integersModPowPullδCompatible ℓ E n p.left)
  TwoSquare.mk _ _ _ _ (inv (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n p) ≫
    Functor.whiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p).inv _)

instance isIso_boundedConstructibleLowerShriekIntegersModPowReductionSquare (p : X ⟶ Y)
    [IsProper p.left] :
    IsIso (boundedConstructibleLowerShriekIntegersModPowReductionSquare ℓ E n p) :=
  have := isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible ℓ E n p
    (integersModPowPullUnitCompatible ℓ E n p.left) (integersModPowPullδCompatible ℓ E n p.left)
  inferInstanceAs (IsIso (inv _ ≫ _))

/-- The canonical étale-reading square for a proper `p`:
`ρ_X ⋙ Rp_!^{ét} ⟶ Rp_*^{𝒪_E ⧸ ℓⁿ} ⋙ ρ_Y`, the inverse of
`ProEtale.CondensedRing.finiteEtaleReadingLowerShriekIso`. -/
noncomputable def finiteEtaleReadingLowerShriekSquare (p : X ⟶ Y) [IsProper p.left] :
    have := HasCompactification.of_over p
    TwoSquare (finiteEtaleReading ℓ E n X)
      (IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n p)
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left)
      (finiteEtaleReading ℓ E n Y) :=
  TwoSquare.mk _ _ _ _ (finiteEtaleReadingLowerShriekIso ℓ E n p).inv

instance isIso_finiteEtaleReadingLowerShriekSquare (p : X ⟶ Y) [IsProper p.left] :
    IsIso (finiteEtaleReadingLowerShriekSquare ℓ E n p) :=
  inferInstanceAs (IsIso (Iso.inv _))

/-- Blueprint `lemma-change-coefficients-compact-support` for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`,
read on the étale site, for a proper `p`. **The canonical isomorphism
`(Rp_! K)_{𝒪_E ⧸ ℓⁿ} ≅ Rp_! (K_{𝒪_E ⧸ ℓⁿ})`**, `Rp_! ⋙ red_Y ≅ red_X ⋙ Rp_!`: the inverse of the
horizontal paste of the canonical condensed reduction square
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIntegersModPowReductionSquare`) and the
canonical étale-reading square (`ProEtale.CondensedRing.finiteEtaleReadingLowerShriekSquare`). -/
noncomputable def etaleReductionLowerShriekIso (p : X ⟶ Y) [IsProper p.left] :
    have := HasCompactification.of_over p
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E p ⋙ etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left :=
  have := TwoSquare.isIso_hComp
    (boundedConstructibleLowerShriekIntegersModPowReductionSquare ℓ E n p)
    (finiteEtaleReadingLowerShriekSquare ℓ E n p)
  (asIso ((boundedConstructibleLowerShriekIntegersModPowReductionSquare ℓ E n p).hComp
    (finiteEtaleReadingLowerShriekSquare ℓ E n p))).symm

/-- Blueprint `lemma-change-coefficients-exceptional-inverse-image` for the coefficient map
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site, for a proper `p`: the transpose
`(Rp^! K)_{𝒪_E ⧸ ℓⁿ} ⟶ Rp^! (K_{𝒪_E ⧸ ℓⁿ})` of the canonical isomorphism
`ProEtale.CondensedRing.etaleReductionLowerShriekIso` under `Rp_! ⊣ Rp^!` is an isomorphism. The
mate of a paste is the paste of the mates (`CategoryTheory.isIso_mateEquiv_hComp`): the condensed
one is invertible by the reduction-triangle argument
(`ProEtale.CondensedRing.isIso_mateEquiv_boundedConstructibleLowerStarIntegersModPowReduction`),
the étale-reading one by
`ProEtale.CondensedRing.exists_isIso_mateEquiv_finiteEtaleReadingLowerShriekIso`. -/
theorem isIso_mateEquiv_etaleReductionLowerShriekIso (p : X ⟶ Y) [IsProper p.left] :
    have := HasCompactification.of_over p
    IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E p)
      (Etale.rightDerivedUpperShriekAdjunction _ p.left)
      (TwoSquare.mk _ _ _ _ (etaleReductionLowerShriekIso ℓ E n p).inv)) := by
  have := HasCompactification.of_over p
  obtain ⟨H', adjH', hγC⟩ := exists_isIso_mateEquiv_finiteEtaleReadingLowerShriekIso ℓ E n p
  have hη := integersModPowPullUnitCompatible ℓ E n p.left
  have hδ := integersModPowPullδCompatible ℓ E n p.left
  have := isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible ℓ E n p hη hδ
  have hB := isIso_mateEquiv_boundedConstructibleLowerStarIntegersModPowReduction p
    (restrictScalarsIntegersModPowBoundedConstructible ℓ E n X.left)
    (restrictScalarsIntegersModPowBoundedConstructible ℓ E n Y.left) hη hδ adjH'
    (asIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n p)) rfl
  rw [mateEquiv_ofNatIsoLeft] at hB
  have : IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E p)
      adjH' (boundedConstructibleLowerShriekIntegersModPowReductionSquare ℓ E n p)) :=
    hB
  have : IsIso (mateEquiv adjH' (Etale.rightDerivedUpperShriekAdjunction _ p.left)
      (finiteEtaleReadingLowerShriekSquare ℓ E n p)) :=
    hγC
  exact isIso_mateEquiv_hComp (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E p)
    adjH' (Etale.rightDerivedUpperShriekAdjunction _ p.left)
    (boundedConstructibleLowerShriekIntegersModPowReductionSquare ℓ E n p)
    (finiteEtaleReadingLowerShriekSquare ℓ E n p)

end AlgebraicGeometry.ProEtale.CondensedRing
