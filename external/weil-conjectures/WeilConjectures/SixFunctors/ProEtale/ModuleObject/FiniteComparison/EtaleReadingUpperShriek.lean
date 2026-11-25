/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
public import WeilConjectures.CategoryTheory.Adjunction.FullyFaithfulCounitLocal
public import WeilConjectures.SixFunctors.Etale.Derived.PurityPreservation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReading

/-!
# The étale reading of `𝒪_E ⧸ ℓⁿ`-coefficients and the exceptional inverse image

Write `ρ_X : Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)`, `M ↦ Rν_* Φ(M)`, for the étale reading of
bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes (`ProEtale.CondensedRing.finiteEtaleReading`).
This file reduces the finite-coefficient comparison for `p^!`
(`ProEtale.CondensedRing.HasEtaleReadingUpperShriekComparison`) for a proper `p : X ⟶ Y` to
statements about objects only:

* `ProEtale.CondensedRing.EtaleOriginReading X`: for every bounded constructible condensed
  `𝒪_E ⧸ ℓⁿ`-complex `M` on `X`, the pro-étale complex `Φ(M)` is bounded constructible of
  étale origin (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`: isomorphic
  to `ν^* M₀` for a
  bounded constructible étale complex `M₀`). Then `ρ_X` is fully faithful
  (`ProEtale.CondensedRing.finiteEtaleReadingFullyFaithful`), the counit of `ν^* ⊣ Rν_*` being
  invertible on objects of étale origin.
* the étale `Rp^!` of the étale reading of a bounded constructible condensed complex on `Y` is
  again (up to isomorphism) the étale reading of a bounded constructible condensed complex on
  `X`.

Under these, the right adjoint `H'` of `Rp_*` on `Dᵇc(-)⟦𝒪_E ⧸ ℓⁿ⟧` is the lift of `ρ_Y ⋙ Rp^!`
along the fully faithful `ρ_X` (`Functor.essImage.liftFunctor`), the adjunction is the étale
`Rp_! ⊣ Rp^!` restricted along `ρ` (`Adjunction.restrictFullyFaithful`), and its exceptional
comparison is the lifting isomorphism (`CategoryTheory.mateEquiv_restrictFullyFaithful`)
(`ProEtale.CondensedRing.hasEtaleReadingUpperShriekComparison_of_essImage`). The commutation of
`ρ` with the pushforwards (`ProEtale.CondensedRing.finiteEtaleReadingLowerStarIso`) is that of
the finite-coefficient comparison `Φ` and of `Rν_*` with `Rp_*`.
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

/-- **The étale reading commutes with the pushforwards**: `Rp_* ⋙ ρ_Y ≅ ρ_X ⋙ Rp_*`, chaining the
compatibility of the inclusion of bounded constructible complexes, of the finite-coefficient
comparison `Φ` (`ProEtale.finiteCoefficientDerivedLowerStarIso`) and of `Rν_*`
(`ProEtale.rightDerivedLowerStarCompComparisonLowerStarIso`) with `Rp_*`. -/
noncomputable def finiteEtaleReadingLowerStarIso (p : X ⟶ Y) :
    IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n p ⋙
        finiteEtaleReading ℓ E n Y ≅
      finiteEtaleReading ℓ E n X ⋙
        R(Etale.lowerStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (IntegersModPowRingObj.boundedConstructibleLowerStarCompatibility ℓ E n p) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (finiteCoefficientDerivedLowerStarIso (PadicAlgCl.integersModPow ℓ E n) p.left).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (rightDerivedLowerStarCompComparisonLowerStarIso
            (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left) ≪≫
        (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm

/-- **The étale reading commutes with the lower shrieks** for a proper `p`:
`Rp_* ⋙ ρ_Y ≅ ρ_X ⋙ Rp_!`, the étale `Rp_!` being `Rp_*`
(`Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`). -/
noncomputable def finiteEtaleReadingLowerShriekIso (p : X ⟶ Y) [IsProper p.left] :
    have := HasCompactification.of_over p
    IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n p ⋙
        finiteEtaleReading ℓ E n Y ≅
      finiteEtaleReading ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          p.left :=
  have := HasCompactification.of_over p
  finiteEtaleReadingLowerStarIso ℓ E n p ≪≫
    Functor.isoWhiskerLeft _
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left).symm

variable (X) in
/-- **The étale reading lands in objects of étale origin** on `X`: for every bounded constructible
condensed `𝒪_E ⧸ ℓⁿ`-complex `M`, the pro-étale complex `Φ(M)` is bounded constructible of étale
origin, i.e. isomorphic to `ν^* M₀` for a bounded constructible étale complex `M₀`. (Blueprint
`definition-constructible-sheaves`: for finite `Λ = A_{E,n}` the comparison `ν^*` identifies the
étale and pro-étale constructible categories; with `theorem-comparison-constructible-sheaves`.) -/
def EtaleOriginReading : Prop :=
  ∀ M : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧,
    AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) X.left
      ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor.obj
        M.obj)

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- On objects of étale origin, the counit `ν^* Rν_* L ⟶ L` of the comparison adjunction is
invertible. -/
lemma isIso_derivedComparisonAdjunction_counit_app_of_boundedConstructible
    (X : Scheme.{u}) {L : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)))}
    (hL : AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) X L) :
    IsIso ((derivedComparisonAdjunction
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) X).counit.app L) := by
  obtain ⟨M₀, hM₀, ⟨e⟩⟩ := hL
  have := isIso_derivedComparisonAdjunction_unit_app _ X M₀ hM₀.1.1
  have := (derivedComparisonAdjunction _ X).isIso_counit_app_obj_of_isIso_unit_app M₀
  exact (derivedComparisonAdjunction _ X).isIso_counit_app_of_iso' e

variable {ℓ E n} in
/-- Under `EtaleOriginReading`, **the étale reading is fully faithful**: `ρ_X = Rν_* ∘ Φ ∘ ι`, where
the inclusion `ι` and `Φ` are fully faithful and `Rν_*` is fully faithful on objects of étale
origin, the counit of `ν^* ⊣ Rν_*` being invertible there. -/
noncomputable def finiteEtaleReadingFullyFaithful (hX : EtaleOriginReading ℓ E n X) :
    (finiteEtaleReading ℓ E n X).FullyFaithful :=
  (derivedComparisonAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
    X.left).fullyFaithfulOfIsIsoCounitApp
    ((boundedConstructible _).ι ⋙
      (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor)
    ((ObjectProperty.fullyFaithfulι _).comp
      (finiteCoefficientDerivedEquivalence X.left
        (PadicAlgCl.integersModPow ℓ E n)).fullyFaithfulFunctor)
    fun M ↦ isIso_derivedComparisonAdjunction_counit_app_of_boundedConstructible ℓ E n X.left
      (hX M)

variable {ℓ E n} in
/-- **The finite-coefficient comparison for `p^!`** (proper `p`), assuming that the étale
reading lands in objects of étale origin on `X` and `Y`, and that the étale `Rp^!` of the étale
reading of a bounded constructible condensed complex on `Y` lies in the essential image of the
étale reading on `X`. -/
theorem hasEtaleReadingUpperShriekComparison_of_essImage (p : X ⟶ Y) [IsProper p.left]
    [HasCompactification p.left]
    (hX : EtaleOriginReading ℓ E n X) (hY : EtaleOriginReading ℓ E n Y)
    (hp : ∀ M : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧,
      (finiteEtaleReading ℓ E n X).essImage
        ((Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n)
          p.left).obj
            ((finiteEtaleReading ℓ E n Y).obj M))) :
    HasEtaleReadingUpperShriekComparison ℓ E n p := by
  have := HasCompactification.of_over p
  let hρX := finiteEtaleReadingFullyFaithful hX
  let hρY := finiteEtaleReadingFullyFaithful hY
  have := hρX.full
  have := hρX.faithful
  let H' := Functor.essImage.liftFunctor
    (finiteEtaleReading ℓ E n Y ⋙
      Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) p.left)
    (finiteEtaleReading ℓ E n X) hp
  let comm2 := (Functor.essImage.liftFunctorCompIso
    (finiteEtaleReading ℓ E n Y ⋙
      Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) p.left)
    (finiteEtaleReading ℓ E n X) hp).symm
  let γ := finiteEtaleReadingLowerShriekIso ℓ E n p
  let adjH' := (Etale.rightDerivedUpperShriekAdjunction
    (integersModPowCoeff.{u} ℓ E n) p.left).restrictFullyFaithful hρX hρY
      γ.symm comm2
  refine ⟨H', adjH', γ, ?_⟩
  have h := mateEquiv_restrictFullyFaithful
    (Etale.rightDerivedUpperShriekAdjunction
      (integersModPowCoeff.{u} ℓ E n) p.left) hρX hρY γ.symm comm2
  rw [Iso.symm_hom] at h
  rw [h]
  exact inferInstanceAs (IsIso comm2.inv)

/-- The exponent `ℓⁿ⁺¹` of `𝒪_E ⧸ ℓⁿ` is invertible in a field of characteristic `≠ ℓ`. -/
instance hasInvertibleExponent_integersModPowCoeff :
    HasInvertibleExponent (integersModPowCoeff.{u} ℓ E n) (Spec (.of k)) := by
  refine ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos _, ?_, ?_⟩
  · have h : (ℓ : integersModPowCoeff.{u} ℓ E n) ^ n = 0 :=
      ULift.down_injective (by simp [PadicAlgCl.natCast_pow_eq_zero_integersModPow])
    rw [Nat.cast_pow, pow_succ, h, zero_mul]
  · have hℓ : (ℓ : k) ≠ 0 := by
      intro h
      have hdvd := (CharP.cast_eq_zero_iff k (ringChar k) ℓ).1 h
      exact (Fact.out : ringChar k ≠ ℓ)
        ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 hdvd)
    have hu : IsUnit ((ℓ ^ (n + 1) : ℕ) : k) := by
      rw [Nat.cast_pow]
      exact (Ne.isUnit hℓ).pow _
    simpa using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom

variable (X) in
/-- **Constructible étale complexes are read from bounded constructible condensed ones** on `X`:
for a bounded constructible étale complex `N`, the condensed `𝒪_E ⧸ ℓⁿ`-complex `Φ⁻¹ (ν^* N)` is
bounded constructible. (Blueprint `definition-constructible-sheaves`, the converse of
`ProEtale.CondensedRing.EtaleOriginReading`.) -/
def BoundedConstructibleOfEtale : Prop :=
  ∀ N, Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) X.left N →
    boundedConstructible (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X.left)
      ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).inverse.obj
        (D(ν^*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]).obj N))

variable {ℓ E n} in
/-- **`Rp^!` of an étale reading is an étale reading**: if the étale reading lands in objects of
étale origin on `Y` and bounded constructible étale complexes on `X` are read from condensed
ones, then for a bounded constructible condensed `M` on `Y` the étale `Rp^! ρ_Y(M)` is in the
essential image of `ρ_X`. Indeed `ρ_Y(M) ≅ M₀` for a bounded constructible étale `M₀`, the étale
`Rp^!` preserves bounded constructible complexes (`Etale.exists_preservationClauses`), and
`ρ_X (Φ⁻¹ ν^* N) ≅ Rν_* ν^* N ≅ N` for bounded below `N`. -/
lemma essImage_finiteEtaleReading_rightDerivedUpperShriek (p : X ⟶ Y)
    [HasCompactification p.left] [QuasiCompact p.left] (hY : EtaleOriginReading ℓ E n Y)
    (hX : BoundedConstructibleOfEtale ℓ E n X)
    (M : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    (finiteEtaleReading ℓ E n X).essImage
      ((Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n)
        p.left).obj ((finiteEtaleReading ℓ E n Y).obj M)) := by
  obtain ⟨M₀, hM₀, ⟨e⟩⟩ := hY M
  have := isIso_derivedComparisonAdjunction_unit_app _ Y.left M₀ hM₀.1.1
  let e₁ : (finiteEtaleReading ℓ E n Y).obj M ≅ M₀ :=
    (R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])).mapIso e.symm ≪≫
      (asIso ((derivedComparisonAdjunction _ Y.left).unit.app M₀)).symm
  obtain ⟨D, hD⟩ := Etale.exists_preservationClauses (integersModPowCoeff.{u} ℓ E n) Y.hom p.left
  obtain ⟨dY, hdY⟩ := exists_topologicalKrullDim_le_of_isPullback Y.hom
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hM₀.1
  have hN := ((hD dY (hdY k (𝟙 _) (𝟙 _) Y.hom (IsPullback.id_horiz Y.hom))).1 a b M₀
    ⟨hM₀, ha, hb⟩).1
  let N := (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n)
    p.left).obj M₀
  have := isIso_derivedComparisonAdjunction_unit_app _ X.left N hN.1.1
  refine ⟨⟨_, hX N hN⟩, ⟨?_⟩⟩
  exact (R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])).mapIso
      ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).counitIso.app
        _) ≪≫
    (asIso ((derivedComparisonAdjunction _ X.left).unit.app N)).symm ≪≫
    (Etale.rightDerivedUpperShriek _ p.left).mapIso e₁.symm

variable {ℓ E n} in
/-- **The finite-coefficient comparison for `p^!`** (proper `p`), from the identification of
bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes with bounded constructible étale complexes
on `X` and `Y` (`EtaleOriginReading`, `BoundedConstructibleOfEtale`). -/
theorem hasEtaleReadingUpperShriekComparison_of_etaleOrigin (p : X ⟶ Y) [IsProper p.left]
    (hX : EtaleOriginReading ℓ E n X) (hY : EtaleOriginReading ℓ E n Y)
    (hX' : BoundedConstructibleOfEtale ℓ E n X) :
    HasEtaleReadingUpperShriekComparison ℓ E n p :=
  have := HasCompactification.of_over p
  hasEtaleReadingUpperShriekComparison_of_essImage p hX hY
    (essImage_finiteEtaleReading_rightDerivedUpperShriek p hY hX')


end AlgebraicGeometry.ProEtale.CondensedRing
