/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeResidueExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent

/-!
# Smooth base change with integral coefficients for quasi-compact quasi-separated pushforward

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`. Fix a cartesian
square of schemes

```
Y --e--> W
|        |
h        g
v        v
X --p--> S
```

with `p` smooth, `g` quasi-compact and quasi-separated, `ℓ` invertible on `S`, all schemes
quasi-compact and quasi-separated and `W` noetherian. Then the base change map
`Lp^* Rg_* K ⟶ Rh_* Le^* K` with coefficients `𝒪_E` is an isomorphism at every bounded
constructible `K` (`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_smooth`).
No finiteness is assumed on `g`: neither side need be constructible.

This is the blueprint's integral step of `theorem-smooth-base-change-all-admissible`, with derived
completeness in place of constructibility of the two sides:

1. both sides are derived complete: `K` is
   (`ProEtale.derivedCompleteIntegers_of_boundedConstructible`), and derived pushforwards and
   pullbacks preserve derived completeness;
2. the first derived reduction of the base change map is the pro-étale base change map with
   coefficients `𝔽_E` at the first derived reduction of `K`
   (`ProEtale.CondensedRing.nonempty_arrowIso_derivedReduction_map_exchangeRight`), which is a
   bounded constructible complex of étale origin, so finite-coefficient smooth base change
   (`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_of_smooth`) applies;
3. derived Nakayama
   (`ProEtale.isIso_of_derivedCompleteIntegers_of_isIso_derivedReduction_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {S W Y X : Scheme.{u}} {p : X ⟶ S} {g : W ⟶ S} {e : Y ⟶ W} {h : Y ⟶ X}

omit [Fact ℓ.Prime] in
/-- The base change map is invertible at `K` as soon as the exchange morphism of the pullback
square comparison is. Stated for an abstract `Λ`: at a concrete coefficient ring, rewriting along
`baseChangeMap_eq_exchangeRight` makes the unifier compare instances elaborated in different
contexts. -/
lemma isIso_baseChangeMap_app_of_isIso_exchangeRight
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (sq : CommSq e h g p)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)))
    (hK : IsIso ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ g)
      (derivedUpperStarLowerStarAdjunction Λ h) (pullbackSquareComparison Λ sq)).app K)) :
    IsIso ((baseChangeMap Λ sq).app K) := by
  rw [baseChangeMap_eq_exchangeRight]
  exact hK

variable (ℓ E p) in
/-- For a cartesian square with `p` smooth, `g` quasi-compact and quasi-separated, `W` noetherian
and `ℓ` invertible on `S`, the first derived reduction of the integral exchange morphism at a
bounded constructible `K` is invertible: it is the base change map with coefficients `𝔽_E` at the
first derived reduction of `K`, a bounded constructible complex of étale origin. -/
lemma isIso_derivedReduction_map_exchangeRight_app_of_smooth [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] [IsNoetherian W] (sq : IsPullback e h g p) (hℓ : IsUnit (ℓ : Γ(S, ⊤)))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W) K) :
    IsIso ((derivedReduction X ℓ E).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) g)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) h)
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) sq.toCommSq)).app K)) := by
  have : K.IsGE hK.1.1.choose := hK.1.1.choose_spec
  have α := (nonempty_arrowIso_derivedReduction_map_exchangeRight ℓ E sq.toCommSq K
    hK.1.1.choose).some
  have hfin := ProEtale.isIso_derivedBaseChangeMap_app_of_smooth _ p sq ℓ
    (Fact.out : ℓ.Prime).ne_zero (ProEtale.natCast_eq_zero_residueFieldCoeff.{u} ℓ E) hℓ _
    (ProEtale.boundedConstructible_derivedReduction_obj W ℓ E K hK)
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff α).2 hfin

variable (ℓ E p) in
/-- **Integral smooth base change for quasi-compact quasi-separated pushforward.** For a
cartesian square `e ≫ g = h ≫ p` of quasi-compact quasi-separated schemes with `p` smooth, `g`
quasi-compact and quasi-separated, `W` noetherian and `ℓ` invertible on `S`, the base change map
`Lp^* Rg_* K ⟶ Rh_* Le^* K` with coefficients `𝒪_E` is an isomorphism at every bounded
constructible `K`. -/
theorem isIso_baseChangeMap_app_padicIntegers_of_smooth [Smooth p] [QuasiCompact g]
    [QuasiSeparated g] [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] [IsNoetherian W]
    (sq : IsPullback e h g p) (hℓ : IsUnit (ℓ : Γ(S, ⊤)))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) W) K) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E) sq.toCommSq).app K) := by
  have hK₀ : derivedCompleteIntegers ℓ E W K := derivedCompleteIntegers_of_boundedConstructible hK
  have hsrc := derivedCompleteIntegers_leftDerivedUpperStar_obj p
    (derivedCompleteIntegers_rightDerivedLowerStar_obj g hK₀)
  have htgt := derivedCompleteIntegers_rightDerivedLowerStar_obj h
    (derivedCompleteIntegers_leftDerivedUpperStar_obj e hK₀)
  have r₁ := isIso_derivedReduction_map_exchangeRight_app_of_smooth ℓ E p sq hℓ K hK
  have hsrc' : derivedCompleteIntegers ℓ E X ((R((g)_*⟦Profinite.padicIntegersRingObj ℓ E⟧) ⋙
      L((p)^*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) := by
    rw [Functor.comp_obj]; exact hsrc
  have htgt' : derivedCompleteIntegers ℓ E X ((L((e)^*⟦Profinite.padicIntegersRingObj ℓ E⟧) ⋙
      R((h)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) := by
    rw [Functor.comp_obj]; exact htgt
  have r₃ : IsIso ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) g)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) h)
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) sq.toCommSq)).app K) :=
    isIso_of_derivedCompleteIntegers_of_isIso_derivedReduction_map _ hsrc' htgt' r₁
  have t := isIso_baseChangeMap_app_of_isIso_exchangeRight
    (Profinite.padicIntegersRingObj ℓ E) sq.toCommSq K
  -- the two statements carry different proofs of `Precoherent Profinite`
  revert r₃ t
  normalize_precoherent
  intro r₃ t
  exact t r₃

end AlgebraicGeometry.ProEtale.CondensedRing
