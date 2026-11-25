/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.NagataRing

/-!
# Normalizations of quotients of Nagata rings

For a Nagata ring `R` (`IsNagataRing`, [Stacks, Tag 032R]) the normalization of every `R / 𝔭`
is finite (`IsNagataRing.finite_integralClosure_quotient`); this is the only consequence of
excellence used in the blueprint for `lem-exc-punctured-curve-branches` (excellent rings are
Nagata, [Stacks, Tag 07QV]).

Fields are Nagata (`IsNagataRing.of_field`).
-/

@[expose] public section

universe u

namespace IsNagataRing

variable {R : Type u} [CommRing R]

/-- A Nagata ring is Noetherian. -/
theorem isNoetherianRing (hR : IsNagataRing R) : IsNoetherianRing R :=
  hR.1

/-- In a Nagata ring `R`, the normalization of `R / 𝔭` (its integral closure in its fraction
field) is a finite `R / 𝔭`-module for every prime `𝔭` ([Stacks, Tag 032R]). This is the
finiteness of normalization used for `lem-exc-punctured-curve-branches`. -/
theorem finite_integralClosure_quotient (hR : IsNagataRing R) (p : Ideal R) [p.IsPrime] :
    Module.Finite (R ⧸ p) (integralClosure (R ⧸ p) (FractionRing (R ⧸ p))) :=
  isN1_of_isN2 _ _ (hR.2 p)

/-- A field is a Nagata ring. -/
theorem of_field (K : Type u) [Field K] : IsNagataRing K := by
  refine ⟨inferInstance, fun p hp ↦ ?_⟩
  have hp' : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right hp.ne_top
  subst hp'
  have : (⊥ : Ideal K).IsMaximal := Ideal.bot_isMaximal
  let := Ideal.Quotient.field (⊥ : Ideal K)
  intro L _ _ _ _ _
  have : Module.Finite (K ⧸ (⊥ : Ideal K)) (FractionRing (K ⧸ (⊥ : Ideal K))) :=
    Module.Finite.equiv
      (FractionRing.algEquiv (K ⧸ (⊥ : Ideal K)) (K ⧸ (⊥ : Ideal K))).symm.toLinearEquiv
  have : Module.Finite (K ⧸ (⊥ : Ideal K)) L :=
    Module.Finite.trans (FractionRing (K ⧸ (⊥ : Ideal K))) L
  exact Module.IsNoetherian.finite _ (integralClosure _ L)

end IsNagataRing
