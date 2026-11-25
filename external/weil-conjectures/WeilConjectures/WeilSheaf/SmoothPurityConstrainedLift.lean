/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityReductionFunctor
public import WeilConjectures.WeilSheaf.SmoothPurityFiniteChoice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftIsomorphisms

/-! # Lifting finite isomorphisms with a prescribed stable property

For Frobenius equivariance one can choose compatible equivariant isomorphisms, without first
showing that a particular canonical isomorphism commutes with coefficient reduction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing
open scoped CategoryTheory.Obj

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- A reduction-step equation gives the transition equation used by reconstruction. -/
lemma derivedReductionStep_compatible
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))} (n : ℕ)
    (s : (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1 + 1))).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1 + 1))).leftDerivedFunctor.obj L)
    (t : (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L)
    (h : derivedReductionStep (n + 1) s = t) :
    (Mod.comap (integersModPowReduction X ℓ E (n + 1 + 1))).mapDerivedCategory.map s ≫
        reductionTransition E (n + 1) L =
      reductionTransition E (n + 1) K ≫
        (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.map t := by
  subst t
  exact Mod.map_comp_derivedReductionTransition_app
    (integersModPowReduction X ℓ E (n + 1 + 1))
    (integersModPowTransition X ℓ E (n + 1))
    (integersModPowReduction X ℓ E (n + 1))
    (integersModPowReduction_comp_integersModPowTransition X ℓ E (n + 1)) s

/-- A property stable under reduction can be imposed on every reduction of the lift. -/
theorem exists_forall_isIso_property_derivedReduction_map
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    (P : ∀ n : ℕ,
      ((purityIntegralReduction X ℓ E (n + 1)).obj K ⟶
        (purityIntegralReduction X ℓ E (n + 1)).obj L) → Prop)
    (hfin : ∀ n : ℕ, Finite
      ((purityIntegralReduction X ℓ E (n + 1)).obj K ⟶
        (purityIntegralReduction X ℓ E (n + 1)).obj L))
    (hne : ∀ n : ℕ, ∃ e :
      (purityIntegralReduction X ℓ E (n + 1)).obj K ≅
        (purityIntegralReduction X ℓ E (n + 1)).obj L,
      P n e.hom)
    (hP : ∀ n s, P (n + 1) s → P n (derivedReductionStep (n + 1) s)) :
    ∃ f : K ⟶ L, ∀ n : ℕ,
      IsIso ((purityIntegralReduction X ℓ E (n + 1)).map f) ∧
        P n ((purityIntegralReduction X ℓ E (n + 1)).map f) := by
  let T := fun n : ℕ ↦
    (purityIntegralReduction X ℓ E (n + 1)).obj K ⟶
      (purityIntegralReduction X ℓ E (n + 1)).obj L
  let r (n : ℕ) (s : T (n + 1)) : T n := derivedReductionStep (n + 1) s
  let Q (n : ℕ) (s : T n) : Prop := IsIso s ∧ P n s
  have hne' (n : ℕ) : ∃ s, Q n s := by
    obtain ⟨e, he⟩ := hne n
    exact ⟨e.hom, inferInstance, he⟩
  have hQ (n : ℕ) (s : T (n + 1)) (hs : Q (n + 1) s) : Q n (r n s) := by
    have := hs.1
    exact ⟨isIso_derivedReductionStep (n + 1) s, hP n s hs.2⟩
  obtain ⟨t, htP, ht⟩ := exists_compatible_choices_with_property r Q hfin hne' hQ
  obtain ⟨f, hf⟩ := exists_derivedReduction_map_eq hL t fun n ↦
    derivedReductionStep_compatible n _ _ (ht n)
  refine ⟨f, fun n ↦ ?_⟩
  have hfn : (purityIntegralReduction X ℓ E (n + 1)).map f = t n := hf n
  rw [hfn]
  exact htP n

end AlgebraicGeometry.ProEtale
