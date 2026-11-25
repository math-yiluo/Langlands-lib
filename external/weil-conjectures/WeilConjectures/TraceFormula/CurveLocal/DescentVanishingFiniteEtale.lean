/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.DerivedFiniteEtaleTrace
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroTraceDescent

/-!
# Descent of vanishing along a finite étale cover

Let `f : W' ⟶ W` be a finite étale morphism all of whose geometric fibres have `n` points, with
`n` invertible in `Λ`. The pullback `RΓ(W, L) ⟶ RΓ(W', f^* L)` of derived global sections has a
left inverse, namely `n⁻¹` times the finite étale trace
(`AlgebraicGeometry.Etale.exists_rightDerivedPullback_app_comp_eq_smul`). Consequently a
morphism `α : M ⟶ RΓ(W, L)` vanishes as soon as its composite with the pullback does
(blueprint `lemma-descent-vanishing-finite-etale`).

## Main statements

- `AlgebraicGeometry.Etale.exists_rightDerivedPullback_app_comp_eq_id`: the pullback map has a
  left inverse.
- `AlgebraicGeometry.Etale.isSplitMono_rightDerivedPullback_app`: the pullback map is a split
  monomorphism.
- `AlgebraicGeometry.Etale.eq_zero_of_comp_rightDerivedPullback_app_eq_zero`: vanishing
  descends along the pullback map.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {W W' : Scheme.{u}} (f : W' ⟶ W) [IsFinite f]
  [Etale f] (n : ℕ)

/-- Blueprint `lemma-descent-vanishing-finite-etale`: for a finite étale `f : W' ⟶ W` all of
whose geometric fibres have `n` points, `n` invertible in `Λ`, the pullback map
`RΓ(W, L) ⟶ RΓ(W', f^* L)` of derived global sections has a left inverse in `D(Λ)`
(`n⁻¹` times the trace). -/
theorem exists_rightDerivedPullback_app_comp_eq_id
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ W),
      Nat.card (f.GeometricFiber s) = n)
    (hn : IsUnit (n : Λ))
    (L : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ r, (Functor.rightDerivedPullback (f)^*[ModuleCat.{u + 1} Λ]
        (ΓPullback (ModuleCat.{u + 1} Λ) f)).app L ≫ r = 𝟙 _ := by
  obtain ⟨t, ht⟩ := exists_rightDerivedPullback_app_comp_eq_smul f n hdeg L
  have := DerivedCategory.isIso_smul_id_of_isUnit
    ((Sheaf.Γ W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj L)
    (d := (n : ℤ)) (by exact_mod_cast hn)
  exact ⟨t ≫ inv _, by rw [← assoc, ht, IsIso.hom_inv_id]⟩

/-- Blueprint `lemma-descent-vanishing-finite-etale`: for a finite étale `f : W' ⟶ W` all of
whose geometric fibres have `n` points, `n` invertible in `Λ`, the pullback map
`RΓ(W, L) ⟶ RΓ(W', f^* L)` of derived global sections is a split monomorphism. -/
theorem isSplitMono_rightDerivedPullback_app
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ W),
      Nat.card (f.GeometricFiber s) = n)
    (hn : IsUnit (n : Λ))
    (L : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsSplitMono ((Functor.rightDerivedPullback (f)^*[ModuleCat.{u + 1} Λ]
        (ΓPullback (ModuleCat.{u + 1} Λ) f)).app L) := by
  obtain ⟨r, hr⟩ := exists_rightDerivedPullback_app_comp_eq_id f n hdeg hn L
  exact IsSplitMono.mk' ⟨r, hr⟩

/-- **Descent of vanishing along a finite étale cover** (blueprint
`lemma-descent-vanishing-finite-etale`): for a finite étale `f : W' ⟶ W` all of whose geometric
fibres have `n` points, `n` invertible in `Λ`, a morphism `α : M ⟶ RΓ(W, L)` in `D(Λ)` vanishes
if its composite with the pullback `RΓ(W, L) ⟶ RΓ(W', f^* L)` vanishes. -/
theorem eq_zero_of_comp_rightDerivedPullback_app_eq_zero
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ W),
      Nat.card (f.GeometricFiber s) = n)
    (hn : IsUnit (n : Λ))
    {L : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {M : DerivedCategory (ModuleCat.{u + 1} Λ)}
    {α : M ⟶ (Sheaf.Γ W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj L}
    (hα : α ≫ (Functor.rightDerivedPullback (f)^*[ModuleCat.{u + 1} Λ]
        (ΓPullback (ModuleCat.{u + 1} Λ) f)).app L = 0) :
    α = 0 := by
  obtain ⟨r, hr⟩ := exists_rightDerivedPullback_app_comp_eq_id f n hdeg hn L
  simpa only [assoc, hr, comp_id, zero_comp] using hα =≫ r

end AlgebraicGeometry.Etale
