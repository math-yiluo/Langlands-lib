/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen

/-!
# Vanishing of the cohomology of an extension by zero

Let `j : U ⟶ X` be an open immersion and `ι : T ⟶ X` a closed immersion with complementary
ranges, and `F` an abelian étale sheaf on `X`. The open–closed sequence
`0 ⟶ j_! j^* F ⟶ F ⟶ ι_* ι^* F ⟶ 0` and the identification `H^q(X, ι_* G) ≅ H^q(T, G)` show:
if the restriction maps `H^q(X, F) ⟶ H^q(T, ι^* F)` (`AlgebraicGeometry.Etale.cohomologyMap`)
are bijective in every degree, then `H^q(X, j_! j^* F) = 0` for all `q`
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`, constant coefficients).

## Main statements

- `CategoryTheory.Sheaf.H.subsingleton_X₁_of_bijective_map_g`: in a short exact sequence of
  abelian sheaves whose second map is bijective on cohomology in every degree, the first term
  has no cohomology.
- `AlgebraicGeometry.Etale.subsingleton_sheafH_openImmersionLowerShriek_of_bijective_cohomologyMap`
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace CategoryTheory

variable {C : Type*} [Category C] {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})] {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}

/-- In a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of abelian sheaves such that
`Hⁿ(S.X₂) → Hⁿ(S.X₃)` is bijective for every `n`, the first term has no cohomology. -/
lemma Sheaf.H.subsingleton_X₁_of_bijective_map_g (hS : S.ShortExact)
    (hg : ∀ n, Function.Bijective (H.map S.g n)) (q : ℕ) : Subsingleton (H S.X₁ q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hfx : H.map S.f q x = 0 :=
    (hg q).1 (by rw [(H.exact_map_map hS q).apply_apply_eq_zero, map_zero])
  cases q with
  | zero =>
    have := hS.mono_f
    have h0 : Abelian.Ext.addEquiv₀ x = 0 :=
      (cancel_mono S.f).1 (by rw [← H.addEquiv₀_map, hfx, map_zero, zero_comp])
    exact Abelian.Ext.addEquiv₀.injective (by rw [h0, map_zero])
  | succ n =>
    obtain ⟨y, rfl⟩ := (H.exact_δSucc_map hS n x).1 hfx
    obtain ⟨z, rfl⟩ := (hg n).2 y
    exact (H.exact_map_δSucc hS n _).2 ⟨z, rfl⟩

end CategoryTheory

namespace AlgebraicGeometry.Etale

variable {U T X : Scheme.{u}} (j : U ⟶ X) (ι : T ⟶ X) [IsOpenImmersion j] [IsClosedImmersion ι]

/-- If the restriction maps `H^q(X, F) ⟶ H^q(T, ι^* F)` to the closed complement `T` of an open
`U ⊆ X` are bijective in every degree, then the extension by zero `j_! j^* F` of the restriction
of `F` to `U` has vanishing cohomology (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`). -/
theorem subsingleton_sheafH_openImmersionLowerShriek_of_bijective_cohomologyMap
    (hjι : Set.range ι.base = (Set.range j.base)ᶜ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ q : ℕ, Function.Bijective (cohomologyMap ι F q)) (q : ℕ) :
    Subsingleton (Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
      ((j)^*[AddCommGrpCat.{u + 1}].obj F)) q) := by
  refine Sheaf.H.subsingleton_X₁_of_bijective_map_g
    (Etale.shortExact_openClosedShortComplex AddCommGrpCat.{u + 1} j ι F hjι) (fun n ↦ ?_) q
  have h := hF n
  simp_rw [funext (cohomologyMap_eq_map_counit_comp ι F n)] at h
  exact (Function.Bijective.of_comp_iff' (bijective_edgeMap_of_isFinite ι _ n) _).1 h

end AlgebraicGeometry.Etale
