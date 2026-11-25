/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SepClosedPoint

/-!
# Compactly supported cohomology of torsion complexes is perfect

The finite stage of `lemma-perfect-complexes-geometric-point` for a complex of sheaves of modules
over a Noetherian ring `Λ` which is killed by an integer `N` invertible on the base. This is the
form in which the finite stages `A_{E,n} = 𝒪_E/𝔪_Eⁿ` occur at the integral stage `Λ = 𝒪_E`: an
object of `D(X_ét, A_{E,n})` is recorded through its restriction of scalars to `𝒪_E`, as in
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Perfectness of compact cohomology and of
geometric stalks.

**Compactly supported cohomology of a torsion complex is perfect.** Let `Λ` be a Noetherian ring,
`k` a separably closed field, `X` separated of finite type over `k`, and `K` a bounded
constructible complex of sheaves of `Λ`-modules on `X_ét` of finite Tor amplitude, killed by an
ideal `J` with `Λ ⧸ J` finite containing an integer `N` invertible in `k`. Then `RΓ_c(X, K)` is
a perfect complex of `Λ`-modules: it is bounded, with finitely generated cohomology modules, and
of finite Tor amplitude.

This is the finite stage of the blueprint (the coefficient ring there is `Λ ⧸ J`, through whose
restriction of scalars `K` is recorded); compare
`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections` for a finite `Λ`. -/
theorem isPerfect_compactlySupportedGlobalSections_of_nsmul_eq_zero (Λ : Type (u + 1))
    [CommRing Λ] [IsNoetherianRing Λ] {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [HasCompactification aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (J : Ideal Λ) [Finite (Λ ⧸ J)] (N : ℕ) [NeZero N] (hNJ : (N : Λ) ∈ J)
    (hJ : ∀ r ∈ J, r • 𝟙 K = 0) (hNk : IsUnit (N : Γ(Spec (.of k), ⊤)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect := by
  have := noetherianSpace_of_hasCompactification aX (𝟙 (Spec (.of k)))
  have : QuasiCompact aX := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  let c := HasCompactification.compactification aX
  obtain ⟨hbc, a, b, hta⟩ := hK
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le c.g
  -- `Ra_! K = Rḡ_* (j_! K)` for the compactification `X ⟶[j] X̄ ⟶[ḡ] Spec k`
  let L := D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj K
  have hL := constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek Λ c.i a b
    ⟨⟨hbc, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta⟩, hta⟩
  have hJL (r : Λ) (hr : r ∈ J) : r • 𝟙 L = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, hJ r hr, Functor.map_zero]
  have hNL : N • 𝟙 L = 0 := by
    rw [← Nat.cast_smul_eq_nsmul Λ]
    exact hJL _ hNJ
  exact isPerfect_rightDerivedGlobalSections_of_isSepClosed _
    ⟨boundedConstructible_rightDerivedLowerStar Λ J c.g (𝟙 _) c.g (Category.comp_id _) N hNJ hNk
      hJL hL.1.1, _, _, torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing Λ c.g (𝟙 _) c.g
      (Category.comp_id _) d hd a b N hNL hNk hL.1.1 hL.2⟩

end AlgebraicGeometry.Etale
