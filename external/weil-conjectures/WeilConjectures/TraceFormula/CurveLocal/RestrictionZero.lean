/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroCovers
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroDescent

/-!

# The supported restriction is zero for Frobenius

This file proves blueprint `lemma-vanishing-local-term-zero-stalk` on the classical étale models: in
the strictly local model `T` of a `CurveLocalModel` (the strict localization of `X ×_k X` at
`(y, y)`, with the graph `G` of `h` and the diagonal `B`), let `L, K ∈ D^b_{ctf}(X, Λ)` with
`K_ȳ = 0` and `P = (L ⊠ K)|_T`. Then the supported restriction
```
ρ_{a,b} : RΓ_G(T, P) ⟶ RΓ_y(B, b^* P)
```
is zero in `D(Λ)`
(`AlgebraicGeometry.Etale.CurveLocalModel.sectionsWithSupportRestriction_eq_zero`).
In the blueprint `L = 𝔻_X K`; the argument uses only that `L` is constructible of finite
Tor-dimension.

The proof follows the blueprint:
1. both `RΓ(T, P)` and `RΓ(B, b^* P)` vanish, the schemes being strictly local with closed stalk
   `L_ȳ ⊗ᴸ K_ȳ = 0` (`lemma-vanishing-local-term-zero-stalk--1` (ii)), so the localization triangles
   identify `ρ_{a,b}` with the restriction `RΓ(T ∖ G, P) ⟶ RΓ(B ∖ y, b^* P)`, which factors
   through `RΓ(T ∖ (G ∪ V), P)` (`lemma-vanishing-local-term-zero-stalk--1` (iii));
2. prime-to-`ℓ` covers (`lemma-tangent-cones-on-cover`) put the curves in the position of
   `lemma-vanishing-restrictions-after-blowing-up--1`, which kills the restriction upstairs;
3. the finite étale trace on the punctured diagonal descends the vanishing, the degree being
   invertible in `Λ` (`lemma-descent-vanishing-finite-etale`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

/-- **The supported restriction is zero for Frobenius** (blueprint
`lemma-vanishing-local-term-zero-stalk`): on the classical strictly local model, for a prime `ℓ`
invertible in `k`, a finite commutative `ℓ`-primary ring `Λ`, `L, K ∈ D^b_{ctf}(X, Λ)` with
`K_ȳ = 0` and `P = (L ⊠ K)|_T`, the supported restriction
`ρ_{a,b} : RΓ_G(T, P) ⟶ RΓ_y(B, b^* P)` is zero in `D(Λ)`. -/
theorem sectionsWithSupportRestriction_eq_zero (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : DerivedCategory.boundedConstructibleFiniteTor Λ M.X L)
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ M.X K)
    (hKy : IsZero ((L((M.y)^*[ModuleCat.{u + 1} Λ])).obj K))
    (P : DerivedCategory.Plus (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P.obj ≅ (L((M.τ)^*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    sectionsWithSupportRestriction (ModuleCat.{u + 1} Λ) M.b M.a M.yB M.openComplement_yB_le P =
      0 := by
  -- Step 1: localization, and the factorization through `T ∖ (G ∪ V)`
  refine sectionsWithSupportRestriction_eq_zero_of_restriction _ M.b M.a M.yB _ M.O inf_le_left M.ψ
    M.ψ_comp_ι P (M.isZero_obj₂_a L K hKy P eP) (M.isZero_obj₂_yB L K hKy P eP) ?_
  -- Step 2: the prime-to-`ℓ` covers
  obtain ⟨S', aS', _, s', hs', π, D', H', B', dD', dH', dB', _, _, _, _, _, _, hH', hD', hB',
    hDB, hDH, hO, πU, _, _, d, hdeg, hd, hπ, E', hE', ⟨e⟩⟩ :=
    M.exists_restrictionZeroCover ℓ hΛ L K hL hK hKy P.obj eP M.ψ M.ψ_comp_ι
  -- Step 3: descent along the finite étale trace on the punctured diagonal
  refine sectionsRestriction_app_eq_zero_of_finite_etale π M.O dD'.openComplement hO M.ψ
    (dB'.resLE dD'.openComplement (dB' ⁻¹ᵁ dD'.openComplement) le_rfl) πU hπ P.obj d hdeg hd ?_
  -- upstairs, the blow-up restriction vanishing
  exact sectionsRestriction_app_eq_zero_of_isOpenImmersion _ dD'.openComplement _ _ _ e
    (sectionsRestriction_app_eq_zero_of_tangentConesMeetAtOrigin aS' s' hs' ℓ hℓ hΛ dD' dH' dB'
      hH' hD' hB' hDB hDH E' hE')

end AlgebraicGeometry.Etale.CurveLocalModel
