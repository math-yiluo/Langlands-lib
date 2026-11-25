/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.CoefficientChange
public import WeilConjectures.PoincareDuality.Biduality.EtaleReading
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBidualityField

/-!
# Constructible Verdier biduality with `ℓ`-adic coefficients

Let `k` be a field of characteristic `p ≠ ℓ` and `X` a separated `k`-scheme of finite type. This
file proves constructible Verdier biduality (blueprint `theorem-verdier-biduality`, through the
coefficient reductions of `theorem-verdier-biduality`): the double-dual morphism
`δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for every bounded constructible complex `K`, with
coefficients `𝒪_E` and `ℚ̄_ℓ`.

The chain of reductions is:

- finite coefficients `𝒪_E ⧸ ℓ` on the étale site
  (`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_field`);
- finite coefficients on the pro-étale site, through the étale reading
  (`ProEtale.CondensedRing.isIso_toIhomIhom_integersModPowReductionAmbient_of_etale`);
- integral coefficients `𝒪_E`, by derived Nakayama
  (`ProEtale.CondensedRing.isIso_verdierBiduality_of_isIso_toIhomIhom_reduction`);
- `ℚ̄_ℓ`, by integral models (`ProEtale.CondensedRing.isIso_verdierBiduality_of_integral`).

## Main results

- `ProEtale.CondensedRing.PadicIntegersRingObj.isIso_verdierBiduality`: biduality for `𝒪_E`.
- `ProEtale.CondensedRing.isIso_verdierBiduality`: biduality for `ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- **Constructible Verdier biduality with integral coefficients** (blueprint
`theorem-verdier-biduality`, (ii)): the double-dual morphism `δ_{K₀} : K₀ ⟶ 𝔻_X 𝔻_X K₀` is an
isomorphism for every bounded constructible `𝒪_E`-complex `K₀`, `𝔻_X = RHom(-, Ra_X^! 𝒪_E)`. -/
theorem PadicIntegersRingObj.isIso_verdierBiduality (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsIso (PadicIntegersRingObj.verdierBiduality ℓ E.1 K₀) :=
  isIso_verdierBiduality_of_isIso_toIhomIhom_reduction ℓ E 1 X one_ne_zero K₀
    (isIso_toIhomIhom_integersModPowReductionAmbient_of_etale ℓ E 1
      (fun hM ↦ Etale.isIso_verdierDualDoubleDual_app_of_field _ X.hom hM) K₀)

/-- **Constructible Verdier biduality** (blueprint `theorem-verdier-biduality`): the double-dual
morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for `K` bounded constructible, with
`ℚ̄_ℓ`-coefficients and `ω_X` the dualizing complex relative to the structure morphism
`X ⟶ Spec k` (Input 3.3 of the specification).

The dualizing complex must be taken relative to `Spec k` (or at least to a regular base): for the
complex `Ra^! ℚ̄_ℓ = ℚ̄_ℓ` relative to `a = 𝟙` on a nodal curve and `K` the skyscraper `ℚ̄_ℓ` at
the node, `𝔻𝔻K` has rank `9`. -/
theorem isIso_verdierBiduality (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (verdierBiduality ℓ K) :=
  isIso_verdierBiduality_of_integral ℓ
    (fun E K₀ ↦ PadicIntegersRingObj.isIso_verdierBiduality ℓ E K₀) K

end AlgebraicGeometry.ProEtale.CondensedRing
