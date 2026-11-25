/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality

/-!
# Étale restriction of the degree-`q` base change map

Two formal facts on the degree-`q` base change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of a
Cartesian square, used in the "minimal counterexample" step of blueprint
`corollary-open-direct-image-over-field--2`:

* `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_etale`: it is an isomorphism when `p`
  is étale (étale base change);
* `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_etale_restriction`: if it is an
  isomorphism for a square on `p₂`, it is an isomorphism for the restriction of this square
  along an étale `p₁`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Étale base change, degreewise: for a Cartesian square on an étale morphism `p`, the
degree-`q` base change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism. -/
theorem Etale.isIso_baseChangeHomologyMap_of_etale {X S T Y : Scheme.{u}} {p : X ⟶ S}
    {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p) [Etale p] (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  rw [Etale.isIso_baseChangeHomologyMap_iff, Etale.baseChange_eq_derivedBaseChangeMapPlus]
  have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sq
  infer_instance

/-- Étale restriction of the degree-`q` base change map: let `sq₂` be a Cartesian square on
`p₂ : Z ⟶ S` along `g`, and `sq` the Cartesian square on `p = p₁ ≫ p₂` along `g` obtained by
restricting `sq₂` along an étale morphism `p₁ : X ⟶ Z` (via the Cartesian square `sq₁`). If the
base change map of `sq₂` at `F` is an isomorphism, so is the one of `sq`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_etale_restriction {X Z S T Y₂ Y : Scheme.{u}}
    {g : T ⟶ S} {p₂ : Z ⟶ S} {e₂ : Y₂ ⟶ T} {h₂ : Y₂ ⟶ Z} {p₁ : X ⟶ Z} {e₁ : Y ⟶ Y₂}
    {h₁ : Y ⟶ X} {e : Y ⟶ T} {p : X ⟶ S} (sq₂ : IsPullback e₂ h₂ g p₂)
    (sq₁ : IsPullback e₁ h₁ h₂ p₁) (sq : IsPullback e h₁ g p) [Etale p₁]
    (he : e₁ ≫ e₂ = e) (hp : p₁ ≫ p₂ = p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsIso (Etale.baseChangeHomologyMap Λ sq₂ q F)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  Etale.isIso_baseChangeHomologyMap_of_paste_horiz Λ sq₂ sq₁ sq he hp q F hF
    (Etale.isIso_baseChangeHomologyMap_of_etale Λ sq₁ q _)

end AlgebraicGeometry
