/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization

/-!
# Finiteness of `Rf_!` on `Dᵇc(-, ℚ̄_ℓ)`

Let `k` be an algebraically closed field with `ringChar k ≠ ℓ`. This file proves that the
compactly supported direct image `Rf_! = Rg_* ∘ i_!` along a compactification
`X ⟶[i] Z ⟶[g] Y` of a morphism `f` of finite-type `k`-schemes carries `Dᵇc(X, ℚ̄_ℓ)` into
`Dᵇc(Y, ℚ̄_ℓ)`, the `ℓ`-adic counterpart of blueprint `sk-prop-sf-finiteness`, i.e. clause (3) of
`proposition-six-operations-dctf` at the stage `ℚ̄_ℓ`.

As in `WeilConjectures.SixFunctors.ProEtale.Adic.Localization`, `Dᵇc(-, ℚ̄_ℓ)` is realised in the
Bhatt–Scholze model: it is the full subcategory
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic ℓ X` of the derived category
of pro-étale sheaves of modules over the constant `ℓ`-adic sheaf.

## Main results

- `ProEtale.boundedConstructibleAdic_mapDerivedCategory_adicOpenImmersionLowerShriek`: the
  extension by zero `j_!` along a quasi-compact open immersion preserves `Dᵇc(-, ℚ̄_ℓ)`.
- `AlgebraicGeometry.ProEtale.boundedConstructibleAdic_rightDerivedLowerShriek`: `Rf_!` carries
  `Dᵇc(X, ℚ̄_ℓ)` into `Dᵇc(Y, ℚ̄_ℓ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime]

/-- The extension by zero `D(j_!)` along a quasi-compact open immersion preserves
`Dᵇc(-, ℚ̄_ℓ)`: `j_!` is exact, so `𝓗ⁿ(D(j_!) K) ≅ j_! 𝓗ⁿ(K)`, and extensions by zero of
constructible sheaves are constructible (`IsAdicConstructibleSheaf.openImmersionLowerShriek`). -/
lemma boundedConstructibleAdic_mapDerivedCategory_adicOpenImmersionLowerShriek
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    {K : DerivedCategory (AdicSheaf l U)} (hK : DerivedCategory.boundedConstructibleAdic l U K) :
    DerivedCategory.boundedConstructibleAdic l X ((j)_!ᵃ[l].mapDerivedCategory.obj K) :=
  ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦
    (adicConstructibleSheaf l X).prop_of_iso
      ((((j)_!ᵃ[l]).mapDerivedCategoryHomologyFunctorIso n).app K)
      ((hK.2 n).openImmersionLowerShriek j)⟩

/-- Blueprint `proposition-six-operations-dctf` (3), `Rf_!` at the stage `ℚ̄_ℓ`; the `ℓ`-adic
counterpart of the finite-coefficient `sk-prop-sf-finiteness`.

**Finiteness of compactly supported direct images with `ℚ̄_ℓ`-coefficients.** Let `k` be an
algebraically closed field with `ringChar k ≠ ℓ`, `Y` quasi-compact and locally of finite type
over `k`, and `f : X ⟶ Y` with a compactification `c = (X ⟶[i] Z ⟶[g] Y)`. Then
`Rf_! = Rg_* ∘ i_!` carries `Dᵇc(X, ℚ̄_ℓ)` into `Dᵇc(Y, ℚ̄_ℓ)`: the extension by zero preserves
`Dᵇc(-, ℚ̄_ℓ)` (`boundedConstructibleAdic_mapDerivedCategory_adicOpenImmersionLowerShriek`, `i`
being quasi-compact as `Z` is noetherian), and so does `Rg_*`
(`AlgebraicGeometry.ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj`).

This replaces an earlier statement with *discrete* `ℚ̄_ℓ`-coefficients on the small étale site,
which is not the `ℓ`-adic statement (for an elliptic curve `E` over `k`, `H¹(E, ℚ̄_ℓ)` vanishes
with discrete coefficients). The finite-coefficient statement of the blueprint is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek`. -/
theorem boundedConstructibleAdic_rightDerivedLowerShriek {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ringChar k ≠ l) {X Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    [QuasiCompact s] {f : X ⟶ Y} (c : Compactification f) {K : DerivedCategory (AdicSheaf l X)}
    (hK : DerivedCategory.boundedConstructibleAdic l X K) :
    DerivedCategory.boundedConstructibleAdic l Y
      ((adicLowerStar l c.g).rightDerivedFunctor.obj ((c.i)_!ᵃ[l].mapDerivedCategory.obj K)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := { __ := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ s) }
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj s hk c.g
    (boundedConstructibleAdic_mapDerivedCategory_adicOpenImmersionLowerShriek c.i hK)

end AlgebraicGeometry.ProEtale
