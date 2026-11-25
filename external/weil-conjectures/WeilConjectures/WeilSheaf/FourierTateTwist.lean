/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateTwistCohomology
public import WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist
public import WeilConjectures.WeilSheaf.FourierTateTwist.Transform

/-!
# The Fourier–Deligne transform commutes with Tate twists

The Tate twist `K ↦ K(m) = R𝓗om(ℚ̄_ℓ(m)^∨, K)` of Weil complexes is the constant twist by
`χ_ℓ(σ)^m`: the Tate sheaf `ℚ̄_ℓ(m)` is the constant twist `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)^m}`
(`AlgebraicGeometry.WeilSheaf.tateTwistSheafIso`), so its dual is the constant twist by the
inverse unit, and `𝓗om(ℚ̄_ℓ ⊗ 𝓑_b, -) ≅ 𝓗om(ℚ̄_ℓ, -) ⊗ 𝓑_{b⁻¹} ≅ - ⊗ 𝓑_{b⁻¹}`. Constant twists
only rescale the Weil structures, so every `ℚ̄_ℓ`-linear construction commutes with them: the
pullback, the internal hom out of a fixed sheaf, the direct image with compact support and the
shift. Hence so does the Fourier–Deligne transform
`FT_ψ(K) = Rpr₂!(pr₁^* K ⊗ μ^* ℒ_ψ)[1]`, and it commutes with Tate twists.

## Main statements

- `AlgebraicGeometry.nonempty_iso_fourierTransform_tateTwist`
(`proposition-base-change-fourier-inversion--2`, clause (2)):
  `FT_ψ(K(m)) ≅ FT_ψ(K)(m)`, naturally in the Weil complex `K`.

This module only imports its parts, so that `import`s of
`WeilConjectures.WeilSheaf.FourierTateTwist` keep working:

- `WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist`
- `WeilConjectures.WeilSheaf.FourierTateTwist.Transform`
-/
