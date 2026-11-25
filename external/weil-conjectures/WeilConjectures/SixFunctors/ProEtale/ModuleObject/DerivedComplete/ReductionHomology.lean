/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionHomologyBounds
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionHomologyCenter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionHomologyCokernel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionHomologyConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.ReductionHomologyTriangle

/-!
# The action of a uniformizer on the cohomology sheaves of an `𝒪_E`-complex

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, uniformizer `ϖ` and
residue field `𝔽_E`, and let `K` be a complex of `𝒪_{E,X}`-module objects on `X_proét`. The
reduction triangle `K --ϖ--> K ⟶ K₁ ⟶ K[1]`, where `K₁ = 𝔽_{E,X} ⊗ᴸ K` is regarded as a complex of
`𝒪_{E,X}`-modules, gives exact sequences
`0 ⟶ coker (ϖ on Hᵠ K) ⟶ Hᵠ K₁ ⟶ ker (ϖ on Hᵠ⁺¹ K) ⟶ 0`. This file records the consequences of
these sequences used in the integral criterion for bounded constructibility.

## Main results

* `ProEtale.nonempty_cokernel_padicIntegersCenter_homology_iso`: if `Hᵠ⁺¹ K = 0`, the cokernel of
  `ϖ` on `Hᵠ K` is `Hᵠ K₁`.
* `ProEtale.exists_epi_kernel_padicIntegersCenter_homology`: the kernel of `ϖ` on `Hᵠ K` is a
  quotient of `Hᵠ⁻¹ K₁`.
* `ProEtale.epi_padicIntegersCenter_homology_of_lt` and its variants: if `K₁` has cohomology in
  degrees `[a, b]`, then `ϖ` is surjective on `Hᵠ K` for `q ∉ [a, b]` and injective on `Hᵠ K`
  for `q ∉ [a + 1, b + 1]`.
* `ProEtale.boundedConstructible_comap_padicIntegersToResidueField`: restriction of scalars along
  `𝒪_{E,X} ⟶ 𝔽_{E,X}` preserves bounded constructible complexes; in particular `K₁` is bounded
  constructible as an `𝒪_{E,X}`-complex as soon as `𝔽_{E,X} ⊗ᴸ K` is. This uses that restriction
  of scalars along `𝒪_{E,X} ⟶ 𝔽_{E,X}` preserves constructibility
  (`ProEtale.isConstructibleModuleObject_comap_padicIntegersToResidueField`), since over a
  member of a pro-étale cover where the unit is projective, finitely presented `𝔽_E`-modules are
  finitely presented `𝒪_E`-modules (`CategoryTheory.Mod.IsFinitelyPresented.comap_of_regularEnd`).
* `ProEtale.boundedConstructible_comap_derivedExtendScalars_of_derivedReduction`: if the first
  derived reduction of `K` lies in the étale-origin `Dᵇc(X, 𝔽_E)`, then `K₁` is a bounded
  constructible complex of `𝒪_{E,X}`-modules.

Note that the cohomology sheaves `Hᵠ K` themselves need not be constructible, nor the cokernel
and kernel of `ϖ` on them: subobjects of constructible sheaves on `X_proét` need not be
constructible.

The results are proved in the modules `ReductionHomologyCenter` (the homology sequence of a
reduction triangle), `ReductionHomologyConstructible`, `ReductionHomologyTriangle`,
`ReductionHomologyCokernel` and `ReductionHomologyBounds` of this directory.
-/
