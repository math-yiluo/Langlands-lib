/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.SmoothAtPrimeFieldExtensionDescentAux


/-!
# Descent of smoothness at a prime along a field extension

Source: Stacks Project, Algebra, Lemma 02UQ, descent implication, via Lemma 00TG
(blueprint: lem-weil-pbc-smooth-at-prime-field-extension-descent).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- For a finite type `k`-algebra `S` and a field extension `K/k`, smoothness of
`K ⊗[k] S` over `K` at `qK` implies smoothness of `S` over `k` at the contracted prime.
The `K`-algebra structure sends `λ` to `λ ⊗ 1`, and `includeRight` sends `s` to `1 ⊗ s`.
Source: Stacks Project, Algebra, Lemma 02UQ, descent implication via Lemma 00TG
(blueprint: lem-weil-pbc-smooth-at-prime-field-extension-descent).

Proof, following the node:
1. A field is Noetherian, so finite type implies finite presentation
(`lem-weil-pbc-finite-type-noetherian-finite-presentation`). Tensor symmetry identifies
`includeRight` with the usual field-extension base change, which is faithfully flat
(`lem-weil-pbc-field-extension-base-change-faithfully-flat`). Localizing gives a flat local
map (`lem-weil-pbc-flat-local-ring-maps`), hence a faithfully flat one
(`lem-weil-pbc-flat-local-hom-faithfully-flat`). Finite presentation survives base change
(`lem-weil-pbc-presentation-base-change`). The map `k → K` is flat as well.
2. Choose a smooth principal localization outside `qK` using
`def-weil-pbc-singular-ideal`. Smoothness gives zero naive cotangent homology and finite
projective differentials (`def-weil-pbc-smooth-ring-map`). Localizing these at `qK`
(`lem-weil-pbc-h1-cotangent-localization`, `lem-weil-pbc-kahler-differentials-localization`)
gives zero homology and finite free differentials
(`proposition-projective-line-rational-coefficients--1`).
3. Flat base change compares cotangent homology
(`lem-weil-pbc-h1-cotangent-flat-base-change`) and differentials
(`lem-weil-pbc-kahler-differentials-base-change`). Localize those comparisons using
`lem-weil-pbc-localization-tensor-over-base` and
`lem-weil-pbc-localization-tensor-product`: for each module `M`, its localization upstairs
is the tensor product of `M` localized downstairs with the local ring upstairs.
4. Faithful flatness reflects vanishing (`def-weil-pbc-faithfully-flat-ring-map`). The
module of differentials downstairs is finite, using algebra generators
(`def-weil-pbc-finite-type-algebra`), the first exact sequence
(`lem-weil-pbc-kahler-differentials-first-exact-sequence`), and the polynomial basis
(`lem-weil-pbc-polynomial-ring-kahler-basis`). Its finite projectivity descends along the
flat local map (`lem-weil-pbc-finite-projective-descends-flat-local`), hence it is finite free.
5. Finite presentation, zero localized cotangent homology and finite free localized
Kähler differentials imply smoothness at the contracted prime by
`lem-weil-pbc-smooth-at-prime-naive-cotangent-criterion`. Thus some principal localization
outside that prime is smooth, as in `def-weil-pbc-singular-ideal`. -/
theorem isSmoothAtPrime_of_fieldExtension
    {k : Type u} {K : Type v} {S : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] [FiniteType k S]
    (qK : PrimeSpectrum (K ⊗[k] S)) (hsmooth : IsSmoothAtPrime K qK) :
    IsSmoothAtPrime k
      (PrimeSpectrum.comap (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK) := by
  have hfp : FinitePresentation k S := FinitePresentation.of_finiteType.mp inferInstance
  let q := PrimeSpectrum.comap
    (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK
  have hformal : Algebra.IsSmoothAt k q.asIdeal :=
    formallySmoothAtPrime_of_fieldExtension qK hsmooth
  obtain ⟨g, hg, hsm⟩ :=
    @Algebra.IsSmoothAt.exists_notMem_smooth k S _ _ _ hfp q.asIdeal inferInstance hformal
  exact ⟨g, hg, hsm⟩

end Algebra
