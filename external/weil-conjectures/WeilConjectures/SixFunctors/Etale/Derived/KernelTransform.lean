/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!

# Kernel transforms

Let `π : V ⟶ S` and `π' : V' ⟶ S` be two `S`-schemes and let `𝒦` be a complex on
`V ×_S V'`, the *kernel*. The *kernel transform* (or integral transform) attached to `𝒦` and
a shift `a : ℤ` is

`Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]`,

`p₁, p₂` being the two projections of `V ×_S V'`. Kernel transforms compose: the composite
of the kernel transforms of `𝒦` and `𝒦'` is the kernel transform of the convolution
`𝒦' ∗ 𝒦`, with the shifts added. The Fourier–Deligne transform of
`WeilConjectures.FourierTransform.Defs` is the kernel transform of the Fourier kernel.

The constructions are made for any coefficient category `A` on which the étale six functors
are built: a Grothendieck abelian, closed symmetric monoidal category with functorial flat
resolutions.

## Main definitions

- `AlgebraicGeometry.Etale.kernelTransform`: the kernel transform `Φ_𝒦` with shift `a`.
- `AlgebraicGeometry.Etale.kernelConvolution`: the convolution
  `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')`.

## Main statements

- `AlgebraicGeometry.Etale.isTriangulated_kernelTransform`: the kernel transform is a
  triangulated functor, being a composite of four triangulated functors.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_shift`: shifting the kernel shifts the
  kernel transform.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`: composition of kernel
  transforms, at finite coefficients.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp_of_nonempty_iso`:
  composition of kernel transforms at a general coefficient category, given the composition
  law of `Rf_!`, compact-support base change and the projection formula.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal`: the kernel transform of a
  kernel supported on the diagonal is a tensor product.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor_of_hasProjectionFormula`: kernel
  transforms are linear over the base on full subcategories where the projection formula for
  the second projection holds.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor`: kernel transforms are linear
  over the base, given the projection formula for the second projection.

## Implementation notes

The statements only assert that an isomorphism *exists*. Showing that the composition of
kernel transforms is compatible with the associativity of convolution will need specific,
coherent isomorphisms, which `Classical.choice` cannot provide.

`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp_of_nonempty_iso` proves the
composition law at a general coefficient category `A`, on the triple product, from
compact-support base change along the cartesian square with sides `r₁₂`, `r₂₃`, `p₂` and `q₁`
and from the projection formula for `r₂₃` and `r₁₃`; it also uses the composition law of `Rf_!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`) and the symmetry of
`⊗ᴸ`. Working over a general `A` keeps the kernel from comparing the
monoidal structures on `D(X_ét)` at `A = ModuleCat Λ` (see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).
`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp` specialises it to a finite ring
`Λ`, where base change is `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`
and the projection formula, on the unbounded derived categories, is
`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`. Base change needs `r₂₃`, a base
change of `π`, to be quasi-compact, so the finiteness hypotheses are put on `π` and `π'`. The
composition law is applied to `r₁₃ ≫ s₂ = r₂₃ ≫ q₂`, `s₂ : V ×_S V'' ⟶ V''` being the second
projection. Instance search does not give this composite a compactification (a composite of
compactifiable morphisms is compactifiable by Nagata's theorem, which needs a quasi-compact
and quasi-separated base), so it is a hypothesis.

`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal` is the projection formula for
the closed immersion `Δ`, followed by `Δ_* = Δ_!` and `Δ ≫ p₂ = 𝟙`. Since `R(f)_!` is computed
with a chosen compactification, the last two steps use independence of the compactification
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), which needs `π` quasi-compact and
torsion coefficients.

`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_shift` is formal: the shift isomorphism
of the derived tensor product in its second variable is natural in the first,
`derivedTensorRight A X (𝒦⟦a⟧) ≅ derivedTensorRight A X 𝒦 ⋙ shiftFunctor _ a`
(`AlgebraicGeometry.Etale.derivedTensorRightShiftIso`), because the derived tensor product
commutes with shifts as a bifunctor.

`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor` moves the shift into the kernel
before applying the projection formula, so that it never has to commute a shift with
`- ⊗ᴸ π'^* N` naturally in `N`. It uses some braiding
of `D((V ×_S V')_ét)` (`DerivedCategory.nonempty_braidedCategory`); since only the existence of
an isomorphism is asserted, the choice does not matter.

TODO: upgrade the statements back to `Iso` constructions once they can be built.

This module only imports its parts: the definitions are in
`WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs`, linearity over the base in
`WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor`, the composition law in
`WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` and the statements at
finite coefficients in `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite`.

-/
