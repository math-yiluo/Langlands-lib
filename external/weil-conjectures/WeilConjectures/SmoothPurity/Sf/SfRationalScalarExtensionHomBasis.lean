/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.SmoothPurity.Sf.SfRationalScalarExtensionHomBasisOfIntegral
import WeilConjectures.SmoothPurity.Rational.RationalScalarIntegralHomBasis

/-! # The finite free Hom formula for rational scalar extension

For a finite extension `F/E` of finite extensions of `ℚ_ℓ`, rational scalar extension
`T : D_cons(W, E) ⥤ D_cons(W, F)` satisfies `Hom_F(T N, T Z) ≅ F ⊗_E Hom_E(N, Z)`.
In basis coordinates: for an `E`-basis `v` of `F`, every morphism `T N ⟶ T Z` is uniquely
of the form `∑ i, v i • T(g i)`.

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Section 6.8 (Lemma 6.7.2,
Proposition 6.8.14(2), Remark 6.8.15); finite free coefficient extension.
(blueprint: def-weil-rationalization-karoubi).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

/-- Finite free Hom formula for rational scalar extension, in basis coordinates.

Let `v` be an `E`-basis of `F` (via `ι`). For rational constructible `E`-objects `N`, `Z`,
the map `(g_i)_i ↦ ∑ i, v i • T(g i)` from `Fin d → (N ⟶ Z)` to `T N ⟶ T Z` is bijective,
where `T` is the rational scalar extension and `v i` acts through the canonical
identification of the localized coefficient ring of `F` with `F`.

Mathematics: the completed integer ring `O_F` is finite free over `O_E`. For complete
integral `N`, the completed scalar extension is the ordinary extension `O_F ⊗_{O_E} N`
(finite-free completed comparison), and extension of scalars is left adjoint to the exact
restriction of scalars on derived categories of sheaves of modules. Hence
`Hom(O_F ⊗ N, O_F ⊗ Z) ≅ Hom(N, O_F ⊗ Z) ≅ O_F ⊗_{O_E} Hom(N, Z)`, the composite being
`∑ β_i ⊗ g_i ↦ ∑ β_i • (O_F ⊗ g_i)` for an `O_E`-basis `β` of `O_F`. Tensoring with the
localized coefficient rings (`Loc_F = F = E ⊗_{O_E} O_F`) gives
`Hom_F(T N, T Z) ≅ F ⊗_E Hom_E(N, Z)`, which in the basis `v` is the displayed map.

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.7.2 and
Proposition 6.8.14(2), Remark 6.8.15 (finite coefficient extension of `D_cons`).
(blueprint: def-weil-rationalization-karoubi, lem-sf-rational-scalar-extension-right-adjoint).

Proof: `sfConstructibleIntegralScalarExtension_map_basis_bijective` (the integral formula,
from the derived extension ⊣ restriction adjunction and the coordinates of
`integralOrdinaryScalar_coordinates`) and
`sfRationalScalarExtension_map_basis_bijective_of_integral` (rationalization). -/
theorem sfRationalScalarExtension_map_basis_bijective (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : AlgebraicGeometry.Scheme.{u}) (p : ℕ) (hl : l ≠ p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) {d : ℕ} (v : Fin d → F)
    (hv : ∀ x : F, ∃! c : Fin d → E, ∑ i, ι (c i) * v i = x)
    (N Z : sfRationalConstructibleCategory l E W) :
    Function.Bijective (fun g : Fin d → (N ⟶ Z) ↦
      ∑ i, (sfRationalCoefficientEquiv l F).symm (v i) •
        (sfRationalScalarExtension l E W p hl F ι).map (g i)) :=
  sfRationalScalarExtension_map_basis_bijective_of_integral l E W p hl F ι
    (sfConstructibleIntegralScalarExtension_map_basis_bijective l E F ι W p hl) v hv N Z

end WeilConjectures
