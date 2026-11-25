/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons

/-!

# The formal case of duality of external products

If the dualizing complexes satisfy `ω_{X×Y} ≅ ω_X ⊠ ω_Y`, Verdier duality commutes with the
external product of dualizable objects. The Künneth–Verdier isomorphism itself and its formal
equivalence with the commutation of Verdier duality with external products are
`AlgebraicGeometry.Etale.nonempty_iso_kunnethVerdier` and
`AlgebraicGeometry.Etale.verdierDualExternalProduct_iff_kunnethVerdier`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_externalProduct_of_isDualizable`
  (`sk-rem-sf-kv-formal`): `𝔻_{X×Y}(M ⊠ N) ≅ 𝔻_X M ⊠ 𝔻_Y N` for dualizable `M`, `N`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `sk-rem-sf-kv-formal`: the formal case of duality of external products.

If the dualizing complexes satisfy `ω_{X×Y} ≅ ω_X ⊠ ω_Y` (the constant-coefficient exceptional
Künneth isomorphism), then for **dualizable** `M` and `N` (for instance perfect complexes on
smooth `X`, `Y`) Verdier duality commutes with the external product,
`𝔻_{X×Y}(M ⊠ N) ≅ 𝔻_X M ⊠ 𝔻_Y N`: internal homs out of dualizable objects commute with the
external product
(`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_derivedHom_of_isDualizable`).
As the blueprint stresses, this perfect case is the base of the induction, not a substitute
for it. -/
theorem nonempty_iso_verdierDual_externalProduct_of_isDualizable {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S) [HasCompactification a] [HasCompactification b]
    [HasCompactification (pullback.fst a b ≫ a)]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : IsDualizable M) (hN : IsDualizable N)
    (hω : Nonempty (dualizingComplex Λ (pullback.fst a b ≫ a) ≅
      externalProduct (ModuleCat.{u + 1} Λ) a b (dualizingComplex _ a) (dualizingComplex _ b))) :
    Nonempty ((verdierDual Λ (pullback.fst a b ≫ a)).obj
        (op (externalProduct (ModuleCat.{u + 1} Λ) a b M N)) ≅
      externalProduct (ModuleCat.{u + 1} Λ) a b
        ((verdierDual Λ a).obj (op M))
        ((verdierDual Λ b).obj (op N))) := by
  obtain ⟨ω⟩ := hω
  obtain ⟨e⟩ := nonempty_iso_externalProduct_derivedHom_of_isDualizable (ModuleCat.{u + 1} Λ) a b
    (N₁ := dualizingComplex _ a) (N₂ := dualizingComplex _ b) hM hN
  exact ⟨((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).obj _).mapIso ω ≪≫ e.symm⟩

end Etale

end AlgebraicGeometry
