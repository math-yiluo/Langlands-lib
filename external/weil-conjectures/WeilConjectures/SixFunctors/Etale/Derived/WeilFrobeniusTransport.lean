/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# Transport of Weil data along non-invertible exchanges

Let `h : Y ⟶ Y` be an endomorphism of a scheme, in the `ℓ`-adic formalism the geometric
Frobenius `g_{Y,γ}` of `Y = Y₀ ×_{k₀} k`, and let `ψ : Lh^* M ⟶ M` be Weil data
(`WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius`). This file records two formal
properties of the equivariance squares `IsWeilMorphism h ψ_M ψ_N u`, complementing
`WeilConjectures.CategoryTheory.WeilEquivariance` and
`WeilConjectures.EtaleCohomology.Purity.Smooth.WeilEquivariance`.

* **Scheme-Frobenius forms.** For an isomorphism `κ : LΦ^* ≅ Lh^*`, a square is equivariant for
  the data `ψ` if and only if it is equivariant for the scheme-Frobenius data `κ ≫ ψ`
  (`AlgebraicGeometry.Etale.isWeilMorphism_precomp_iff`; the forward direction, for any `κ`,
  is `AlgebraicGeometry.Etale.IsWeilMorphism.schemeFrobeniusWeilDatum`).
* **Transport along an operation with a non-invertible exchange.** A functor
  `F : D(Y_ét, Λ) ⥤ D(Y'_ét, Λ')` together with an exchange `e : Lh'^* ∘ F ⟶ F ∘ Lh^*`, not
  necessarily invertible, carries Weil data to Weil data, `ψ ↦ e_M ≫ F(ψ)`
  (`AlgebraicGeometry.Etale.exchangeTransportWeilDatum`), and equivariance squares to
  equivariance squares (`AlgebraicGeometry.Etale.IsWeilMorphism.transport`). For an invertible
  exchange this is `CategoryTheory.IsWeilEquivariant.map`. The compactly supported direct image
  with its exchange `Ex_!` is the compact-support transport of Weil data
  (`AlgebraicGeometry.Etale.lowerShriekWeilDatum_eq_exchangeTransportWeilDatum`), and transport
  is compatible with composition of operations
  (`AlgebraicGeometry.Etale.exchangeTransportWeilDatum_comp`).

## Main statements

- `AlgebraicGeometry.Etale.isWeilMorphism_precomp_iff`.
- `AlgebraicGeometry.Etale.IsWeilMorphism.transport`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section SchemeFrobenius

variable {Λ : Type (u + 1)} [CommRing Λ] {Y : Scheme.{u}} {h Φ : Y ⟶ Y}
  {M N : DerivedCategoryModule Λ Y}
  {ψM : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M}
  {ψN : (L((h)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N}

/-- Scheme-Frobenius forms of Weil equivariance, for an invertible comparison.

For an isomorphism `κ : LΦ^* ≅ Lh^*` (the comparison `κ_Y` of
`sec-Weil-complexes`), a square is equivariant for the geometric-Frobenius data
`ψ` if and only if it is equivariant for the scheme-Frobenius data `κ ≫ ψ`. -/
theorem isWeilMorphism_precomp_iff
    (κ : L((Φ)^*[ModuleCat.{u + 1} Λ]) ≅ L((h)^*[ModuleCat.{u + 1} Λ])) {f : M ⟶ N} :
    IsWeilMorphism Φ (κ.hom.app M ≫ ψM) (κ.hom.app N ≫ ψN) f ↔ IsWeilMorphism h ψM ψN f := by
  have key {Φ₁ Φ₂ : Y ⟶ Y}
      (κ' : L((Φ₁)^*[ModuleCat.{u + 1} Λ]) ⟶ L((Φ₂)^*[ModuleCat.{u + 1} Λ]))
      {φM : (L((Φ₂)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M}
      {φN : (L((Φ₂)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N} (hf : IsWeilMorphism Φ₂ φM φN f) :
      IsWeilMorphism Φ₁ (κ'.app M ≫ φM) (κ'.app N ≫ φN) f := by
    unfold IsWeilMorphism at *
    rw [← Category.assoc, κ'.naturality f, Category.assoc, hf, Category.assoc]
  refine ⟨fun hf ↦ ?_, key κ.hom⟩
  simpa only [Iso.inv_hom_id_app_assoc] using key κ.inv hf

end SchemeFrobenius

section Transport

variable {Λ Λ' Λ'' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [CommRing Λ'']
  {Y Y' Y'' : Scheme.{u}} {h : Y ⟶ Y} {h' : Y' ⟶ Y'} {h'' : Y'' ⟶ Y''}
  (F : DerivedCategoryModule Λ Y ⥤ DerivedCategoryModule Λ' Y')
  (e : F ⋙ L((h')^*[ModuleCat.{u + 1} Λ']) ⟶ L((h)^*[ModuleCat.{u + 1} Λ]) ⋙ F)

/-- The *transport* of a Weil datum `ψ : Lh^* M ⟶ M` along an operation
`F : D(Y_ét, Λ) ⥤ D(Y'_ét, Λ')` with a (not necessarily invertible) exchange
`e : Lh'^* ∘ F ⟶ F ∘ Lh^*`:
```
                 e_M                     F ψ
  Lh'^* F M ──────────▶ F Lh^* M ──────────▶ F M
```
For `F = Ra_!` and `e = Ex_!` this is the compact-support transport
(`AlgebraicGeometry.Etale.lowerShriekWeilDatum`), for `F = Ra_*` and `e = Ex_*` the transport to
the direct image (`AlgebraicGeometry.Etale.lowerStarWeilDatum`). For an invertible exchange it
is `CategoryTheory.transportWeilDatum`. -/
noncomputable def exchangeTransportWeilDatum {M : DerivedCategoryModule Λ Y}
    (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    (L((h')^*[ModuleCat.{u + 1} Λ'])).obj (F.obj M) ⟶ F.obj M :=
  e.app M ≫ F.map ψ

variable {M N : DerivedCategoryModule Λ Y}
  {ψM : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M}
  {ψN : (L((h)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N}

/-- Compatibilities of Weil equivariance, for a non-invertible exchange.

An operation `F` with an exchange `e : Lh'^* ∘ F ⟶ F ∘ Lh^*` carries equivariance squares to
equivariance squares: if `u : M ⟶ N` is a morphism of Weil objects for `ψ_M` and `ψ_N`, then
`F u` is one for the transported data (`AlgebraicGeometry.Etale.exchangeTransportWeilDatum`).
For an invertible exchange this is `CategoryTheory.IsWeilEquivariant.map`. The proof is the
naturality of `e`. -/
theorem IsWeilMorphism.transport {f : M ⟶ N} (hf : IsWeilMorphism h ψM ψN f) :
    IsWeilMorphism h' (exchangeTransportWeilDatum F e ψM) (exchangeTransportWeilDatum F e ψN)
      (F.map f) := by
  have := e.naturality f
  simp only [Functor.comp_map] at this
  unfold IsWeilMorphism exchangeTransportWeilDatum at *
  rw [reassoc_of% this, ← F.map_comp, hf, F.map_comp, Category.assoc]

/-- Transporting a Weil datum along `F` and then along `G` is transporting it along `F ⋙ G`,
with the pasted exchange `Lh''^* G F ⟶ G Lh'^* F ⟶ G F Lh^*`. -/
lemma exchangeTransportWeilDatum_comp
    (G : DerivedCategoryModule Λ' Y' ⥤ DerivedCategoryModule Λ'' Y'')
    (e' : G ⋙ L((h'')^*[ModuleCat.{u + 1} Λ'']) ⟶ L((h')^*[ModuleCat.{u + 1} Λ']) ⋙ G)
    (ψ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    exchangeTransportWeilDatum G e' (exchangeTransportWeilDatum F e ψ) =
      exchangeTransportWeilDatum (F ⋙ G)
        (Functor.whiskerLeft F e' ≫ Functor.whiskerRight e G) ψ := by
  simp [exchangeTransportWeilDatum]

end Transport

section Exchange

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {a : X ⟶ Y}
  [HasCompactification a] {g : X ⟶ X} {h : Y ⟶ Y}

/-- The compact-support transport `AlgebraicGeometry.Etale.lowerShriekWeilDatum` of
`prose-10-20` is the transport of Weil data along `Ra_!` with the
exchange `Ex_!`. -/
lemma lowerShriekWeilDatum_eq_exchangeTransportWeilDatum [QuasiCompact a]
    (sq : IsPullback g a a h) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    lowerShriekWeilDatum sq φ =
      exchangeTransportWeilDatum (R(a)_![ModuleCat.{u + 1} Λ])
        (rightDerivedLowerShriekBaseChangeMap Λ sq) φ :=
  rfl

omit [Finite Λ] [HasCompactification a] in
/-- The transport `AlgebraicGeometry.Etale.lowerStarWeilDatum` to the direct image is the
transport of Weil data along `Ra_*` with the exchange `Ex_*`. -/
lemma lowerStarWeilDatum_eq_exchangeTransportWeilDatum (sq : CommSq g a a h)
    {M : DerivedCategoryModule Λ X} (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    lowerStarWeilDatum sq ψ =
      exchangeTransportWeilDatum (R((a)_*[ModuleCat.{u + 1} Λ])) (derivedBaseChangeMap _ sq) ψ :=
  rfl

end Exchange

end Etale

end AlgebraicGeometry
