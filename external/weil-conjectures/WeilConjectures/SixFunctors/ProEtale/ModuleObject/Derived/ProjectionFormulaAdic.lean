/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection

/-!
# Open direct image, projection formula and proper base change over `𝒪_E`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E` and condensed ring
`𝒪̲_E`, and let `Loc(Dctf(X, 𝒪_E)) = Loc(Dbc(X, 𝒪_E))` be the localizing closure of the bounded
constructible complexes in `D(X_proét, 𝒪_E) = D(Mod_{𝒪_{E,X}})`
(`AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible`). This file proves
blueprint `lemma-projection-formula-integral-coefficients`:

* for a quasi-compact open immersion `j : U ⟶ X`, `Rj_*` maps `Dctf(U, 𝒪_E)` into `Dctf(X, 𝒪_E)`
  (`proposition-direct-image-along-open-immersion--1`);
* proper base change holds on `Loc(Dbc(-, 𝒪_E))`
(`proposition-proper-base-change-localizing-categories--1`);
* the categories `Loc(Dbc(-, 𝒪_E))` are closed under `⊗ᴸ_{𝒪_{E,X}}` and the proper projection
  formula holds on them (`lemma-projection-formula-integral-coefficients--1`).

The arguments extending the statements from `Dbc` to `Loc(Dbc)` are those of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection`; the inputs on
`Dbc` from other subsections are collected in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs`.

## Main statements

- `boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_padicIntegersRingObj`
  (`proposition-direct-image-along-open-immersion--1`);
- `isIso_baseChangeMap_of_localizingBoundedConstructible_padicIntegersRingObj`
  (`proposition-proper-base-change-localizing-categories--1`);
- `isIso_projectionMap_of_localizingBoundedConstructible_padicIntegersRingObj`
  (`lemma-projection-formula-integral-coefficients--1`);
- `openDirectImage_baseChange_projectionFormula_padicIntegersRingObj`
  (`lemma-projection-formula-integral-coefficients`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻[" Λ "](" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

include ℓ k

set_option hygiene false in
/-- The condensed ring `𝒪̲_E`. -/
local notation "𝐎" => Profinite.padicIntegersRingObj.{u} ℓ E

/-- Blueprint `proposition-direct-image-along-open-immersion--1`: Integral open direct image
preserves constructibility.

Let `j : U ⟶ X` be a quasi-compact open immersion and `K ∈ Dbc(U, 𝒪_E)`. Then
`Rj_*K ∈ Dbc(X, 𝒪_E) = Dctf(X, 𝒪_E)`.

The blueprint proof shows that `Rj_*K` is derived complete with reduction
`(Rj_*K) ⊗ᴸ 𝐅_{E,X} ≃ Rj_*(K ⊗ᴸ 𝐅_{E,U})` bounded constructible, and concludes by the residue
criterion; this is the integral case of `proposition-direct-image-along-open-immersion`, which is
used here. The derived completeness and the reduction formula, intermediate steps of that argument,
are not stated: derived completeness and reduction modulo `π_E`
(`definition-derived-adic-completeness`) are not yet available for module objects over `𝒪_{E,X}`. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_padicIntegersRingObj
    (j : X ⟶ Y) [IsOpenImmersion j.left] [QuasiCompact j.left] {K : 𝔻[𝐎](X.left)}
    (hK : boundedConstructible (condensedRingObj 𝐎 X.left) K) :
    boundedConstructible (condensedRingObj 𝐎 Y.left) ((R((j.left)_*⟦𝐎⟧)).obj K) :=
  boundedConstructible_rightDerivedLowerStar_openImmersion_padicIntegersRingObj ℓ E j hK

/-- Blueprint `proposition-proper-base-change-localizing-categories--1`: Integral proper base change
on localizing categories.

For a cartesian square `g' ≫ p = p' ≫ g` with `p : X ⟶ Y` proper, the base change map
`g^*Rp_*K ⟶ Rp'_*g'^*K` is an isomorphism for every `K ∈ Loc(Dbc(X, 𝒪_E))`. On `Dbc(X, 𝒪_E)` it
is an isomorphism by proper base change for integral constructible complexes
(`proposition-proper-direct-image-constructible-complexes`); both sides are exact and preserve
direct sums on the localizing categories, so the objects on which it is an isomorphism form a
localizing subcategory containing `Dbc(X, 𝒪_E)`
(`proposition-proper-base-change-localizing-categories--1`). -/
theorem isIso_baseChangeMap_of_localizingBoundedConstructible_padicIntegersRingObj
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left]
    (sq : IsPullback g' p' p g) {K : 𝔻[𝐎](X.left)}
    (hK : localizingBoundedConstructible 𝐎 X.left K) :
    IsIso ((baseChangeMap 𝐎 ((Over.forget _).map_commSq sq.toCommSq)).app K) :=
  isIso_baseChangeMap_of_localizing_padicIntegersRingObj ℓ E sq
    (fun K hK' ↦
      (properDirectImage_baseChange_projectionFormula_padicIntegersRingObj ℓ E p).2.1 sq K hK') hK

/-- Blueprint `lemma-projection-formula-integral-coefficients--1`: The integral proper projection
formula.

Let `p : X ⟶ Y` be proper.

1. For `K ∈ Dbc(X, 𝒪_E)` and `L ∈ Dbc(Y, 𝒪_E)` the projection formula map
   `Rp_*K ⊗ᴸ L ⟶ Rp_*(K ⊗ᴸ p^*L)` (underived completion, tensor over `𝒪_{E,Y}`) is an
   isomorphism in `D(Y_proét, 𝒪_E)`.
2. The categories `Loc(Dbc(-, 𝒪_E))` are closed under `⊗ᴸ`, and the projection formula map is an
   isomorphism for `K ∈ Loc(Dbc(X, 𝒪_E))` and `L ∈ Loc(Dbc(Y, 𝒪_E))`.

Part (1) is the projection formula of `proposition-proper-direct-image-constructible-complexes`. For
(2), the tensor closure follows from `proposition-six-operations-dctf--14` by the two-variable
localizing argument, and the projection formula extends from `Dbc` to `Loc(Dbc)` one variable at a
time, `Rp_*` preserving the localizing categories and direct sums there
(`proposition-compactness-proper-direct-image--2`). -/
theorem isIso_projectionMap_of_localizingBoundedConstructible_padicIntegersRingObj
    (p : X ⟶ Y) [IsProper p.left] :
    (∀ (K : 𝔻[𝐎](X.left)) (L : 𝔻[𝐎](Y.left)), boundedConstructible (condensedRingObj 𝐎 X.left) K →
      boundedConstructible (condensedRingObj 𝐎 Y.left) L →
        IsIso (((projectionMap 𝐎 p.left).app K).app L)) ∧
    (∀ A B : 𝔻[𝐎](X.left), localizingBoundedConstructible 𝐎 X.left A →
      localizingBoundedConstructible 𝐎 X.left B →
        localizingBoundedConstructible 𝐎 X.left (A ⊗ B)) ∧
    (∀ A B : 𝔻[𝐎](Y.left), localizingBoundedConstructible 𝐎 Y.left A →
      localizingBoundedConstructible 𝐎 Y.left B →
        localizingBoundedConstructible 𝐎 Y.left (A ⊗ B)) ∧
    (∀ (K : 𝔻[𝐎](X.left)) (L : 𝔻[𝐎](Y.left)), localizingBoundedConstructible 𝐎 X.left K →
      localizingBoundedConstructible 𝐎 Y.left L →
        IsIso (((projectionMap 𝐎 p.left).app K).app L)) :=
  ⟨fun K L hK hL ↦
      (properDirectImage_baseChange_projectionFormula_padicIntegersRingObj (X' := X) (Y' := Y) ℓ E
        p).2.2 K L hK hL,
    fun _ _ hA hB ↦ localizingBoundedConstructible_tensor 𝐎
      (fun _ _ hK hL ↦ boundedConstructible_tensor_padicIntegersRingObj ℓ E hK hL) hA hB,
    fun _ _ hA hB ↦ localizingBoundedConstructible_tensor 𝐎
      (fun _ _ hK hL ↦ boundedConstructible_tensor_padicIntegersRingObj ℓ E hK hL) hA hB,
    fun _ _ hK hL ↦ isIso_projectionMap_of_localizingBoundedConstructible 𝐎 p.left
      (localizingBoundedConstructible_rightDerivedLowerStar_padicIntegersRingObj ℓ E p).1
      (localizingBoundedConstructible_rightDerivedLowerStar_padicIntegersRingObj ℓ E p).2
      (fun L hL ↦ boundedConstructible_leftDerivedUpperStar_obj 𝐎 ℓ p ⟨L, hL⟩)
      (fun _ _ hK hL ↦ boundedConstructible_tensor_padicIntegersRingObj ℓ E hK hL)
      (properDirectImage_baseChange_projectionFormula_padicIntegersRingObj (X' := X) (Y' := Y) ℓ E
        p).2.2 hK hL⟩

/-- Blueprint `lemma-projection-formula-integral-coefficients`: Open direct image and projection
formula.

For a quasi-compact open immersion `j : U ⟶ X`, `Rj_* : D(U_proét, 𝒪_E) ⥤ D(X_proét, 𝒪_E)` maps
`Dctf(U, 𝒪_E) = Dbc(U, 𝒪_E)` into `Dctf(X, 𝒪_E)`. Proper base change and the proper projection
formula, with the tensor product `⊗ᴸ_{𝒪_{E,X}}`, hold on `Loc(Dctf(-, 𝒪_E))`: for a cartesian
square `g' ≫ p = p' ≫ g` with `p` proper the base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` is an
isomorphism for `K ∈ Loc(Dbc(X, 𝒪_E))`, and for `p : X ⟶ Y` proper the projection formula map
`Rp_*K ⊗ᴸ L ⟶ Rp_*(K ⊗ᴸ p^*L)` is an isomorphism for `K ∈ Loc(Dbc(X, 𝒪_E))` and
`L ∈ Loc(Dbc(Y, 𝒪_E))`. -/
theorem openDirectImage_baseChange_projectionFormula_padicIntegersRingObj :
    (∀ (j : X ⟶ Y) [IsOpenImmersion j.left] [QuasiCompact j.left] (K : 𝔻[𝐎](X.left)),
      boundedConstructible (condensedRingObj 𝐎 X.left) K →
        boundedConstructible (condensedRingObj 𝐎 Y.left) ((R((j.left)_*⟦𝐎⟧)).obj K)) ∧
    (∀ {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left]
      (sq : IsPullback g' p' p g) (K : 𝔻[𝐎](X.left)), localizingBoundedConstructible 𝐎 X.left K →
        IsIso ((baseChangeMap 𝐎 ((Over.forget _).map_commSq sq.toCommSq)).app K)) ∧
    (∀ (p : X ⟶ Y) [IsProper p.left] (K : 𝔻[𝐎](X.left)) (L : 𝔻[𝐎](Y.left)),
      localizingBoundedConstructible 𝐎 X.left K → localizingBoundedConstructible 𝐎 Y.left L →
        IsIso (((projectionMap 𝐎 p.left).app K).app L)) :=
  ⟨fun j _ _ _ hK ↦
      boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion_padicIntegersRingObj ℓ E j hK,
    fun sq _ hK ↦
      isIso_baseChangeMap_of_localizingBoundedConstructible_padicIntegersRingObj ℓ E sq hK,
    fun p _ _ _ hK hL ↦
      (isIso_projectionMap_of_localizingBoundedConstructible_padicIntegersRingObj ℓ E p).2.2.2
        _ _ hK hL⟩

end AlgebraicGeometry.ProEtale.CondensedRing
