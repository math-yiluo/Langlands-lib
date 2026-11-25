/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection

/-!
# Projection formula and proper base change with rational coefficients

Let `Λ = E` (a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`) or `Λ = ℚ̄_ℓ`, with condensed ring `E̲`,
resp. `ℚ̲̄_ℓ`, and let `Loc(Dctf(X, Λ)) = Loc(Dbc(X, Λ))` be the localizing closure of the bounded
constructible complexes in `D(X_proét, Λ) = D(Mod_{Λ_X})`
(`AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible`). This file proves
blueprint `proposition-projection-formula-rational-coefficients`:

* `Loc(Dbc(X, Λ))` is closed under `⊗ᴸ` (`proposition-projection-formula-rational-coefficients--1`);
* for `p : X ⟶ Y` proper, the projection formula map `Rp_*A ⊗ᴸ B ⟶ Rp_*(A ⊗ᴸ p^*B)` is an
  isomorphism for `A ∈ Loc(Dbc(X, Λ))` and `B ∈ Loc(Dbc(Y, Λ))`
  (`proposition-projection-formula-rational-coefficients--2`);
* for a cartesian square with `p` proper, the base change map `g^*Rp_* ⟶ Rp'_*g'^*` is an
  isomorphism on `Loc(Dbc(X, Λ))`.

Following the blueprint, each claim is obtained by fixing all but one variable and observing that
the objects satisfying it form a localizing subcategory containing `Dbc`
(`AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible_tensor`,
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_projectionMap_of_localizingBoundedConstructible`).
The inputs on `Dbc` are the tensor closure `proposition-six-operations-dctf--14`, the projection
formula on `Dbc` (`proposition-proper-direct-image-constructible-complexes`, part of
`proposition-proper-direct-image-constructible-complexes`), the proper direct image on the
localizing categories (`proposition-proper-direct-image-extension-zero`) and proper base change on
the localizing categories (`proposition-proper-base-change-localizing-categories--1`), see
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs`.

## Main statements

For `Λ = E̲` (suffix `continuousMapRingObj`) and `Λ = ℚ̲̄_ℓ` (suffix `padicAlgClRingObj`):

- `tensor_mem_localizingBoundedConstructible_*`
(`proposition-projection-formula-rational-coefficients--1`);
- `isIso_projectionMap_of_localizingBoundedConstructible_*`
(`proposition-projection-formula-rational-coefficients--2`);
- `projectionFormula_baseChange_localizingBoundedConstructible_*`
(`proposition-projection-formula-rational-coefficients`).
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

include ℓ k

/-! ### The coefficient field `E` -/

section Field

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

set_option hygiene false in
/-- The condensed field `E̲`. -/
local notation "𝐄" => Profinite.continuousMapRingObj.{u} E

omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
/-- Blueprint `proposition-projection-formula-rational-coefficients--1`: Tensor closure of the
rational localizing categories; the case `Λ = E`.

1. `Dbc(X, E)` is closed under `⊗ᴸ` in `D(X_proét, E)`;
2. for `A, B ∈ Loc(Dbc(X, E))`, the derived tensor product `A ⊗ᴸ B`, formed in `D(X_proét, E)`,
   lies in `Loc(Dbc(X, E))`.

Part (1) is `proposition-six-operations-dctf--14`. For (2), fixing `B ∈ Dbc(X, E)`, the objects `A`
of `Loc(Dbc(X, E))` with `A ⊗ᴸ B ∈ Loc(Dbc(X, E))` form a localizing subcategory containing
`Dbc(X, E)`, since `- ⊗ᴸ B` is exact and preserves direct sums; then fix `A` and argue in `B`. -/
theorem tensor_mem_localizingBoundedConstructible_continuousMapRingObj :
    (∀ K L : 𝔻[𝐄](X.left), boundedConstructible (condensedRingObj 𝐄 X.left) K →
      boundedConstructible (condensedRingObj 𝐄 X.left) L →
        boundedConstructible (condensedRingObj 𝐄 X.left) (K ⊗ L)) ∧
    ∀ A B : 𝔻[𝐄](X.left), localizingBoundedConstructible 𝐄 X.left A →
      localizingBoundedConstructible 𝐄 X.left B → localizingBoundedConstructible 𝐄 X.left (A ⊗ B) :=
  ⟨fun _ _ hK hL ↦ boundedConstructible_tensor_continuousMapRingObj ℓ E hK hL,
    fun _ _ hA hB ↦ localizingBoundedConstructible_tensor 𝐄
      (fun _ _ hK hL ↦ boundedConstructible_tensor_continuousMapRingObj ℓ E hK hL) hA hB⟩

/-- Blueprint `proposition-projection-formula-rational-coefficients--2`: The proper projection
formula on the rational localizing categories; the case `Λ = E`.

Let `p : X ⟶ Y` be proper. For `A ∈ Loc(Dbc(X, E))` and `B ∈ Loc(Dbc(Y, E))` the projection
formula map `(Rp_*A) ⊗ᴸ B ⟶ Rp_*(A ⊗ᴸ p^*B)` is an isomorphism. Both sides lie in
`Loc(Dbc(Y, E))` and are exact, direct-sum preserving functors of each variable; the map is an
isomorphism on `Dbc` (`proposition-proper-direct-image-constructible-complexes`), hence on the
localizing categories, one variable at a time
(`lemma-checking-isomorphisms-constructible-complexes--1`). -/
theorem isIso_projectionMap_of_localizingBoundedConstructible_continuousMapRingObj
    (p : X ⟶ Y) [IsProper p.left] {A : 𝔻[𝐄](X.left)} {B : 𝔻[𝐄](Y.left)}
    (hA : localizingBoundedConstructible 𝐄 X.left A)
    (hB : localizingBoundedConstructible 𝐄 Y.left B) :
    IsIso (((projectionMap 𝐄 p.left).app A).app B) :=
  isIso_projectionMap_of_localizingBoundedConstructible 𝐄 p.left
    ((localizingBoundedConstructible_lowerStar_lowerShriek_continuousMapRingObj (X' := X) ℓ E).1
      p).1
    ((localizingBoundedConstructible_lowerStar_lowerShriek_continuousMapRingObj (X' := X) ℓ E).1
      p).2
    (fun L hL ↦ boundedConstructible_leftDerivedUpperStar_obj 𝐄 ℓ p ⟨L, hL⟩)
    (fun _ _ hK hL ↦ boundedConstructible_tensor_continuousMapRingObj ℓ E hK hL)
    (properDirectImage_baseChange_projectionFormula_continuousMapRingObj (X' := X) (Y' := Y) ℓ E
      p).2.2 hA hB

/-- Blueprint `proposition-projection-formula-rational-coefficients`: Projection formula and proper
base change with rational coefficients; the case `Λ = E`.

The category `Loc(Dctf(X, E)) = Loc(Dbc(X, E))` is closed under `⊗ᴸ`. For a proper
`p : X ⟶ Y`, the projection formula map `(Rp_*A) ⊗ᴸ B ⟶ Rp_*(A ⊗ᴸ p^*B)` is an isomorphism for
`A ∈ Loc(Dbc(X, E))` and `B ∈ Loc(Dbc(Y, E))`, and for a cartesian square
`g' ≫ p = p' ≫ g` with `p` proper the base change map `g^*Rp_*A ⟶ Rp'_*g'^*A` is an isomorphism
for `A ∈ Loc(Dbc(X, E))`. The base change statement is
`proposition-proper-base-change-localizing-categories--1`. -/
theorem projectionFormula_baseChange_localizingBoundedConstructible_continuousMapRingObj :
    (∀ A B : 𝔻[𝐄](X.left), localizingBoundedConstructible 𝐄 X.left A →
      localizingBoundedConstructible 𝐄 X.left B →
        localizingBoundedConstructible 𝐄 X.left (A ⊗ B)) ∧
    (∀ (p : X ⟶ Y) [IsProper p.left] (A : 𝔻[𝐄](X.left)) (B : 𝔻[𝐄](Y.left)),
      localizingBoundedConstructible 𝐄 X.left A → localizingBoundedConstructible 𝐄 Y.left B →
        IsIso (((projectionMap 𝐄 p.left).app A).app B)) ∧
    (∀ {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left]
      (sq : IsPullback g' p' p g) (A : 𝔻[𝐄](X.left)), localizingBoundedConstructible 𝐄 X.left A →
        IsIso ((baseChangeMap 𝐄 ((Over.forget _).map_commSq sq.toCommSq)).app A)) :=
  ⟨(tensor_mem_localizingBoundedConstructible_continuousMapRingObj ℓ E).2,
    fun p _ _ _ hA hB ↦
      isIso_projectionMap_of_localizingBoundedConstructible_continuousMapRingObj ℓ E p hA hB,
    fun sq _ hA ↦ isIso_baseChangeMap_of_localizing_continuousMapRingObj ℓ E sq hA⟩

end Field

/-! ### The coefficient field `ℚ̄_ℓ` -/

section AlgCl

set_option hygiene false in
/-- The condensed field `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

omit [Fact (ringChar k).Prime] [IsSeparated X.hom] in
/-- Blueprint `proposition-projection-formula-rational-coefficients--1`: Tensor closure of the
rational localizing categories; the case `Λ = ℚ̄_ℓ`.

1. `Dbc(X, ℚ̄_ℓ)` is closed under `⊗ᴸ` in `D(X_proét, ℚ̄_ℓ)`;
2. for `A, B ∈ Loc(Dbc(X, ℚ̄_ℓ))`, the derived tensor product `A ⊗ᴸ B`, formed in
   `D(X_proét, ℚ̄_ℓ)`, lies in `Loc(Dbc(X, ℚ̄_ℓ))`.

Part (1) is `proposition-six-operations-dctf--14`. For (2), fixing `B ∈ Dbc(X, ℚ̄_ℓ)`, the objects
`A` of `Loc(Dbc(X, ℚ̄_ℓ))` with `A ⊗ᴸ B ∈ Loc(Dbc(X, ℚ̄_ℓ))` form a localizing subcategory
containing `Dbc(X, ℚ̄_ℓ)`, since `- ⊗ᴸ B` is exact and preserves direct sums; then fix `A` and argue
in `B`. -/
theorem tensor_mem_localizingBoundedConstructible_padicAlgClRingObj :
    (∀ K L : 𝔻[𝐐](X.left), boundedConstructible (condensedRingObj 𝐐 X.left) K →
      boundedConstructible (condensedRingObj 𝐐 X.left) L →
        boundedConstructible (condensedRingObj 𝐐 X.left) (K ⊗ L)) ∧
    ∀ A B : 𝔻[𝐐](X.left), localizingBoundedConstructible 𝐐 X.left A →
      localizingBoundedConstructible 𝐐 X.left B → localizingBoundedConstructible 𝐐 X.left (A ⊗ B) :=
  ⟨fun _ _ hK hL ↦ boundedConstructible_tensor_padicAlgClRingObj ℓ hK hL,
    fun _ _ hA hB ↦ localizingBoundedConstructible_tensor 𝐐
      (fun _ _ hK hL ↦ boundedConstructible_tensor_padicAlgClRingObj ℓ hK hL) hA hB⟩

/-- Blueprint `proposition-projection-formula-rational-coefficients--2`: The proper projection
formula on the rational localizing categories; the case `Λ = ℚ̄_ℓ`.

Let `p : X ⟶ Y` be proper. For `A ∈ Loc(Dbc(X, ℚ̄_ℓ))` and `B ∈ Loc(Dbc(Y, ℚ̄_ℓ))` the projection
formula map `(Rp_*A) ⊗ᴸ B ⟶ Rp_*(A ⊗ᴸ p^*B)` is an isomorphism. Both sides lie in
`Loc(Dbc(Y, ℚ̄_ℓ))` and are exact, direct-sum preserving functors of each variable; the map is an
isomorphism on `Dbc` (`proposition-proper-direct-image-constructible-complexes`), hence on the
localizing categories, one variable at a time
(`lemma-checking-isomorphisms-constructible-complexes--1`). -/
theorem isIso_projectionMap_of_localizingBoundedConstructible_padicAlgClRingObj
    (p : X ⟶ Y) [IsProper p.left] {A : 𝔻[𝐐](X.left)} {B : 𝔻[𝐐](Y.left)}
    (hA : localizingBoundedConstructible 𝐐 X.left A)
    (hB : localizingBoundedConstructible 𝐐 Y.left B) :
    IsIso (((projectionMap 𝐐 p.left).app A).app B) :=
  isIso_projectionMap_of_localizingBoundedConstructible 𝐐 p.left
    ((localizingBoundedConstructible_lowerStar_lowerShriek_padicAlgClRingObj (X' := X) ℓ).1 p).1
    ((localizingBoundedConstructible_lowerStar_lowerShriek_padicAlgClRingObj (X' := X) ℓ).1 p).2
    (fun L hL ↦ boundedConstructible_leftDerivedUpperStar_obj 𝐐 ℓ p ⟨L, hL⟩)
    (fun _ _ hK hL ↦ boundedConstructible_tensor_padicAlgClRingObj ℓ hK hL)
    (properDirectImage_baseChange_projectionFormula_padicAlgClRingObj (X' := X) (Y' := Y) ℓ
      p).2.2 hA hB

/-- Blueprint `proposition-projection-formula-rational-coefficients`: Projection formula and proper
base change with rational coefficients; the case `Λ = ℚ̄_ℓ`.

The category `Loc(Dctf(X, ℚ̄_ℓ)) = Loc(Dbc(X, ℚ̄_ℓ))` is closed under `⊗ᴸ`. For a proper
`p : X ⟶ Y`, the projection formula map `(Rp_*A) ⊗ᴸ B ⟶ Rp_*(A ⊗ᴸ p^*B)` is an isomorphism for
`A ∈ Loc(Dbc(X, ℚ̄_ℓ))` and `B ∈ Loc(Dbc(Y, ℚ̄_ℓ))`, and for a cartesian square
`g' ≫ p = p' ≫ g` with `p` proper the base change map `g^*Rp_*A ⟶ Rp'_*g'^*A` is an isomorphism
for `A ∈ Loc(Dbc(X, ℚ̄_ℓ))`. The base change statement is
`proposition-proper-base-change-localizing-categories--1`. -/
theorem projectionFormula_baseChange_localizingBoundedConstructible_padicAlgClRingObj :
    (∀ A B : 𝔻[𝐐](X.left), localizingBoundedConstructible 𝐐 X.left A →
      localizingBoundedConstructible 𝐐 X.left B →
        localizingBoundedConstructible 𝐐 X.left (A ⊗ B)) ∧
    (∀ (p : X ⟶ Y) [IsProper p.left] (A : 𝔻[𝐐](X.left)) (B : 𝔻[𝐐](Y.left)),
      localizingBoundedConstructible 𝐐 X.left A → localizingBoundedConstructible 𝐐 Y.left B →
        IsIso (((projectionMap 𝐐 p.left).app A).app B)) ∧
    (∀ {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left]
      (sq : IsPullback g' p' p g) (A : 𝔻[𝐐](X.left)), localizingBoundedConstructible 𝐐 X.left A →
        IsIso ((baseChangeMap 𝐐 ((Over.forget _).map_commSq sq.toCommSq)).app A)) :=
  ⟨(tensor_mem_localizingBoundedConstructible_padicAlgClRingObj ℓ).2,
    fun p _ _ _ hA hB ↦
      isIso_projectionMap_of_localizingBoundedConstructible_padicAlgClRingObj ℓ p hA hB,
    fun sq _ hA ↦ isIso_baseChangeMap_of_localizing_padicAlgClRingObj ℓ sq hA⟩

end AlgCl

end AlgebraicGeometry.ProEtale.CondensedRing
