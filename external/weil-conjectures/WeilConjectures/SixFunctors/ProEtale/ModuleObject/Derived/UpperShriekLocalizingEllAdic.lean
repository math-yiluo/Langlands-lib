/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness

/-!
# The exceptional inverse image on `Loc(Dᵇc)` for the `ℓ`-adic coefficient rings

For the three families of `ℓ`-adic coefficient rings, schemes separated of finite type over a
field `k` in which `ℓ` is invertible and which is finite or separably closed (so that
`cd_ℓ(k)` is finite; without this, the compact generation fails, e.g. for `k = ℝ`), the two
inputs of the existence theorem
`AlgebraicGeometry.ProEtale.CondensedRing.exists_rightAdjoint_rightDerivedLowerShriekLocalizing`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing`) are the
theorems

| `Λ` | `lemma-hypotheses-brown-representability` |
`proposition-construction-independence-rf-shriek` |
| --- | --- | --- |
| `E` | `compactlyGenerates_continuousMapRingObj` | `lowerShriek_continuousMapRingObj` |
| `𝒪_E` | `compactlyGenerates_padicIntegersRingObj` | `lowerShriek_padicIntegersRingObj` |
| `ℚ̄_ℓ` | `compactlyGenerates_padicAlgClRingObj` | `lowerShriek_padicAlgClRingObj` |

(all in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`), and the existence theorem
follows (`exists_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj`, ...).

The statements of `proposition-construction-independence-rf-shriek` take a separated base `Y` of
finite type over `k`, the setting of the blueprint, in which the ind-constructible heart is
available. A noetherian base is needed in any case: over a merely quasi-compact quasi-separated
base, `Rp_*` need not preserve constructibility. For instance the inclusion `p` of the origin into
`Y = Spec k[x₁, x₂, …]` is proper, but `p_* Λ` is supported on the closed point, which is not a
constructible subset of `Y`.

These theorems are separate from the formal part
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing`) since their
proofs use the reduction to residue field coefficients, which imports the formal part.

## Sorried input

- The inputs of `isCompactObj_singleLocalizingBoundedConstructible_continuousMapRingObj`,
  `isCompactObj_singleLocalizingBoundedConstructible_padicAlgClRingObj` (blueprint
  `theorem-compactness-rational-coefficients`) and
  `isCompactObj_singleLocalizingBoundedConstructible_padicIntegersRingObj` (blueprint
  `proposition-compactness-proper-direct-image`), that constructible sheaves are compact in
  `Loc(Dᵇc(X)⟦Λ⟧)`: the closure properties of the ind-constructible sheaves
  (`proposition-ind-constructible-sheaves`), the continuity of `Ext` out of a constructible sheaf
  (`lemma-continuity-ext-out-constructible-complex--1`) and the uniform `Ext` bound
  (`lemma-uniform-ext-bound`), see
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic`. The
  compactness follows by the finite-window argument and left completeness. By dévissage, all bounded
  constructible complexes are compact
  (`isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible`).
- The inputs of `properLowerStarHypotheses_continuousMapRingObj`,
  `properLowerStarHypotheses_padicAlgClRingObj` and
  `properLowerStarHypotheses_padicIntegersRingObj` (for `p` proper, `Rp_*` preserves `Dᵇc` and
  direct sums on `Loc(Dᵇc)`): that `Rp_*` preserves `Dᵇc` (blueprint
  `proposition-proper-direct-image-constructible-complexes`) and has finite amplitude and commutes
  with direct sums on the ind-constructible heart (blueprints
  `lemma-uniform-bound-proper-direct-image`, `proposition-compactness-proper-direct-image--2` (1)),
  see `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic`. The
  commutation with direct sums on `Loc(Dᵇc)` follows by dévissage and left completeness
  (`ProperLowerStarHeartHypotheses.preservesColimitsOfShape`).
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The `ℓ`-adic coefficient rings -/

section EllAdic

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]

/-! #### The coefficient ring `E` -/

/-- Blueprint `theorem-compactness-rational-coefficients`
(`theorem-compactness-rational-coefficients`): for the coefficient ring `E` of a finite extension
`E` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`, the constructible sheaves are compact
objects of `Loc(Dᵇc(X)⟦E⟧)`. -/
theorem isCompactObj_singleLocalizingBoundedConstructible_continuousMapRingObj (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X))
    (hM : IsConstructibleModuleObject _ M) : BrownRepresentability.IsCompactObj
      (singleLocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X M hM) :=
  isCompactObj_singleFunctor_continuousMapRingObj ℓ E aX hk M hM _

/-- Blueprint `theorem-compactness-rational-coefficients`: for the coefficient ring `E` of a finite
extension `E` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`, the bounded constructible
complexes are compact objects of `Loc(Dᵇc(X)⟦E⟧)`, by dévissage to constructible sheaves. -/
theorem isCompactObj_boundedConstructible_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (K : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X)
    (hK : boundedConstructible _ K.obj) : BrownRepresentability.IsCompactObj K :=
  isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible _ X
    (isCompactObj_singleLocalizingBoundedConstructible_continuousMapRingObj ℓ E aX hk) K hK

/-- Blueprint `lemma-hypotheses-brown-representability`: Hypotheses of Brown representability, for
the coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` (including `E = ℚ_ℓ`) and a separated
finite-type `k`-scheme `X`. The category `Loc(Dᵇc(X)⟦E⟧)` is locally small, triangulated and has
direct sums (by construction); it has split idempotents, and `Dᵇc(X)⟦E⟧ = Dctf(X, E)` is
essentially small, with a small skeleton forming a set of compact generators. -/
theorem compactlyGenerates_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k) :
    (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} E)
        X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete (LocalizingBoundedConstructible (Profinite.continuousMapRingObj E) X) :=
  have := isNoetherian_of_locallyOfFiniteType aX
  compactlyGenerates_of_isCompactObj _ X
    (isCompactObj_boundedConstructible_continuousMapRingObj ℓ E aX hk)

/-- Blueprints `proposition-proper-direct-image-constructible-complexes` and
`proposition-proper-direct-image-extension-zero`: for the coefficient ring `E` of a finite extension
`E` of `ℚ_ℓ` and a proper morphism `p : Z ⟶ Y` to a separated finite-type `k`-scheme, `Rp_*` maps
`Dᵇc(Z)⟦E⟧` into `Dᵇc(Y)⟦E⟧` and preserves direct sums on `Loc(Dᵇc(Z)⟦E⟧)`. -/
theorem properLowerStarHypotheses_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {Z Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (p : Z ⟶ Y) [IsProper p] :
    ProperLowerStarHypotheses (Profinite.continuousMapRingObj.{u} E) p :=
  have := isNoetherian_of_locallyOfFiniteType aY
  ⟨boundedConstructible_rightDerivedLowerStar_of_isProper_continuousMapRingObj_of_finiteType ℓ p aY
      E,
    (properLowerStarHeartHypotheses_continuousMapRingObj ℓ E aY p).preservesColimitsOfShape⟩

/-- Blueprint `proposition-construction-independence-rf-shriek`: Compact support along one
compactification on the localizing category, for the coefficient ring `E` of a finite extension `E`
of `ℚ_ℓ` and a separated finite-type `k`-scheme `Y`: for a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)`
of `f`, `Rp_* ∘ j_!` maps `Loc(Dctf(X, E))` into `Loc(Dctf(Y, E))` and `Dctf(X, E)` into
`Dctf(Y, E)`, and preserves direct sums on `Loc(Dctf(X, E))`. -/
theorem lowerShriek_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    {f : X ⟶ Y} (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.continuousMapRingObj.{u} E) c :=
  have := isNoetherian_of_locallyOfFiniteType aY
  have := isNoetherian_of_locallyOfFiniteType c.g
  lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses _ c
    (properLowerStarHypotheses_continuousMapRingObj ℓ E aY c.g)

/-! #### The coefficient ring `𝒪_E` -/

/-- Blueprint `proposition-compactness-proper-direct-image` (compactness of constructible sheaves):
for the coefficient ring `𝒪_E` of the ring of integers of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and
a separated finite-type `k`-scheme `X`, the constructible sheaves are compact objects of
`Loc(Dᵇc(X)⟦𝒪_E⟧)`. -/
theorem isCompactObj_singleLocalizingBoundedConstructible_padicIntegersRingObj (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X))
    (hM : IsConstructibleModuleObject _ M) : BrownRepresentability.IsCompactObj
      (singleLocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X M hM) :=
  isCompactObj_singleFunctor_padicIntegersRingObj ℓ E aX hk M hM _

/-- Blueprint `proposition-compactness-proper-direct-image`: for the coefficient ring `𝒪_E` of the
ring of integers of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated finite-type `k`-scheme
`X`, the bounded constructible complexes are compact objects of `Loc(Dᵇc(X)⟦𝒪_E⟧)`, by dévissage to
constructible sheaves. -/
theorem isCompactObj_boundedConstructible_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (K : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X)
    (hK : boundedConstructible _ K.obj) : BrownRepresentability.IsCompactObj K :=
  isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible _ X
    (isCompactObj_singleLocalizingBoundedConstructible_padicIntegersRingObj ℓ E aX hk) K hK

/-- Blueprint `lemma-hypotheses-brown-representability`: Hypotheses of Brown representability, for
the coefficient ring `𝒪_E` of the ring of integers of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(including `ℤ_ℓ`, for `E = ℚ_ℓ`) and a separated finite-type `k`-scheme `X`: `Loc(Dᵇc(X)⟦𝒪_E⟧)`
has split idempotents, and `Dᵇc(X)⟦𝒪_E⟧ = Dctf(X, 𝒪_E)` is essentially small, with a small
skeleton forming a set of compact generators. -/
theorem compactlyGenerates_padicIntegersRingObj (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aX] (hk : Finite k ∨ IsSepClosed k) :
    (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E)
        X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete
        (LocalizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X) :=
  have := isNoetherian_of_locallyOfFiniteType aX
  compactlyGenerates_of_isCompactObj _ X
    (isCompactObj_boundedConstructible_padicIntegersRingObj ℓ E aX hk)

/-- Blueprints `proposition-proper-direct-image-constructible-complexes` and
`proposition-compactness-proper-direct-image` (direct sums): for the coefficient ring `𝒪_E` of a
finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a proper morphism `p : Z ⟶ Y` to a separated finite-type
`k`-scheme, `Rp_*` maps `Dᵇc(Z)⟦𝒪_E⟧` into `Dᵇc(Y)⟦𝒪_E⟧` and preserves direct sums on
`Loc(Dᵇc(Z)⟦𝒪_E⟧)`. -/
theorem properLowerStarHypotheses_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] [IsSeparated aY] (p : Z ⟶ Y) [IsProper p] :
    ProperLowerStarHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) p :=
  have := isNoetherian_of_locallyOfFiniteType aY
  ⟨boundedConstructible_rightDerivedLowerStar_of_isProper_padicIntegersRingObj_of_finiteType ℓ p aY
      E,
    (properLowerStarHeartHypotheses_padicIntegersRingObj ℓ E aY p).preservesColimitsOfShape⟩

/-- Blueprint `proposition-construction-independence-rf-shriek`: Compact support along one
compactification on the localizing category, for the coefficient ring `𝒪_E` of a finite extension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated finite-type `k`-scheme `Y`: for a compactification
`c = (X ⟶[j] X̄ ⟶[p] Y)` of `f`, `Rp_* ∘ j_!` maps `Loc(Dctf(X, 𝒪_E))` into `Loc(Dctf(Y, 𝒪_E))` and
`Dctf(X, 𝒪_E)` into `Dctf(Y, 𝒪_E)`, and preserves direct sums on `Loc(Dctf(X, 𝒪_E))`. -/
theorem lowerShriek_padicIntegersRingObj (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY] {f : X ⟶ Y} (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.padicIntegersRingObj.{u} ℓ E) c :=
  have := isNoetherian_of_locallyOfFiniteType aY
  have := isNoetherian_of_locallyOfFiniteType c.g
  lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses _ c
    (properLowerStarHypotheses_padicIntegersRingObj ℓ E aY c.g)

/-! #### The coefficient ring `ℚ̄_ℓ` -/

/-- Blueprint `theorem-compactness-rational-coefficients`
(`theorem-compactness-rational-coefficients`): for the coefficient ring `ℚ̄_ℓ` and a separated
finite-type `k`-scheme `X`, the constructible sheaves are compact objects of `Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧)`. -/
theorem isCompactObj_singleLocalizingBoundedConstructible_padicAlgClRingObj {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X))
    (hM : IsConstructibleModuleObject _ M) : BrownRepresentability.IsCompactObj
      (singleLocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X M hM) :=
  isCompactObj_singleFunctor_padicAlgClRingObj ℓ aX hk M hM _

/-- Blueprint `theorem-compactness-rational-coefficients`: for the coefficient ring `ℚ̄_ℓ` and a
separated finite-type `k`-scheme `X`, the bounded constructible complexes are compact objects of
`Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧)`, by dévissage to constructible sheaves. -/
theorem isCompactObj_boundedConstructible_padicAlgClRingObj {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (K : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X)
    (hK : boundedConstructible _ K.obj) : BrownRepresentability.IsCompactObj K :=
  isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible _ X
    (isCompactObj_singleLocalizingBoundedConstructible_padicAlgClRingObj ℓ aX hk) K hK

/-- Blueprint `lemma-hypotheses-brown-representability`: Hypotheses of Brown representability, for
the coefficient ring `ℚ̄_ℓ` and a separated finite-type `k`-scheme `X`: `Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧)` has
split idempotents, and `Dᵇc(X)⟦ℚ̄_ℓ⟧ = Dctf(X, ℚ̄_ℓ)` is essentially small, with a small skeleton
forming a set of compact generators. -/
theorem compactlyGenerates_padicAlgClRingObj {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k) :
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ)
        X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete (LocalizingBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) :=
  have := isNoetherian_of_locallyOfFiniteType aX
  compactlyGenerates_of_isCompactObj _ X
    (isCompactObj_boundedConstructible_padicAlgClRingObj ℓ aX hk)

/-- Blueprints `proposition-proper-direct-image-constructible-complexes` and
`proposition-proper-direct-image-extension-zero`: for the coefficient ring `ℚ̄_ℓ` and a proper
morphism `p : Z ⟶ Y` to a separated finite-type `k`-scheme, `Rp_*` maps `Dᵇc(Z)⟦ℚ̄_ℓ⟧` into
`Dᵇc(Y)⟦ℚ̄_ℓ⟧` and preserves direct sums on `Loc(Dᵇc(Z)⟦ℚ̄_ℓ⟧)`. -/
theorem properLowerStarHypotheses_padicAlgClRingObj {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (p : Z ⟶ Y) [IsProper p] :
    ProperLowerStarHypotheses (Profinite.padicAlgClRingObj.{u} ℓ) p :=
  have := isNoetherian_of_locallyOfFiniteType aY
  ⟨boundedConstructible_rightDerivedLowerStar_of_isProper_padicAlgClRingObj_of_finiteType ℓ p aY,
    (properLowerStarHeartHypotheses_padicAlgClRingObj ℓ aY p).preservesColimitsOfShape⟩

/-- Blueprint `proposition-construction-independence-rf-shriek`: Compact support along one
compactification on the localizing category, for the coefficient ring `ℚ̄_ℓ` and a separated
finite-type `k`-scheme `Y`: for a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f`, `Rp_* ∘ j_!`
maps `Loc(Dctf(X, ℚ̄_ℓ))` into `Loc(Dctf(Y, ℚ̄_ℓ))` and `Dctf(X, ℚ̄_ℓ)` into `Dctf(Y, ℚ̄_ℓ)`, and
preserves direct sums on `Loc(Dctf(X, ℚ̄_ℓ))`. -/
theorem lowerShriek_padicAlgClRingObj {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] {f : X ⟶ Y}
    (c : Compactification f) :
    LowerShriekLocalizingHypotheses (Profinite.padicAlgClRingObj.{u} ℓ) c :=
  have := isNoetherian_of_locallyOfFiniteType aY
  have := isNoetherian_of_locallyOfFiniteType c.g
  lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses _ c
    (properLowerStarHypotheses_padicAlgClRingObj ℓ aY c.g)

variable {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] {f : X ⟶ Y} (c : Compactification f)
  (hk : Finite k ∨ IsSepClosed k)

include aX hk in
/-- Blueprint `theorem-existence-exceptional-inverse-image`: Existence of the exceptional inverse
image, for the coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` (including `ℚ_ℓ`) and
separated finite-type `k`-schemes `X`, `Y`. For a compactification `c` of `f : X ⟶ Y`, the
coproduct-preserving functor `Rf_! : Loc(Dctf(X, E)) ⥤ Loc(Dctf(Y, E))` has a right adjoint
`f^!`, which commutes with shifts compatibly with the adjunction, is exact (triangulated),
preserves direct sums and is unique up to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ (G : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y ⥤
        LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X)
      (adj : rightDerivedLowerShriekLocalizing
        (lowerShriek_continuousMapRingObj ℓ E aY c) ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y ⥤
          LocalizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X)
        (adj' : rightDerivedLowerShriekLocalizing
          (lowerShriek_continuousMapRingObj ℓ E aY c) ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing
          (lowerShriek_continuousMapRingObj ℓ E aY c)).map (e.hom.app N) ≫
            adj'.counit.app N = adj.counit.app N :=
  exists_rightAdjoint_rightDerivedLowerShriekLocalizing _
    (compactlyGenerates_continuousMapRingObj ℓ E aX hk).1
    (compactlyGenerates_continuousMapRingObj ℓ E aY hk).1

include aX hk in
/-- Blueprint `theorem-existence-exceptional-inverse-image`: Existence of the exceptional inverse
image, for the coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (including `ℤ_ℓ`)
and separated finite-type `k`-schemes `X`, `Y`. For a compactification `c` of `f : X ⟶ Y`, the
coproduct-preserving functor `Rf_! : Loc(Dctf(X, 𝒪_E)) ⥤ Loc(Dctf(Y, 𝒪_E))` has a right adjoint
`f^!`, which commutes with shifts compatibly with the adjunction, is exact (triangulated),
preserves direct sums and is unique up to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing_padicIntegersRingObj (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ (G : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) Y ⥤
        LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X)
      (adj : rightDerivedLowerShriekLocalizing
        (lowerShriek_padicIntegersRingObj ℓ E aY c) ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) Y ⥤
          LocalizingBoundedConstructible (Profinite.padicIntegersRingObj.{u} ℓ E) X)
        (adj' : rightDerivedLowerShriekLocalizing
          (lowerShriek_padicIntegersRingObj ℓ E aY c) ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing
          (lowerShriek_padicIntegersRingObj ℓ E aY c)).map (e.hom.app N) ≫
            adj'.counit.app N = adj.counit.app N :=
  exists_rightAdjoint_rightDerivedLowerShriekLocalizing _
    (compactlyGenerates_padicIntegersRingObj ℓ E aX hk).1
    (compactlyGenerates_padicIntegersRingObj ℓ E aY hk).1

include aX hk in
/-- Blueprint `theorem-existence-exceptional-inverse-image`: Existence of the exceptional inverse
image, for the coefficient ring `ℚ̄_ℓ` and separated finite-type `k`-schemes `X`, `Y`. For a
compactification `c` of `f : X ⟶ Y`, the coproduct-preserving functor
`Rf_! : Loc(Dctf(X, ℚ̄_ℓ)) ⥤ Loc(Dctf(Y, ℚ̄_ℓ))` has a right adjoint `f^!`, which commutes with
shifts compatibly with the adjunction, is exact (triangulated), preserves direct sums and is
unique up to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing_padicAlgClRingObj :
    ∃ (G : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y ⥤
        LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X)
      (adj : rightDerivedLowerShriekLocalizing
        (lowerShriek_padicAlgClRingObj ℓ aY c) ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y ⥤
          LocalizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X)
        (adj' : rightDerivedLowerShriekLocalizing
          (lowerShriek_padicAlgClRingObj ℓ aY c) ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing
          (lowerShriek_padicAlgClRingObj ℓ aY c)).map (e.hom.app N) ≫
            adj'.counit.app N = adj.counit.app N :=
  exists_rightAdjoint_rightDerivedLowerShriekLocalizing _
    (compactlyGenerates_padicAlgClRingObj ℓ aX hk).1
    (compactlyGenerates_padicAlgClRingObj ℓ aY hk).1

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
