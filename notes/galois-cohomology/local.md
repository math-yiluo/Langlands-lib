# Galois cohomology of local fields

This note describes `Langlands/GaloisCohomology/Local/` (namespace
`Langlands.GaloisCohomology.Local`): the Galois cohomology of a nonarchimedean local field `K` of
any characteristic, with finite coefficients of order invertible in `K`. It rests on the layers of
[cohomology of profinite groups and Galois cohomology of fields](profinite-and-fields.md); its
results are used at the places of a number field by [global Galois cohomology](global.md) and
[Poitou–Tate duality](poitou-tate.md). The [overview](overview.md) gives the whole.

## The mathematics

Let `K` be a nonarchimedean local field, Ksep a separable closure and `G = Gal(Ksep/K)`. Local
class field theory makes `(G, Ksepˣ)` a class formation, with the invariant
`inv : H²(G, Ksepˣ) ≅ ℚ/ℤ`; its compatibility with the local Artin map is the cup symbol
`inv(δχ ∪ a) = χ(Art(a))`. From these, for finite modules `M` of order invertible in `K`, the
classical theorems of Tate follow: `cd_ℓ(G) ≤ 2` for every prime `ℓ` invertible in `K`, finiteness of
the `Hʳ(G, M)`, local Tate duality `Hʳ(G, M) × H^{2-r}(G, M') → H²(G, Ksepˣ) ≅ ℚ/ℤ` with
`M' = Hom(M, Ksepˣ)`, and the local Euler characteristic formula
`|H⁰(M)|·|H²(M)|/|H¹(M)| = |𝒪_K/|M|𝒪_K|⁻¹`. The unramified classes (those vanishing on inertia)
are orthogonal to each other under the Tate pairing, and each is the exact annihilator of the other
when `|M|` is prime to the residue characteristic. The references followed are Serre, *Galois
Cohomology*, II §5, Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, VII §§1–3, and Tate's
address *Duality theorems in Galois cohomology over number fields* (Stockholm, 1962); these treat
`p`-adic fields, and the Library's statements cover every nonarchimedean local field with `|M|`
invertible in `K`. Each page gives the exact places.

## Layout

| Files | Content |
| --- | --- |
| `Invariant.lean` | the invariant `H²(Gal(Ksep/K), Ksepˣ) ≃ ℚ/ℤ`, on open subgroups, restriction law |
| `ClassFormation.lean` | the class formation of `K` |
| `CharacterCup.lean`, `CupSymbol.lean` | the class `δχ ∪ a` and the cup symbol |
| `Dimension.lean`, `Finiteness.lean` | `cd_ℓ ≤ 2`, vanishing in degrees `≥ 3`, finiteness |
| `Duality/` | the invariant on `H²(U, μ_n)`, norm groups of abelian extensions, the cup product of a character with a Kummer class, the Tate pairing, local Tate duality, the existence theorem for norm groups containing `n`-th powers |
| `EulerCharacteristic/` | the local Euler characteristic formula and its steps (coinduced modules, coprime descent, twisting by μ_l, Kummer theory over open subgroups, the units as a Galois module, vanishing under tame inertia, group structure of the Galois group) |
| `Unramified.lean` | unramified classes and their orthogonality |
| `Arithmetic/` | local-field lemmas used by the proofs: valuative extensions, rings of integers, uniqueness of the structure of a finite extension, valuations on algebraic extensions, `n`-th powers, the unit filtration, ramification groups, lattices spanned by a normal basis |

The order of dependence is `Arithmetic/` → `Invariant.lean`, `ClassFormation.lean` → `CharacterCup.lean`,
`CupSymbol.lean`; `ClassFormation.lean` → `Finiteness.lean` → `Dimension.lean` → `Duality/Pairing.lean` (with
`Duality/RootsOfUnity.lean`, `Duality/NormCharacters.lean`, `Duality/KummerCup.lean`) and
`EulerCharacteristic/Main.lean` → `Duality/Main.lean` → `Duality/Existence.lean`, `Unramified.lean`. Local duality is first proved in `Duality/Pairing.lean` under a
counting hypothesis, which `Duality/Main.lean` derives from the Euler characteristic formula.

## The fields

The local fields are Mathlib's: `K : Type u` with `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`, of any characteristic, and `Ksep : Type u` with `[IsSepClosure K Ksep]`
(the field and its separable closure in **one universe** `u`, any `u`). The modules are
`M : Rep IntegerScalars.{u} Gal(Ksep/K)` with `[IsSmoothRep M] [Finite M]`, and the condition on
the order is `(Nat.card M : K) ≠ 0`, which is vacuous in characteristic `0`.

## Main definitions and theorems

- `invariant K Ksep : H²(Gal(Ksep/K), Ksepˣ) ≃+ RationalModIntegers` (`Invariant.lean`), defined
  as the Library's Brauer invariant `localBrauerInvariant K` read through
  `Langlands.GaloisCohomology.brauerEquiv`; `invariant_brauerEquiv` says so.
  `invariant_unitsRestriction`: restriction to a finite extension `L` multiplies the invariant by
  `[L : K]`. `openInvariant K U` is the invariant of the fixed field of an open subgroup `U`, and
  `openInvariant_resOfLE` is the restriction law `inv_V ∘ res = [U : V] · inv_U`.
- `classFormation K Ksep : ClassFormation (unitsModule K Ksep)` (`ClassFormation.lean`).
- `characterCup K Ksep χ hχ a ∈ H²(Gal(Ksep/K), Ksepˣ)` for a character
  `χ : Gal(Ksep/K) →* Multiplicative RationalModIntegers` with open kernel and `a ∈ Kˣ`: the cup
  product of `δχ ∈ H²(G, ℤ)` with `a ∈ H⁰(G, Ksepˣ)` (`CharacterCup.lean`).
- **The cup symbol** `invariant_characterClass_cup` (`CupSymbol.lean`): for such `χ`, `a ∈ Kˣ` and
  `σ ∈ Gal(Ksep/K)` with `IsArithmeticArtinLift K Ksep a σ`,
  `invariant K Ksep (characterCup K Ksep χ hχ a) = χ(σ)`. Lifts exist for every `a`
  (`Langlands.ClassFieldTheory.Local.Artin.exists_isArithmeticArtinLift`).
- **Dimension** (`Dimension.lean`): `cd_le_two`: `cd ℓ Gal(Ksep/K) ≤ 2` for a prime `ℓ` with
  `(ℓ : K) ≠ 0`; `subsingleton_cohomology_of_three_le`: `Hʳ(G, M) = 0` for `r ≥ 3` and every smooth
  module killed by an `n` with `(n : K) ≠ 0`; `finite_cohomology`: `Hʳ(G, M)` is finite for every `r`
  and every finite smooth `M` with `(Nat.card M : K) ≠ 0`; `hasFiniteCohomology` is the hypothesis
  `Langlands.ProfiniteCohomology.HasFiniteCohomology` of the Euler characteristic for this class of modules.
- **Local Tate duality** (`Duality/`): `tatePairing K Ksep M h : Hʳ(M) →+ Hˢ(M') →+ RationalModIntegers`
  for `h : r + s = 2`, with `M' = cartierDual K Ksep M = Hom(M, Ksepˣ)`: the cup product into
  `H²(Ksepˣ)` followed by `invariant` (`Duality/Pairing.lean`). `tatePairing_bijective` and
  `tatePairing_flip_bijective` (`Duality/Main.lean`): for finite smooth `M` with
  `(Nat.card M : K) ≠ 0`, both `Hʳ(M) → Hom(Hˢ(M'), ℚ/ℤ)` and `Hˢ(M') → Hom(Hʳ(M), ℚ/ℤ)` are
  bijective. The counting hypothesis `CardCohomologyOneLe` of `Duality/Pairing.lean` is proved as
  `cardCohomologyOneLe`.
- **Norm groups** (`Duality/NormCharacters.lean`, `Duality/Existence.lean`): for a finite abelian
  extension L/K (`K L : Type u`), `reciprocityEquiv K L : Gal(L/K) ≃* Kˣ ⧸ N(Lˣ)` and the norm index
  `index_fieldNormSubgroup_of_isAbelianGalois : [Kˣ : N(Lˣ)] = [L : K]`; the norm group is the NYLL
  copy's `LocalFieldTheory.DiscreteValuationField.fieldNormSubgroup`. The existence theorem
  `exists_isAbelianGalois_fieldNormSubgroup_eq`: for `(n : K) ≠ 0`, every subgroup of `Kˣ` containing
  Kˣⁿ is the norm group of a finite abelian extension of `K` inside Ksep.
- **The Euler characteristic formula** (`EulerCharacteristic/Main.lean`): `eulerCharacteristic_eq`:
  for finite smooth `M` with `(Nat.card M : K) ≠ 0`,
  `ProfiniteCohomology.eulerCharacteristic M = |𝒪[K] ⧸ (Nat.card M)|⁻¹`; `card_cohomology_one` is the
  same multiplied out, `|H¹| = |H⁰| · |H²| · |𝒪[K] ⧸ (Nat.card M)|`.
- **Unramified classes** (`Unramified.lean`): `unramifiedClasses K Ksep M ⊆ H¹(G, M)`, the classes
  whose restriction to the inertia subgroup (the Library's `LocalGalois.SepClosed.absoluteInertia`)
  vanishes; `card_unramifiedClasses`: for finite `M` there are as many as `|M^G|`;
  `tatePairing_eq_zero_of_mem_unramifiedClasses`: unramified classes of `M` and of `M'` are
  orthogonal; `mem_unramifiedClasses_cartierDual_iff`: if `|M|` is prime to the residue
  characteristic, a class of `H¹(M')` is unramified iff it is orthogonal to all unramified classes of
  `M`. `isZHatGenerator_frobenius_one` and `exists_isZHatGenerator_inertia` give G/I its
  `ℤ̂`-generator through the Library's residue degree `Weil.Local.SepClosed.localResidueDegree`.

## Conventions

- **The invariant is normalized by the arithmetic Frobenius**, as the Library's
  `localBrauerInvariant` is: on a class inflated from an unramified extension it is Serre's
  unramified invariant (valuation, inverse connecting map, arithmetic Frobenius)
  (`invariant_unramified`, `CupSymbol.lean`).
- **The cup symbol uses arithmetic Artin lifts.** `IsArithmeticArtinLift K Ksep a σ`
  (`Langlands/ClassFieldTheory/Local/Artin/ArtinLift.lean`) says that `σ` restricts to the
  arithmetic Artin symbol `arithmeticFiniteArtin K L a` on every finite abelian subextension `L`;
  `arithmeticFiniteArtin` sends a uniformizer to the arithmetic Frobenius
  (`arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius_zpow`) and is the geometric map
  `geometricFiniteArtin` (the NYLL copy's) composed with inversion. `invariant_characterClass_cup`
  fixes this convention: `inv(δχ ∪ a) = χ(σ)`, with no sign.
- **The pairing.** The Tate pairing is `x ⊗ y ↦ inv(x ∪ y)` with the evaluation `M ⊗ M' → Ksepˣ`
  and the cup product of the foundations (left factor `M`); `M'` is the Cartier dual, not the
  Pontryagin dual; the dual of a group is `Hom(·, ℚ/ℤ)`.

## What is stated without proof

Nothing: the directory has no `…Statement`. `CardCohomologyOneLe` is a hypothesis of
`Duality/Pairing.lean` that `cardCohomologyOneLe` proves.

## Why it is built this way

- The invariant and the Artin map are the Library's (`localBrauerInvariant`, the local Artin maps
  of `Langlands/ClassFieldTheory/Local/Artin/`), not constructed again: the local layer adds the
  cohomological statements. Class field theory enters through the invariant, the Artin lifts of the
  cup symbol, and the reciprocity isomorphism and norm index of `Duality/NormCharacters.lean` (from
  the local Artin map of the bridge `Langlands/ClassFieldTheory/Local/Artin/NormSubgroup.lean`); the existence theorem for norm groups containing `n`-th powers
  is derived here from duality.
- The theorems are stated for Mathlib's `IsNonarchimedeanLocalField`, so they apply at once to the
  completions of a number field at its finite places (the structure
  `Langlands.Global.FiniteCompletion.valuativeRel`) and in positive characteristic.
- `Duality/NormCharacters.lean` reaches the local reciprocity of the NYLL copy through the bridge
  `Langlands.ClassFieldTheory.Local.Artin.abelianArtinHom` (see
  [the roots and the import rule](../library/roots-and-import-rule.md)).

## Origin of the text

25 of the 31 files are ported from the repository leanprover-community/riemann-hypothesis (commit
`f1f6d65`); the others, among them `Duality/Main.lean`, contain no text of the source (their pages say so: the source proves
duality with the existence theorem, the Library by the counting from the Euler characteristic).
Each page names its source, and `licenses/RiemannHypothesis/SOURCE.md` describes the source and the
terms of its use.
