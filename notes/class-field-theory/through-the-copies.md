# Class field theory through the NYLL copy: the bridges and what the Library proves itself

This note describes how the Library obtains the local and global Artin maps, the existence theorem
and the principal ideal theorem from the copy `Nyll/` of the NYLL library, through the bridge files
of `Langlands/ClassFieldTheory/Global/Artin/`, `Langlands/ClassFieldTheory/Local/Artin/`,
`Langlands/ClassFieldTheory/Local/General/` and `Langlands/ClassFieldTheory/Local/QuadraticNormIndex.lean`,
and what of class field theory the Library proves on its own side. The copy and the import rule are
described in [the roots of the repository and the import rule](../library/roots-and-import-rule.md);
the Library's own local class field theory in
[local class-field theory: constructions and statement coverage](local-coverage.md).

## The mathematics

Local class field theory gives, for a finite abelian extension L/K of nonarchimedean local fields,
the reciprocity isomorphism `Kˣ/N(Lˣ) ≅ Gal(L/K)`, normalized on unramified extensions by sending a
uniformizer to a Frobenius, compatible with towers and norms. Global class field theory gives, for a
number field `K`, the Artin map from the idèle class group `C_K` onto the abelianized absolute Galois
group, with kernel the connected component of the identity, compatible with the local maps; every
open subgroup of `C_K` of finite index is the norm group of a unique finite abelian extension (the
existence theorem); and the Hilbert class field capitulates every ideal (the principal ideal
theorem). NYLL proves all of these in its own notions (its idèles, its ramification groups, its class
formations); the Library states them in its own and in Mathlib's vocabulary — Mathlib's
`IsNonarchimedeanLocalField`, Mathlib's idèle class group `NumberField.IdeleClassGroup` (the Library's
`Langlands.Global.IdeleClasses`), subfields of `AlgebraicClosure K` — and proves each statement from
the copy in a bridge file.

## Local: the bridges

In `Langlands/ClassFieldTheory/Local/Artin/` (namespace `Langlands.ClassFieldTheory.Local.Artin`), for
`K` a nonarchimedean local field of any characteristic and L/K finite abelian:

- `geometricFiniteArtin K L : Kˣ →ₜ* Gal(L/K)` is NYLL's
  `LocalClassFieldTheory.Universe.abelianLocalArtinMap K L` (`FiniteArtin.lean`), and
  `arithmeticFiniteArtin K L` is the geometric map of the inverse unit. Both are surjective with
  kernel the norm group (`geometricFiniteArtin_surjective`, `geometricFiniteArtin_ker`,
  `arithmeticFiniteArtin_surjective`, `arithmeticFiniteArtin_ker`) and compatible with restriction in
  towers and with norms (`restrictNormalHom_arithmeticFiniteArtin`,
  `restrictNormalHom_arithmeticFiniteArtin_normUnits`); the arithmetic family satisfies the Library's
  `FiniteArtinSystemRelation` (`finiteArtinSystemRelation_arithmeticFiniteArtinFamily`).
- `arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius_zpow` (`FiniteArtinNormalization.lean`): on an
  unramified stage, `arithmeticFiniteArtin K E x` is the Library's arithmetic Frobenius to the power
  of the normalized order of `x`; `arithmeticFiniteArtin_eq_arithmeticFrobenius_zpow` is the same in
  NYLL's vocabulary.
- `IsArithmeticArtinLift K Ksep a σ` and `exists_isArithmeticArtinLift` (`ArtinLift.lean`): an element
  of `Gal(Ksep/K)` restricting to `arithmeticFiniteArtin K L a` on every finite abelian subextension;
  lifts exist and multiply. This is the notion in which the cup symbol of local Galois cohomology is
  stated (see [local Galois cohomology](../galois-cohomology/local.md)).
- `geometricSymbol_eq_geometricFiniteArtin` and `artinSymbol_eq_arithmeticFiniteArtin`
  (`PadicComparison.lean`): on a `p`-adic field `F` (`Langlands.PadicField` with any supplied
  topological datum), the Library's own geometric and arithmetic finite Artin symbols
  (`FiniteArtinSystemExistence.geometricSymbol`, built from the Library's cohomological local class
  field theory) are the maps of the copy.
- `Langlands/ClassFieldTheory/Local/General/`: `suppliedUnramifiedValuedExtension` and
  `suppliedValuationSign` prove `SuppliedUnramifiedValuedExtensionStatement` and
  `SuppliedValuationSignStatement`, which identify NYLL's unramified class and valuation map with the
  Library's notions for any supplied realization of a `p`-adic field (NYLL's valuation is minus the
  Library's order).
- `Langlands.LocalClassField.index_range_norm_eq_two` and `Langlands.LocalClassField.normResidueSign`
  (`Langlands/ClassFieldTheory/Local/QuadraticNormIndex.lean`): the norm group of a quadratic extension
  of nonarchimedean local fields (`F E : Type`) has index two, and its quadratic character.
- `Langlands.ClassFieldTheory.Local.Artin.abelianArtinHom`
  (`Langlands/ClassFieldTheory/Local/Artin/NormSubgroup.lean`): the local Artin map `Kˣ →* Gal(L/K)` of a
  finite abelian extension of nonarchimedean local fields, surjective (`abelianArtinHom_surjective`)
  with kernel the norm group (`abelianArtinHom_ker`). From it
  `Langlands/GaloisCohomology/Local/Duality/NormCharacters.lean` has the reciprocity isomorphism
  `Langlands.GaloisCohomology.Local.reciprocityEquiv` and the norm index
  `Langlands.GaloisCohomology.Local.index_fieldNormSubgroup_of_isAbelianGalois`.
- `Langlands/ClassFieldTheory/Local/NormalSubgroupFiltration.lean`: the two laws of the copy's structure of
  an antitone filtration of a group by normal subgroups (`antitone_lower`, `normal_lower`), for
  `Langlands/Shimura/DefiniteFormsTower.lean`.

## Global: the bridges

In `Langlands/ClassFieldTheory/Global/Artin/` (namespace `Langlands.ClassFieldTheory.Global.Artin`), for
a number field `K : Type u`:

- `nyllIdeleClassEquiv : _root_.IdeleClassGroup K ≃ₜ* IdeleClasses K` (NYLL's `IdeleClassGroup`, in the root namespace) (`IdeleClassComparison.lean`):
  NYLL's idèle class group and Mathlib's are isomorphic as topological groups.
- `arithmeticFiniteArtin K L : IdeleClasses K →* (L ≃ₐ[K] L)` (`FiniteArtin.lean`) for `L : Type v`
  finite abelian over `K`: NYLL's map read on the Library's idèle classes, in the arithmetic
  normalization; surjective and continuous (`arithmeticFiniteArtin_surjective`,
  `arithmeticFiniteArtin_continuous`).
- `arithmeticFiniteArtin_hasArithmeticArtinNormalization` (`FiniteArtinNormalization.lean`): it
  satisfies the Library's normalization `Langlands.Global.HasArithmeticArtinNormalization` (every
  uniformizer at a finite place unramified in `L` goes to an arithmetic Frobenius at every prime
  above, every local unit to `1`).
- `arithmeticFiniteArtin_finiteClassInclusion_eq_one_iff` and the unit criterion
  `isUnramifiedAt_of_arithmeticFiniteArtin_finiteClassInclusion_eq_one` (`FiniteArtinUnramified.lean`):
  local norms are the kernel at a place, and a place where the local units are killed is unramified.
- `geometricArtinMap K : IdeleClasses K →ₜ* Field.absoluteGaloisGroupAbelianization K` (`ArtinMap.lean`):
  the global Artin map onto the topological abelianization of `Gal(AlgebraicClosure K/K)`,
  surjective (`geometricArtinMap_surjective`) with kernel the connected component of the identity
  (`geometricArtinMap_ker`), restricting to the inverse of `arithmeticFiniteArtin` on every finite
  abelian extension (`arithmeticFiniteArtin_eq_inv_abelianRestriction`).
- `classField K H` (`ClassField.lean`) for an open subgroup `H` of `IdeleClasses K`: a finite abelian
  subextension of `AlgebraicClosure K` whose arithmetic Artin map has kernel `H`
  (`arithmeticFiniteArtin_classField_ker`), the only one (`classField_eq_iff`).
- `exists_unramified_extension_forall_isPrincipal` (`PrincipalIdeal.lean`): every number field has a
  finite extension `H : Type`, unramified at every finite place, in which every ideal of `𝓞 K`
  becomes principal (NYLL's Hilbert class field); the field `H` is in universe `0`.

From these, `Langlands.Global.finiteAbelianClassField`
(`Langlands/Global/Arithmetic/ClassFieldProof.lean`) proves the Library's
`FiniteAbelianClassFieldStatement`: finite abelian Artin reciprocity with uniqueness, finiteness of
the index of open subgroups of `IdeleClasses K`, existence and kernel rigidity of class fields, and
the realization of Hecke characters of finite order through the Artin map
(`finiteOrderHeckeArtinRealization`). The principal ideal theorem gives `H¹(G_S, 𝒪_Sˣ) ≅ Pic(𝒪_S)`
in the global Galois cohomology (`Langlands.GaloisCohomology.cohomologyOneSUnitsPicardEquiv`, see
[global Galois cohomology](../galois-cohomology/global.md)).

## What the Library proves itself

- The uniqueness of a normalized Artin map: `eq_of_hasArithmeticArtinNormalization`
  (`ArtinUniqueness.lean`) — two continuous homomorphisms `IdeleClasses K → Gal(L/K)` with the
  arithmetic normalization are equal; the file imports only the Library and Mathlib.
- `openSubgroup_finiteIndex` (`OpenSubgroupFiniteIndex.lean`): every open subgroup of the idèle class
  group has finite index; also without the copy.
- Local class field theory for `p`-adic fields on its own side (the cohomological construction of
  `Langlands/ClassFieldTheory/Local/`, the geometric symbol `FiniteArtinSystemExistence.geometricSymbol`,
  the invariant `localBrauerInvariant`), which `PadicComparison.lean` identifies with the copy's map.
  The local Galois cohomology takes its invariant from it.

## Conventions

- **Normalizations.** NYLL's maps are geometric (a uniformizer goes to the inverse of the arithmetic
  Frobenius). The Library names both: `geometricFiniteArtin`, `geometricArtinMap` geometric;
  `arithmeticFiniteArtin` (local and global) arithmetic, the geometric map of the inverse; the global
  normalization `HasArithmeticArtinNormalization` is arithmetic. The relation between the two global
  forms is `arithmeticFiniteArtin_eq_inv_abelianRestriction`.
- **Idèle classes** are Mathlib's (`Langlands.Global.IdeleClasses`); NYLL's group appears only in the
  bridge files.
- **Fields** are subfields of `AlgebraicClosure K` for the global statements; the local maps are stated
  for Mathlib's `IsNonarchimedeanLocalField`, in any characteristic.

## What is stated and not proved

Every statement that the bridge directories prove is proved without hypotheses; the two
`…Statement`s of `Langlands/ClassFieldTheory/Local/General/` have their proofs beside them.

## Why it is built this way

- NYLL's global class field theory is one development in its own notions from bottom to top and
  cannot be separated from its local theory; the copy stays whole, and what only it has — the idèlic
  Artin map with the existence theorem — enters the Library's vocabulary through a small directory of
  bridge theorems that prove the Library's existing statements and give the maps their names.
- The Library's own local class field theory, ramification theory and class formations stay the
  Library's theory; on `p`-adic fields the two local Artin maps are proved equal rather than one being
  replaced by the other.
- Every name says its normalization (`arithmetic…`, `geometric…`), because the Library's statements
  use both.

## Origin of the text

The copy is NYLL at commit `fe40c03df1b2b195053fdd63305571d97c73ce48` (`licenses/NYLL/LICENSE`,
`licenses/NYLL/NOTICE`); the bridge files are the Library's own text.
