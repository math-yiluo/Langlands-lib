# The roots of the repository and the import rule

The repository holds one library of its own, the Library under `Langlands/`, and beside it
copies of three outside Lean libraries, each in a root of its own: `Nyll/`,
`FontaineWintenberger/` (with the root file `FontaineWintenberger.lean`), and the two directories
`StacksCore/` and `StacksFrontier/` of one extract. `lakefile.toml` declares each of them as a
`lean_lib` of the package and requires Mathlib (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`).
Two more libraries of the package, `WeilConjectures` and `Weil`, have their sources in
`external/weil-conjectures/`: the Lean library weil-conjectures, whole and unchanged, as it is at commit
`a25955cde4f85f67bef3149a6efc3efe20c22132` of
https://github.com/formal-arithmetic-geometry/weil-conjectures. It is kept here so that nothing but
Mathlib and Mathlib's own dependencies has to be fetched to build what the repository holds.

This note says what each root is, under which rule the Library may import a copy, and how the
rule is checked. The parts of the Library that use the copies are described in their own notes:
class field theory through `Nyll/` in
[class field theory through the copies](../class-field-theory/through-the-copies.md), the
ramification theory that uses `FontaineWintenberger/` in
[conductors and ramification](../local-factors/conductors-and-ramification.md).

## The roots

| Root | What it is | Source | Licence entry |
| --- | --- | --- | --- |
| `Langlands/` | The Library: about 40,000 Lean files, each with a page (a Markdown file of the same name) beside it; namespace `Langlands` | itself | — |
| `Nyll/` | 1,095 Lean files with a page each: valued fields and local fields, ramification groups, the cohomology of cyclic groups and Kummer theory, local and global class field theory with idèles, the Artin map and the existence theorem, and what these need of scheme theory and of pro-C groups | NYLL, https://github.com/n-yamaguchi-0729/NYLL, commit `fe40c03df1b2b195053fdd63305571d97c73ce48` | `licenses/NYLL/LICENSE`, `licenses/NYLL/NOTICE` |
| `FontaineWintenberger/` and `FontaineWintenberger.lean` | 192 Lean files with a page each, in five parts (`FontaineWintenberger/APF/`, `FontaineWintenberger/FieldOfNorms/`, `FontaineWintenberger/LocalField/`, `FontaineWintenberger/Mathlib/`, `FontaineWintenberger/Ramification/`): arithmetically profinite extensions, the field of norms of an infinite APF extension and the isomorphism of absolute Galois groups, the upper ramification filtration of infinite extensions (Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*) | FontaineWintenberger, https://github.com/YijunYuan/FontaineWintenberger, commit `e835d58871d8d564901c0f13b685034cd202659e` | `licenses/FontaineWintenberger/` (`licenses/FontaineWintenberger/LICENSE`, `licenses/FontaineWintenberger/MANIFEST.tsv`, `licenses/FontaineWintenberger/RENAMES.tsv`, `licenses/FontaineWintenberger/REPAIRED.tsv`) |
| `StacksCore/`, `StacksFrontier/` | 609 Lean files (12 and 597) with a page each: an extract of the Stacks formalization, cut by declaration, holding what the reduced fibre theorem (Stacks Project, Tag 09IL) and the Nagata theorems (Tags 032W, 0334) need. The two directories are the two tiers of the source, under the source's own paths | AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b` | `licenses/Stacks/` (`licenses/Stacks/LICENSE`, `licenses/Stacks/STX-MANIFEST.tsv`, `licenses/Stacks/STX-RENAMES.tsv`) |
| `external/weil-conjectures/` | The Lean library weil-conjectures, whole and unchanged, without pages: the 26,795 Lean files under the root `WeilConjectures`, and `Weil/Definitions.lean`, which six of them import; the source keeps that file in its directory `Comparator/`, and it stands here at its module path. Compiled with the options of the library's own lakefile, which `lakefile.toml` repeats. No file of the Library or of a copy imports it at present. 186 of its files contain the word `sorry`, in a proof or in a comment; `Langlands/` and the four copies contain none in a proof | weil-conjectures, https://github.com/formal-arithmetic-geometry/weil-conjectures, commit `a25955cde4f85f67bef3149a6efc3efe20c22132` | `external/weil-conjectures/LICENSE` |

The origin of every file of `Nyll/` and `FontaineWintenberger/` is given at the end of its page,
under "Origin of the file": repository, commit, path and SHA-256 of the source file, and the
changes made in the copy. `licenses/FontaineWintenberger/MANIFEST.tsv` lists the SHA-256 of
every source file and of its copy. For the Stacks extract, the page of each file gives the repository, the commit, the source file
and what the extract leaves out or renames; `licenses/Stacks/STX-MANIFEST.tsv`
lists, file by file, every declaration of the source with its status in the extract (kept or
dropped), and `licenses/Stacks/STX-RENAMES.tsv` the renamed declarations with the rule of
renaming; the commit of the source is cited on the pages of the two bridge files (below).

A table or a script that this note or a note under `notes/reuse/` names is kept in the repository as a
Markdown file of that name with `.md` added (`licenses/Stacks/STX-MANIFEST.tsv.md`,
`notes/library/check_import_rule.py.md`), which holds the file in a code block.

The other entries of `licenses/` (`licenses/Anthropic-FLT/`, `licenses/ImperialCollegeLondon-FLT/`,
`licenses/RiemannHypothesis/`) are not roots: they cover text that was ported into `Langlands/` itself,
for instance under `Langlands/AnthropicFLT/`.

## A copy keeps its names and is not edited by hand

A copy keeps the module paths, the namespaces and the declaration names of its source. Its files
are not edited by hand and no new mathematics is written in them; new work on their subjects goes
into the Library's directories, in the Library's notions. The differences from the source are few
and each is recorded on the page of the file it concerns:

- **`Nyll/`.** 1,085 files are the source byte for byte. Eight files of
  `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/` replace an anonymous local instance
  `Fact p.1.Prime`, which Lean names from its type and which therefore clashed between modules, by
  the shared theorem `GlobalClassFieldTheory.Reciprocity.fact_prime_val` of
  `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/PrimesFact.lean`, a file that belongs to
  the copy and not to NYLL. In
  `Nyll/SchemeTheory/HomologicalAlgebra/HomologySequenceExactFunctor.lean` the theorem
  `CategoryTheory.ShortComplex.homologyπ_mapHomologyIso_hom` of the source is called
  `homologyπ_mapHomologyIso_hom_of_exact`, because weil-conjectures declares the source's name
  with other hypotheses and Lean refuses to import both.
- **`FontaineWintenberger/`.** Every file sets after its imports the two options that the source's
  lakefile sets (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`). The ten declarations of
  the namespace `ValuationSubring` about the lower ramification group carry the suffix Int
  (`ValuationSubring.lowerRamificationGroupInt` and its lemmas); the page of
  `FontaineWintenberger/Ramification/Lower/Basic.lean` gives as reason that the Library declared the
  same full names for lower groups with natural index, and the Library as it is declares none of
  them (its lower groups are `Langlands.Ramification.lowerGroup` and
  `Langlands.Ramification.lowerGroupInt`). The theorem
  `AlgEquiv.restrictNormal_restrictScalars` of the source is called
  `AlgEquiv.restrictNormal_restrictScalars_comm`, because another library declares the source's
  full name for a different statement (`licenses/FontaineWintenberger/RENAMES.tsv`). Three files differ from the source in proofs only, so as to compile on the Library's Mathlib,
  which is older than the source's (`licenses/FontaineWintenberger/REPAIRED.tsv`).
- **`StacksCore/`, `StacksFrontier/`.** The extract keeps, of each source file, only the
  declarations that `licenses/Stacks/STX-MANIFEST.tsv` marks as kept (5,718; 2,831 are dropped),
  which are what the reduced fibre theorem and the two Nagata theorems need, and no file of it
  imports `Mathlib` whole. A declaration whose full name is also declared by weil-conjectures,
  Mathlib or the Library keeps its namespace and gets the prefix "stacks" on its last component
  (for example the class `IsNagataRing` of the source is `StacksIsNagataRing`, because
  weil-conjectures declares `IsNagataRing`); the 18 renames are the rows of
  `licenses/Stacks/STX-RENAMES.tsv`, whose header states the rule.

**Why a copy stays a copy.** Each copy is, in its proofs, one development in its own notions
from bottom to top: NYLL's global class field theory rests on its own idèles, ramification
groups and class formations; the FontaineWintenberger copy is a single proof of the main
theorems of Wintenberger's paper, for a class of fields (complete discretely valued with perfect
residue field) that contains the Library's local fields and cannot be expressed in the Library's
notions without losing generality; the Stacks theorems are proved through hundreds of lemmas in
the Stacks vocabulary. Rewriting any of them on the Library's notions would be a rewrite of the
proofs, and would end the byte-for-byte state by which each file is compared with its source.
The copies are also files of Lean's module system (all of `FontaineWintenberger/`, `StacksCore/` and
`StacksFrontier/`, and 1,088 of the 1,095 files of `Nyll/`), which cannot import the classic
files of the Library. So what the Library takes from a copy enters as theorems: each is a proof,
in a bridge file, of a statement written in the Library's and Mathlib's notions.

## Bridges

A **bridge** is a file of the Library that imports a copy and states and proves, in the Library's
notions, what is taken from it. Other Library files import the bridge, not the copy. The
directories whose files may import a copy are:

| Copy | Bridge files |
| --- | --- |
| `Nyll/` | the files under `Langlands/ClassFieldTheory/`; those that import the copy now are `Langlands/ClassFieldTheory/Global/Artin/` (seven files), `Langlands/ClassFieldTheory/Local/Artin/` (three files) and `Langlands/ClassFieldTheory/Local/QuadraticNormIndex.lean`, besides two files of `Langlands/ClassFieldTheory/Local/General/` that import only the open zone |
| `FontaineWintenberger/` | `Langlands/LocalFactor/Ramification/Wintenberger/` (nine of its ten files import the copy) |
| `StacksCore/`, `StacksFrontier/` | `Langlands/AlgebraicGeometry/DvrAffineReducedFibre/` and `Langlands/CommutativeAlgebra/CompleteLocalNormalizationFinitenessProof.lean` |
| `WeilConjectures` | none |

The two Stacks bridges show the pattern. `Langlands.AlgebraicGeometry.DvrAffineReducedFibre.schemeReducedFibre`
(`Langlands/AlgebraicGeometry/DvrAffineReducedFibre/SchemeReducedFibreProof.lean`) proves the
Library's `SchemeReducedFibreStatement` (Tag 09IL) by the copy's theorem
`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback`;
`Langlands.CommutativeAlgebra.completeLocalNormalizationFiniteness`
(`Langlands/CommutativeAlgebra/CompleteLocalNormalizationFinitenessProof.lean`) proves
`CompleteLocalNormalizationFinitenessStatement` (for a Noetherian local ring `R` complete at its
maximal ideal, a domain `S` of finite type over `R` and a finite extension `L` of the fraction
field of `S`, the integral closure of `S` in `L` is a finite `S`-module) by the copy's
`StacksIsNagataRing.of_isPrecomplete_maximalIdeal` (Tag 032W) and `isNagataRing_tfae` (Tag 0334).
From these two, outside the bridge directories, `Langlands.AlgebraicGeometry.dvrAffineReducedFibre`
proves `DvrAffineReducedFibreStatement` (the affine reduced fibre theorem for a flat algebra of
finite type over a discrete valuation ring with smooth generic fibre) and
`Langlands.AlgebraicGeometry.dvrStableNormalization` proves `DvrStableNormalizationStatement`.

**The open zone of `Nyll/`.** Three directories of `Nyll/` are algebra on Mathlib's notions and
may be imported by any Library file: `Nyll/ValuedFieldTheory/Valuation/`,
`Nyll/ValuedFieldTheory/LocalField/` and `Nyll/ClassFieldTheory/LubinTate/FormalModule/` (the
modules `Nyll.ValuedFieldTheory.Valuation.…`, `Nyll.ValuedFieldTheory.LocalField.…`,
`Nyll.ClassFieldTheory.LubinTate.FormalModule.…`). Twelve Library files outside the bridge
directories import them, for instance `Langlands/CommutativeAlgebra/FiniteIntegralClosure.lean`,
`Langlands/GaloisCohomology/Local/Arithmetic/Units.lean` and
`Langlands/Geometry/FormalGroup/LubinTateStandardCoordinates.lean`.

**Direction.** No file of a copy imports the Library or weil-conjectures, and no copy imports
another, except that `StacksFrontier/` imports `StacksCore/`.

## weil-conjectures and `Langlands.MathlibBase`

weil-conjectures is kept unchanged, so its names are not the Library's to change. Three modules of Mathlib declare
names that weil-conjectures also declares, so a module with both in its import closure is
rejected by Lean. The module `Langlands.MathlibBase` (`Langlands/MathlibBase.lean`) imports every
module that Mathlib's umbrella file imports except these three, and the Library imports it where
it would import `Mathlib`; its page gives the table of the three modules. On the side of the
copies, the clashes with weil-conjectures are resolved by renaming in the copy, as above.

## The check

`notes/library/check_import_rule.py.md` holds a script that checks the rule over the import lines. Saved as
`check_import_rule.py`, it is run as

    python3 check_import_rule.py <root of the repository> [--list]

It reads the imports of every file under `Langlands/` and reports (1) the Library files that
import a copy directly, by copy and directory, (2) the imports of a copy that are neither from a
bridge directory nor of the open zone, (3) the files of a copy that import the Library. Its exit
status is 0 when (2) and (3) are empty, 1 otherwise; `--list` prints every direct import of a
copy.

On the Library as it is, the check finds 38 Library files that import a copy directly (27 import
`Nyll/`, 9 `FontaineWintenberger/`, 2 `StacksFrontier/`), no file of a copy that imports the
Library, and no import outside the bridge directories and the open zone, so that its exit status
is 0.
