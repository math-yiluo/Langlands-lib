STATUS: complete

# NYLL report: the copy joined to the Library, and `FiniteAbelianClassFieldStatement` proved

Steps 1 to 3 are done and `Langlands.Global.FiniteAbelianClassFieldStatement` is proved:
`Langlands.Global.finiteAbelianClassField` in `Langlands/Global/Arithmetic/ClassFieldProof.lean`,
with each of the five clauses as its own theorem. All 334 Library roots, the copy and the seven
new modules build from the committed tree; the copy imports together with weil-conjectures.

Commits on branch `work` (oldest first): Step 1 (`7863527d`), Step 2 (`4c8a01f9`), Step 3
(`76c3f5d0`), Step 4 in several commits ending with `928093fe`, then this report.

## 1. Edits to Library files, by kind

Every edit is a row of `NYLL-LIBRARY-EDITS.tsv` (file, kind, what): 47 rows, 44 paths.

| Kind | Lean files | Pages | What |
|---|---:|---:|---|
| tidying | 14 | 19 | Partially qualified names `NYLL.x` that referred to the old name space `Langlands.LocalClassField.NYLL` (now `…UniverseZero`), in 13 Lean files and their pages, rewritten to `UniverseZero.x` by `tools/fix_tidying_names.py`; relative page links into the moved directories (`ClassField/Global/`, `ClassFieldTheory/Local/NYLL/`) re-pointed by the same script; one prose mention of the old directory in `FiniteReciprocityProof.md` by hand. |
| toolchain | 7 | 0 | Files of the latest publication that did not compile on Lean 4.35 / Mathlib `56a0058`. Six are an option scoped with `in` to one declaration: `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` / `maxRecDepth` in `TorusFibreMaximality`, `StandardParabolicClassificationProof`, `AffineWeilUnitGalois`, `WeilRestrictionNormOne` (bound raised from 800000 to 3200000), `WeilRestrictionNormBaseChange`, `RelativeFiniteBrauerProfiles`. One is a Mathlib API change: `NumberField.LiesOver.completionMap_coe` now takes the places `v w` explicitly (`NumberFieldWeilCocycleTransfer`). No statement changed. |
| old-adaptation | 4 | 2 | `ReductionLimit`, `HarrisLatticeLimit`, `LubinTateStandardIntertwiner`, `LubinTateStandardCoordinates` and the pages of the first two, re-pointed at the copy by `tools/remove_old_adaptation.py`; then `Langlands/NYLL/` (the last 2 modules and 2 pages) deleted by the same script. |

Note on the toolchain kind: five of the seven files are listed as "compiled before" in
`NYLL-LIBRARY-FILES.tsv` (all but `AffineWeilUnitGalois` and `RelativeFiniteBrauerProfiles`);
here, four of them failed with elaboration timeouts after their dependencies were rebuilt, and
one (`NumberFieldWeilCocycleTransfer`) on the changed Mathlib signature.

## 2. Files set aside

None. Every root builds.

## 3. Renames in the copy

One, recorded in `NYLL-RENAMES.tsv` and in the page of the file:

| Old full name | New full name | File | Clashed with |
|---|---|---|---|
| `CategoryTheory.ShortComplex.homologyπ_mapHomologyIso_hom` | `CategoryTheory.ShortComplex.homologyπ_mapHomologyIso_hom_of_exact` | `Nyll/SchemeTheory/HomologicalAlgebra/HomologySequenceExactFunctor.lean` (declaration line 41, its one use line 155) | the lemma of the same name in weil-conjectures, `WeilConjectures/Mathlib/Algebra/Homology/SingleHomology.lean` (hypotheses `[F.PreservesHomology]`) |

The page of the file now has a section "Renamed declarations" and gives the SHA-256 of the
source and of the file as it is. `NYLL-MANIFEST.tsv` is unchanged, as the record of the source.
That Lean refuses the pair was taken from the brief and not re-checked before the rename.

## 4. The two import tests

1. **The copy beside weil-conjectures.** After the one rename, one file importing the seven
   roots of the copy and `WeilConjectures` is **accepted**; no further clash. It took
   1 min 24 s cold and 5–50 s later. `tools/check_copy_with_weil.sh .` recomputes the roots
   (the modules of the copy that no module of the copy imports: still the seven of the design
   note, 1.1) and reruns the test.
2. **Root names.** One file imports the copy's seven roots and the Library modules
   `ClassFieldTheory.Global.CyclicHasseNormStatement`, `IdeleClassNormGaloisProductStatement`,
   `IntegralIdeleUnitExact` and `Global.Arithmetic.ClassFieldStatement`, and elaborates their
   texts again verbatim under `open NumberField` and `open Langlands.Global.AdelicFunctoriality`:
   `IdeleGroup (𝓞 E) E`, `IdeleClassGroup (𝓞 L) L`, `ideleClassNorm (K := K) (L := L) x`,
   `IdeleGroup.unitEmbedding (𝓞 F) F a`, a full tactic proof. **Everything elaborates**; the two
   definitions are `rfl`-equal to the originals; the file takes about 9 s. The overloaded names
   resolve by arity and type. The two lines of (G1) of the design note also elaborate. The only
   ambiguity found does not involve the copy: `FinitePlace` under both `open NumberField` and
   `open Langlands.Global` is ambiguous between `Langlands.Global.FinitePlace` and Mathlib's
   `NumberField.FinitePlace`; the bridges write `Langlands.Global.FinitePlace`.

A further test, not asked for: importing `Langlands.Global.Arithmetic.ClassFieldProof` together
with `WeilConjectures` is **refused**, but not because of the copy. weil-conjectures'
`WeilConjectures.FromJoel.CategoryTheory.GuitartExact.Basic` declares
`CategoryTheory.TwoSquare.GuitartExact.prod`, which this Mathlib already has in
`Mathlib.CategoryTheory.GuitartExact.Prod`; that Mathlib module enters through the Library's
existing `Langlands.Global.IdeleClosedSubgroupDensity` (used by the uniqueness bridge). Importing
`Mathlib.CategoryTheory.GuitartExact.Prod` alone with `WeilConjectures` is refused the same way.
See section 10.

## 5. Scripts under `tools/`

Each takes the root of a tree as its argument; each is idempotent (a second run changes nothing).

- `fix_tidying_names.py ROOT [--dry-run]`: repairs what the tidying of names left wrong. It
  collects the first components of the names declared in `Langlands.LocalClassField.UniverseZero`
  and rewrites the tokens `NYLL.x` with such an `x` to `UniverseZero.x` in Lean files and pages
  (refusing names that the old adaptation `Langlands.NYLL` also declares); and it re-points
  relative page links whose target moved (`ClassField/Global/` → `ClassFieldTheory/Global/`,
  `ClassFieldTheory/Local/NYLL/X` → the subdirectory where `X` now is). Prints one line per
  changed file.
- `remove_old_adaptation.py ROOT [--dry-run]`: points the last users of `Langlands/NYLL/` at the
  copy (import lines mapped to the copy's source modules; `open Langlands.NYLL.LubinTate.SameUniformizer`
  → `open LubinTate.SameUniformizer`; `NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite R M I`
  → the copy's `ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite (R := R) (M := M) I`,
  keeping line breaks; the same names in pages), then checks that no file outside
  `Langlands/NYLL/` imports, opens or names the adaptation, and only then deletes the directory.
  If anything is left it lists it and deletes nothing.
- `check_copy_with_weil.sh ROOT [WEIL_LIB]`: recomputes the roots of the copy, imports them with
  `WeilConjectures` in one file without Lake, and reports `ACCEPTED` or `REFUSED`.

## 6. New modules

Name space `Langlands.ClassFieldTheory.Global.Artin` for the bridges, `Langlands.Global` for the
proof. Every file has its page (664 lines of pages in all).

| Module | Lines | Imports of the copy | Content |
|---|---:|---|---|
| `Langlands/ClassFieldTheory/Global/Artin/IdeleClassComparison` | 58 | yes | (G1) `nyllIdeleClassEquiv : _root_.IdeleClassGroup K ≃ₜ* IdeleClasses K`, the one-place compatibility |
| `…/Artin/FiniteArtin` | 116 | yes | (G2) `arithmeticFiniteArtin K L : IdeleClasses K →* (L ≃ₐ[K] L)`, surjective, continuous (Krull and `⊥`), kernel = image of `(_root_.ideleClassNorm K L).range`; `arithmeticFiniteArtinBot` |
| `…/Artin/FiniteArtinNormalization` | 157 | yes | (G3) values on units (two forms) and at every uniformizer (`arithFrobAt`); `HasArithmeticArtinNormalization (arithmeticFiniteArtin K L)` |
| `…/Artin/ArtinUniqueness` | 193 | **no** (closure has no `Nyll` module) | (G4) density lemma, finiteness of ramified places, uniqueness of Frobenius, uniqueness of a normalized map |
| `…/Artin/OpenSubgroupFiniteIndex` | 120 | **no** (closure has no `Nyll` module) | clause 2: open subgroups of `IdeleClasses K` have finite index |
| `…/Artin/ClassField` | 229 | yes | (G5) norm groups and isomorphisms, rigidity, `classField K H : IntermediateField K (AlgebraicClosure K)`, its kernel, `classField_eq_iff` |
| `Langlands/Global/Arithmetic/ClassFieldProof` | 149 | no (only the bridges) | the five clauses and `finiteAbelianClassField` |

Total 1,022 lines of Lean. Outside these, the only Library files that import the copy's
`ClassFieldTheory` are the two Lubin–Tate files, which import the open zone
`LubinTate/FormalModule` (design note 5.2).

## 7. The final theorems

In `Langlands/Global/Arithmetic/ClassFieldProof.lean`, name space `Langlands.Global`:

```lean
theorem finiteAbelianArtinReciprocity : FiniteAbelianArtinReciprocityStatement.{u, v}
theorem openIdeleClassSubgroupFiniteIndex : OpenIdeleClassSubgroupFiniteIndexStatement.{u}
theorem finiteAbelianClassFieldExistence : FiniteAbelianClassFieldExistenceStatement.{u}
theorem finiteAbelianClassFieldKernelRigidity : FiniteAbelianClassFieldKernelRigidityStatement.{u}
theorem finiteOrderHeckeArtinRealization : FiniteOrderHeckeArtinRealizationStatement.{u}

theorem finiteAbelianClassField : FiniteAbelianClassFieldStatement.{u, v} :=
  ⟨finiteAbelianArtinReciprocity, openIdeleClassSubgroupFiniteIndex,
    finiteAbelianClassFieldExistence, finiteAbelianClassFieldKernelRigidity,
    finiteOrderHeckeArtinRealization⟩
```

The statements, as published in `Langlands/Global/Arithmetic/ClassFieldStatement.lean` (not
changed):

```lean
def HasArithmeticArtinNormalization
    {K : Type u} {L : Type v} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (ρ : IdeleClasses K →* (L ≃ₐ[K] L)) : Prop :=
  ∀ (v : FinitePlace K) (w : FinitePlace L),
    w.asIdeal.LiesOver v.asIdeal →
    Algebra.IsUnramifiedAt (RingOfIntegers K) w.asIdeal →
    ∀ π : (FiniteCompletion K v)ˣ,
      Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
      (RingOfIntegers.mapAlgHom
        (ρ (finiteClassInclusion K v π))).IsArithFrobAt w.asIdeal

def FiniteAbelianArtinReciprocityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) →
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    ∃! ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L),
      Function.Surjective ρ ∧ HasArithmeticArtinNormalization ρ.toMonoidHom

def OpenIdeleClassSubgroupFiniteIndexStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (H : OpenSubgroup (IdeleClasses K)), H.toSubgroup.FiniteIndex

def FiniteAbelianClassFieldExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (H : OpenSubgroup (IdeleClasses K)), H.toSubgroup.FiniteIndex →
    ∃ (L : IntermediateField K (AlgebraicClosure K))
      (hfin : FiniteDimensional K L),
      letI := hfin
      letI := NumberField.of_module_finite K L
      IsGalois K L ∧
      (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧
      (letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
       ∃ ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L),
         Function.Surjective ρ ∧
         HasArithmeticArtinNormalization ρ.toMonoidHom ∧
         ρ.toMonoidHom.ker = H.toSubgroup)

def FiniteAbelianClassFieldKernelRigidityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K E],
    letI := NumberField.of_module_finite K L
    letI := NumberField.of_module_finite K E
    (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) →
    (∀ σ τ : E ≃ₐ[K] E, σ * τ = τ * σ) →
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    letI : TopologicalSpace (E ≃ₐ[K] E) := ⊥
    ∀ (ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L))
      (τ : IdeleClasses K →ₜ* (E ≃ₐ[K] E)),
      Function.Surjective ρ → Function.Surjective τ →
      HasArithmeticArtinNormalization ρ.toMonoidHom →
      HasArithmeticArtinNormalization τ.toMonoidHom →
      ρ.toMonoidHom.ker = τ.toMonoidHom.ker → L = E

def FiniteOrderHeckeArtinRealizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (χ : HeckeCharacter K), χ.HasFiniteOrder →
    ∃ (L : IntermediateField K (AlgebraicClosure K))
      (hfin : FiniteDimensional K L),
      letI := hfin
      letI := NumberField.of_module_finite K L
      IsGalois K L ∧
      (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧
      (letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
       ∃ (ρ : IdeleClasses K →ₜ* (L ≃ₐ[K] L))
         (θ : (L ≃ₐ[K] L) →ₜ* ℂˣ),
         Function.Surjective ρ ∧ Function.Injective θ ∧
         HasArithmeticArtinNormalization ρ.toMonoidHom ∧
         ∀ x, θ (ρ x) = χ x)

def FiniteAbelianClassFieldStatement : Prop :=
  FiniteAbelianArtinReciprocityStatement.{u,v} ∧
  OpenIdeleClassSubgroupFiniteIndexStatement.{u} ∧
  FiniteAbelianClassFieldExistenceStatement.{u} ∧
  FiniteAbelianClassFieldKernelRigidityStatement.{u} ∧
  FiniteOrderHeckeArtinRealizationStatement.{u}
```

`#print axioms` (from a file importing `Langlands.Global.Arithmetic.ClassFieldProof`):

```
'Langlands.Global.finiteAbelianClassField' depends on axioms: [propext, Classical.choice, Quot.sound]
Langlands.Global.finiteAbelianClassField : Langlands.Global.FiniteAbelianClassFieldStatement
```

The same holds for `arithmeticFiniteArtin_hasArithmeticArtinNormalization` and
`openSubgroup_finiteIndex`, printed separately.

How the clauses come out: reciprocity is `arithmeticFiniteArtinBot K L` (surjective, normalized)
and `eq_of_hasArithmeticArtinNormalization` for uniqueness; finite index is
`openSubgroup_finiteIndex`; existence is `classField K H` with kernel `H`; rigidity is uniqueness
plus `eq_of_arithmeticFiniteArtin_ker_eq`; for a Hecke character of finite order the kernel is
open (its values are roots of unity) and the character factors injectively through the Artin
map of the class field of its kernel.

## 8. Build times (12 cores, `taskset -c 12-23`)

| Build | Time |
|---|---|
| `lake build Nyll`, before the rename (up to date) | 4 s |
| Roots, first build after the tidying (15 first-level failures) | 39 min 30 s |
| Roots, second build (2 new failures downstream) | 7 min 12 s |
| Roots, third build (only the step-3 files fail) | 51 s |
| `lake build Nyll` after the rename (514 modules above the renamed file and more) | 32 min 11 s |
| Roots after step 3 | 31 s |
| New modules, each (`lake build`) | 4–40 s; `ClassFieldProof` 33 s |
| Closing check from the committed tree: `lake build Nyll` / roots + new modules | 3 s / 6 s (up to date, 5,299 / 19,891 jobs) |
| Import of the copy's roots with `WeilConjectures` | 1 min 24 s cold, 5–50 s warm |

## 9. Deviations from the design note

1. **Names.** The finite map is `arithmeticFiniteArtin` (design note: `finiteArtin`) so that the
   normalization is read off the name, as the brief asks; `arithmeticFiniteArtinBot` is the same
   map as a continuous homomorphism for `⊥`. The density lemma is
   `ideleClass_hom_ext_of_uniformizers` (Lean naming) and is stated for any group with the
   discrete topology, not only a commutative one.
2. **Directory and name space.** `Langlands/ClassFieldTheory/Global/Artin/`, name space
   `Langlands.ClassFieldTheory.Global.Artin` (decided since the note, as the brief says).
3. **Construction of the class field (G5).** `classField K H` is the image of NYLL's class field
   `closedFiniteIndexClassField` (a field in universe 0 with norm group the corresponding closed
   subgroup) under a `K`-embedding into `AlgebraicClosure K` (`IsAlgClosed.lift`), not the double
   `IntermediateField.lift` of `infiniteAbelianClassFieldCorrespondence`. Reason: fewer steps.
   The choice of embedding does not leak: the extension is normal, so all embeddings have the
   same image, and `classField_eq_iff` characterizes `classField K H` intrinsically. The note's
   `maximalAbelianExtension` inside `AlgebraicClosure K` is therefore not defined.
4. **Rigidity (clause 4)** uses NYLL's maximal abelian extension: the norm group determines a
   finite abelian extension up to isomorphism (`nonempty_algEquiv_of_ideleClassNorm_range_eq`,
   via `finiteAbelianExtensionInMaximalAbelianExtension` and
   `maximalAbelianGlobalArtin_comap_fixingSubgroup`), and isomorphic normal subfields of
   `AlgebraicClosure K` are equal. The audit's compositum argument is not used.
5. **The unit statement of (G3)** has NYLL's hypothesis `a ∈ (v.adicCompletionIntegers K).units`;
   a second form with `Valued.v (a : FiniteCompletion K v) = 1` is added
   (`arithmeticFiniteArtin_finiteClassInclusion_of_valuation_eq_one`).
6. **A fourth user of the old adaptation.** Besides the three files named in the brief,
   `Cohomology/DivisibleSystem/HarrisLatticeLimit.lean` calls the adaptation's
   `isAdicComplete_of_moduleFinite` twice (it reaches it through its import of
   `ReductionLimit`); it is re-pointed in the same way, as kind `old-adaptation`.
7. **Manifest.** Design note 5.1 has the manifest record the renamed file; following rule 4.2 of
   the brief the rename is recorded in `NYLL-RENAMES.tsv` and in the page, and the manifest stays
   the record of the source.
8. Clause 2 and (G4) are from the Library alone, as the note asks (B2). (Clause 2 was first proved
   through the copy's ray class groups and then replaced.)

## 10. Suggestions for the Library

1. **weil-conjectures against Mathlib.** Any Library module whose closure contains
   `Mathlib.CategoryTheory.GuitartExact.Prod` cannot be imported together with `WeilConjectures`
   (`CategoryTheory.TwoSquare.GuitartExact.prod` is declared by both). The Library's
   `Langlands.Global.IdeleClosedSubgroupDensity` is such a module, so the proof of
   `FiniteAbelianClassFieldStatement` cannot today be imported with weil-conjectures. Since
   weil-conjectures cannot be changed, either the Library's dependency on that Mathlib module has
   to be cut below `IdeleClosedSubgroupDensity`, or weil-conjectures updated. This is a clash with
   Mathlib, not with the copy.
2. **Pages that still speak of the old adaptation** (stale before this work, not edited here
   because rule 4.1 does not cover them): `ClassFieldTheory/Local/UniverseZero/UniverseZeroModel.md`
   (line 151, "pieces of it are in the Library under `Langlands.NYLL`"),
   `ClassFieldTheory/Local/General/SuppliedValuationSignProof.md` and `SuppliedUnramifiedProof.md`
   (names `Langlands.NYLL.LocalFieldTheory…`), `CommutativeAlgebra/AdicCompleteness.md`, and the
   remarks "imports no module under `Langlands/NYLL/`" in `TypeZero*Proof.md` and
   `FiniteReciprocityProof.md`.
3. `finite_setOf_ramificationIdx_ne_one` (`ClassFieldTheory/Global/IdeleLocalSupport.lean`) is
   stated for two fields in one universe; `Artin.finite_setOf_not_isUnramifiedAt` is the
   two-universe form and could replace it.
4. The page `ClassFieldStatement.md` could point to `ClassFieldProof`; the first premise of
   `FiniteHeckeAvatarLiftStatement` (`FiniteAbelianClassFieldExistenceStatement`) is now proved by
   `finiteAbelianClassFieldExistence`.
5. The six scoped heartbeat/recursion options of section 1 are stopgaps; the slow instance
   searches (`map_zero`/`map_sum` on equivalences into `characterLattice`) deserve a look.
6. `IsMulCommutative (IdeleClasses K)` is not found by instance search; the bridges supply it with
   `IsMulCommutative.of_comm`.
7. The next bridge for the consumers is the design note's (G6): NYLL's geometric
   `mathlibGlobalArtin` as a named map on `IdeleClasses K` with
   `L.abelianRestriction (artinMap K x) = (arithmeticFiniteArtin K L x)⁻¹`; it is what
   `FiniteGeometricArtinLifting` needs.

## 11. What was not done

- (G6) the profinite (geometric) Artin map, (B6) the unit criterion
  `FiniteArtinUnramifiedCriterionProof`, and (G7) the comparison of the two idèle norms: not
  required by the brief's step 4 and not written.
- The local bridges of design note 5.3 and 5.4, the folding of the wrapper files
  `CommutativeAlgebra/FiniteIntegralClosure.lean` and `AdicCompleteness.lean` (B8), and the atlas,
  wiki and licence texts (A5): outside this port and this workspace.
- The clash of the original theorem name with weil-conjectures was not reproduced before the
  rename (section 3).
