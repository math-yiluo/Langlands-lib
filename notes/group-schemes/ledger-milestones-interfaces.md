# Group-scheme ledger: milestones and algebraic interfaces

Author: Worker 3483, 10 November 2026, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). This note is the index of that
program's source-to-declaration ledger. The eight family ledgers listed below cover the
thematic families. This note records:

- the evidence for the contract's first milestone (`GL_n`, and the non-split torus
  `Res_{ℂ/ℝ} 𝔾_m` with finite separable Weil restriction);
- the evidence for the field layer that follows it (the rational structure theorems and the
  noncommutative non-split unitary example `U(1,1)`);
- the algebraic interfaces that the contract asks the program to export;
- the status changes since the family ledgers' commits, and the remaining limitations.

It describes Library commit `86ea837f8bbc2362833af96e434e544dd1a892bd` and environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. "Field group" means a group scheme over `Spec k` for
a field `k : Type u`.

**Names and modules.** Each table is written in a namespace `N`, which is
`Langlands.GroupScheme` unless the section states another one. A Lean name `X` in a table
denotes the declaration that Lean's name resolution finds for `X` inside `namespace N`: `N.X`
if it exists, otherwise `X` in the nearest enclosing namespace of `N` that has it, and finally
the root name `X` (this is how Mathlib names such as `CommRingCat.of` or `AlgEquiv.refl` are
meant). A projection such as `GeneralLinear.reductiveStatement.1` is the first component of the
theorem so resolved. Mathematical notation such as `GL_n`, `X^*(T_E)` or `det(Ad on Lie U)` is
also set in code font; it is not a Lean name. Module paths are relative to `Langlands/GroupScheme/` unless
they start with `Langlands/` or the section states another base directory. The section "How
the names were checked" describes the mechanical check of these conventions.

## The family ledgers

Each family ledger describes the Library commit shown here. The section "Status changes
since the family ledgers" lists every row whose status differs at `86ea837f`.

| Family | Ledger note | Commit described |
| --- | --- | --- |
| 1. Group-scheme and affine foundations | [ledger-family-1-foundations.md](ledger-family-1-foundations.md) | `f2c5495` |
| 2. Tori and multiplicative type | [ledger-family-2-tori.md](ledger-family-2-tori.md) | `e449cde` |
| 3. Unipotent structure and geometric reductivity | [ledger-family-3-unipotent-reductive.md](ledger-family-3-unipotent-reductive.md) | `f2c5495` |
| 4. Absolute structure over fields | [ledger-family-4-absolute.md](ledger-family-4-absolute.md) | `e449cde` |
| 5. Rational structure | [ledger-family-5-rational.md](ledger-family-5-rational.md) | `f2c5495` |
| 6. Galois and central structure | [ledger-family-6-galois-central.md](ledger-family-6-galois-central.md) | `e748734` |
| 7. Split realization and classification | [ledger-family-7-split-classification.md](ledger-family-7-split-classification.md) | `18a1f10` |
| 8. Relative structure over general bases | [ledger-family-8-relative.md](ledger-family-8-relative.md) | `f2c5495` |

A row reference such as "fam5 D7" means row D7 of the family-5 ledger.

## Status codes and evidence

This note uses its own codes. They are defined here and do not depend on any other note.

- **D (definition or internal result).** A published construction, or a published theorem
  that is not a proposition declaration (it has binders and no `…Statement` names it). The
  row lists its hypotheses. The evidence is the declaration and its module.
- **P (published proof).** The Library contains a theorem whose type is exactly the named
  proposition declaration `S`. The evidence is that theorem and its module.
- **I (instance).** No proposition declaration states the assertion. A published theorem with
  binders, applied to published data, gives a term whose type is the assertion. The row gives
  that term.
- **C (composite, not published).** A proposition declaration `S` states the assertion and no
  published theorem has type `S`. A term built only from published theorems has type `S`. The
  composite is not an accepted artifact; the row names the owner task if one exists.
- **O (open).** A proposition declaration states the assertion, and no published proof and no
  composite from published results is known. A staged candidate or a private draft in an owner
  task does not change this status.
- **M (missing).** No Lean declaration states the assertion.

Every P row, every I term and every C term below was type-checked by the author in a private
module (`example : S := proof`, or the displayed term) in the environment above, at Library
commit `86ea837f`. The last run of that module, record `d755aadb-1a98-4db2-a9e1-d57dcdc15a77`,
had no errors or warnings. Its 64 `#print axioms` lines show only `propext`,
`Classical.choice` and `Quot.sound`. This private check is not public evidence; the public
evidence of a P row is the published theorem itself. The existence and the module of every
Lean name in this note were checked separately, as described in the last section.

"Accepted" and "published" refer only to artifacts that passed independent review. Staged
candidates and private drafts are never called accepted.

Source locators use these registered sources, cited by source id:

- `milne-2017-algebraic-groups`: J. S. Milne, *Algebraic Groups* (2017). PDF page = printed
  page + 16.
- `milne-2022-algebraic-groups`: the 2022 corrected reprint. PDF page = printed page + 11.
- `conrad-2014-reductive-group-schemes`: B. Conrad, *Reductive group schemes* (2014). Printed
  page = PDF page.
- `conrad-gabber-prasad-2015-pseudo-reductive`: Conrad, Gabber and Prasad, *Pseudo-reductive
  groups*, 2nd edition (2015). PDF page = printed page + 26.
- `kaletha-prasad-2023-bruhat-tits-new-approach`: Kaletha and Prasad, *Bruhat–Tits theory: a
  new approach* (2023). PDF page = printed page + 31.
- `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: the Clay Mathematics Proceedings
  volume 4 (2005), containing Milne's *Introduction to Shimura varieties*. PDF page = printed
  page + 12.
- `mumford-fogarty-kirwan-1994-git-3rd`: Mumford, Fogarty and Kirwan, *Geometric invariant
  theory*, 3rd edition (1994). PDF page = printed page + 12.
- `borel-tits-1965-groupes-reductifs`: Borel and Tits, *Groupes réductifs* (1965).

## Milestone 1(a): `GL_n`, its dynamic subgroups and base change

In this section `N = Langlands.GroupScheme.GeneralLinear`; so `blockLimitHom` means
`Langlands.GroupScheme.GeneralLinear.blockLimitHom`, while `dynamicGeometricUnipotentRadical`,
which has no `GeneralLinear` version, means `Langlands.GroupScheme.dynamicGeometricUnipotentRadical`.

The construction is `GeneralLinear.groupScheme n R` (`GeneralLinear`), the
matrix-coordinate group scheme over `Spec R` for every `R : CommRingCat.{u}` and every finite
type `n : Type` with decidable equality. In universe `0` this includes `R = ℤ`, and every
`GL_n` over a ring in universe `0` is a base change of it by the row on base change. No
general integral-model theory is used. `GeneralLinear.pointsEquiv n R T` is a group
isomorphism between the points `T ⟶ GL_n` on a test scheme `T` over `Spec R` and the
invertible `n × n` matrices over `Γ(T, ⊤)`.

The dynamic subgroups are taken for the diagonal cocharacter `GeneralLinear.diagonalCocharacter`
(`Dynamic/GeneralLinear`) given by a weight function `e : n → ℤ`. The block parabolic, block
Levi and block unipotent subgroups are the closed subgroups of matrices of the block shape
determined by `e`.

| Assertion | Lean declaration (module) | Status and evidence |
| --- | --- | --- |
| `GL_n` is smooth over every base ring | `GeneralLinear.SmoothStatement` (`GeneralLinearSmoothStatement`) | P: `GeneralLinear.smoothStatement` (`GeneralLinearSmoothProof`). fam1 B6 |
| `GL_n` over every field is connected reductive (Milne 2017, Lemma 19.16 and Example 19.19, printed p.401, PDF 417), and `GL_n` over every ring is reductive in Conrad's sense (Conrad 2014, Definition 3.1.1, p.81) | `GeneralLinear.ReductiveStatement` = `IsConnectedReductiveStatement ∧ IsReductiveStatement` (`Reductive/GeneralLinearStatement`) | P: `GeneralLinear.reductiveStatement` (`Reductive/GeneralLinearProof`). The two components are C: `reductiveStatement.1` and `reductiveStatement.2`; owner Task 5476 (`a54e38fe-1a3a-45d4-b553-05208da37fcb`) |
| Geometric reductivity in Haboush's sense: over an algebraically closed field `k`, for every matrix representation `ρ` of `GL_n` on `k^m` and every nonzero fixed vector `v`, there is a homogeneous invariant polynomial `F` of positive degree with `F(v) ≠ 0` (Mumford–Fogarty–Kirwan, appendix to Chapter 1, §A, definition (iii), printed p.191, PDF 203; Theorem A.1.0, printed p.192, PDF 204) | the conclusion of `ReductiveGeometricReductivityStatement` (`Reductive/GeometricReductivityStatement`, fam3 F9) for `GeneralLinear.groupScheme n (CommRingCat.of k)` | I: `reductiveGeometricReductivity k _ (GeneralLinear.reductiveStatement.1 k n).isPseudoReductive m ρ v hv hfix`, with `reductiveGeometricReductivity` from `Reductive/GeometricReductivityProof` |
| Dynamic subgroups: `P(λ)`, `Z(λ)`, `U(λ)` of the diagonal cocharacter and of block shapes, described by matrix entries on points over every test `T`; the limit map on points; the Levi decomposition of `P(λ)` on points (CGP Example 2.1.1, pp.45–47, PDF 71–73; Lemma 2.1.5, pp.50–51; Proposition 2.1.8(2), p.53) | `GeneralLinear.DynamicStatement` (`Dynamic/GeneralLinearStatement`), the conjunction of `DiagonalCocharacterDynamicStatement`, `BlockShapeDynamicStatement`, `DiagonalCocharacterLimitStatement`, `DiagonalCocharacterLeviDecompositionStatement`, `BlockShapeLimitStatement` | P: `GeneralLinear.dynamicStatement` (`Dynamic/GeneralLinearProof`). fam4 C12, fam8 F2. The five components are C, in that order: `dynamicStatement.1`, `dynamicStatement.2.1`, `dynamicStatement.2.2.1`, `dynamicStatement.2.2.2.1`, `dynamicStatement.2.2.2.2`; owner Task 5476 (`a54e38fe-1a3a-45d4-b553-05208da37fcb`) |
| Inclusions: `P(λ)`, `Z(λ)`, `U(λ)` are represented by the closed subgroups `blockParabolicHom`, `blockLeviHom`, `blockUnipotentHom` | `GeneralLinear.isRepresentedBy_parabolic_diagonalCocharacter`, `isRepresentedBy_centralizer_diagonalCocharacter`, `isRepresentedBy_unipotent_diagonalCocharacter`, `exists_isClosedSubgroup_isRepresentedBy_diagonalCocharacter` (`Dynamic/GeneralLinearRepresentability`) | D, over every `R : CommRingCat` and every `e : n → ℤ` |
| Limit map, Levi section, kernel and semidirect product: `blockLimitHom : P → Z` agrees with the dynamic limit on every test (`pointsEquiv_blockLimitHom`); `blockLeviToParabolic` is a section of it; `blockUnipotentIsoKernel : U ≅ ker(blockLimitHom)`; `blockMultiplicationIso : U ×_R Z ≅ P` is matrix multiplication on points | `GeneralLinear.blockLimitHom`, `blockLeviToParabolic`, `blockLeviToParabolic_comp_blockLimitHom`, `blockUnipotentIsoKernel`, `blockUnipotentIsoKernel_hom_comp`, `blockMultiplicationIso` (`Dynamic/GeneralLinearDecomposition`) | D, over every `R : CommRingCat`. These instantiate the general maps of `Dynamic/SchemeDecomposition` (fam8 F2) |
| Over a field, the block unipotent subgroup is the geometric unipotent radical of the block parabolic | `IsGeometricUnipotentRadical ((GeneralLinear.blockUnipotentIsoKernel n (CommRingCat.of k) e).hom ≫ kernelι (GeneralLinear.blockLimitHom n (CommRingCat.of k) e))` | I: `dynamicGeometricUnipotentRadical` (proof of `DynamicGeometricUnipotentRadicalStatement`, `Dynamic/GeometricUnipotentRadicalProof`, fam4 C6) applied to `GeneralLinear.reductiveStatement.1 k n` and the parabolic and unipotent representability theorems above |
| Base change: `(GL_{n,R})_{R'} ≅ GL_{n,R'}` for every morphism `b : Spec R' ⟶ Spec R`, and the formation of `P(λ)`, `Z(λ)`, `U(λ)` and of the block subgroups commutes with it (Conrad 2014, paragraph after Example 4.1.9, p.114) | `GeneralLinear.baseChangeIso n b` (`Reductive/GeneralLinear`); `GeneralLinear.parabolic_diagonalCocharacter_baseChange`, `centralizer_diagonalCocharacter_baseChange`, `unipotent_diagonalCocharacter_baseChange`, `blockParabolic_baseChange`, `blockLevi_baseChange`, `blockUnipotent_baseChange` (`Dynamic/GeneralLinearBaseChange`) | D. Each theorem says that the object over `R` base-changes to the object over `R'` pulled back along `(baseChangeIso n b).hom` |
| Borel subgroups (Milne 2017, Example 17.7, p.354) | `GeneralLinearBorelStatement` (`Absolute/BorelStatement`) | P: `generalLinearBorel` (`Absolute/GeneralLinearBorelProof`). fam4 A14 |
| Root datum and Weyl group (Milne 2017, 17.88, p.380; 21.6, p.426; 21.40, p.436) | `GeneralLinearRootDatumStatement` (`Reductive/RootDatumStatement`) | P: `generalLinearRootDatum` (`Reductive/GeneralLinearRootDatumProof`). fam4 B12 |
| Rational structure and standard parabolics of `GL_n` | `GeneralLinearRationalStatement` (`Rational/GeneralLinearStatement`), `GeneralLinearStandardParabolicStatement` (`Rational/GeneralLinearStandardParabolicStatement`) | P: `generalLinearRationalStatement` (`Rational/GeneralLinearProof`), `generalLinearStandardParabolic` (`Rational/GeneralLinearStandardParabolicProof`). fam5 E5 |
| Rational characters of `GL_n` | `GeneralLinearCharactersStatement` (`Rational/CharactersStatement`) | P: `generalLinearCharacters` (`Rational/CharactersProof`). fam5 E5 |

## Milestone 1(b): the non-split torus `Res_{ℂ/ℝ} 𝔾_m` and finite separable Weil restriction

The Deligne torus `𝕊` is `Langlands.Shimura.DeligneTorus.groupScheme` (`Langlands/Shimura/Unitary/DeligneGroupScheme`), in universe `0`. In the
first table of this section `N = Langlands.Shimura.DeligneTorus` and module paths are relative
to `Langlands/Shimura/Unitary/`; the second table uses the defaults. The first table's rows are fam2 E4. Sources: Milne,
*Introduction to Shimura varieties* (in `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`),
§2, paragraph "Hodge structures as representations of S", printed p.282, PDF 294; Milne 2017,
Definition 12.14, printed p.236, PDF 252.

| Assertion | Lean declaration (module) | Status and evidence |
| --- | --- | --- |
| `𝕊` is smooth, its base change to `ℂ` is a split torus, and `𝕊` is not a split torus over `ℝ` | `NonSplitTorusStatement` (`DeligneNonSplitStatement`) | P: `nonSplitTorusStatement` (`DeligneNonSplitProof`). Non-splitting is the proved theorem `not_isSplitTorus_groupScheme`, not an input |
| `𝕊` is connected reductive and reductive | `ReductiveStatement` (`DeligneReductiveStatement`) | P: `reductiveStatement` (`DeligneReductiveProof`) |
| `𝕊 ≅ Res_{ℂ/ℝ} 𝔾_m` as group schemes | `weilRestrictionIso : Langlands.GroupScheme.WeilGm.groupScheme ℝ ℂ ≅ groupScheme` (`DeligneWeilRestriction`) | D |
| `X^*(𝕊_ℂ) ≅ ℤ × ℤ` and `X_*(𝕊_ℂ) ≅ ℤ × ℤ`; complex conjugation acts by the swap; the action is nontrivial | `characterEquiv`, `cocharacterEquiv`, `characterEquiv_galoisRepresentation_conj`, `cocharacterEquiv_galoisRepresentation_conj`, `characterLattice_galoisRepresentation_conj_ne_one` (`DeligneLattices`) | D. The action is the Library's `Langlands.GroupScheme.characterLattice.galoisRepresentation` (and `Langlands.GroupScheme.cocharacterLattice.galoisRepresentation`) on the lattices of the base-changed torus |

The surrounding general theory (fam2 E1–E3, D3):

| Assertion | Lean declaration (module) | Status and evidence |
| --- | --- | --- |
| Weil restriction of `𝔾_m` along a finite projective algebra `A → B`, smooth, with base change `A → A'` and splitting comparisons (Milne 2017, 2.55, printed p.57, PDF 73) | `WeilGm.groupScheme A B` and `WeilGm.smooth` (`Torus/WeilRestriction`), `WeilGm.baseChangeIso` (`Torus/WeilRestrictionBaseChange`), `WeilGm.splitIso` (`Torus/WeilRestrictionSplit`), `WeilGm.decompositionIso` (`Torus/WeilRestrictionDecomposition`) | D. fam2 E1 |
| For a finite separable field extension `K/k`: `Res_{K/k} 𝔾_m` is a torus; over a field `Ω` in which every `minpoly k x` (`x : K`) splits, it becomes the split torus on the `k`-embeddings `K → Ω`; its lattices are `(K →ₐ[k] Ω) → ℤ` with Galois acting by permuting embeddings, continuously for the discrete topology (Milne 2017, 2.61, printed p.59, PDF 75) | `WeilGm.isTorus_of_finite_separable`, `WeilGm.separableEmbeddingIso`, `WeilGm.separableEmbeddingCharacterEquiv_galoisRepresentation`, `WeilGm.separableEmbeddingCharacterContinuousAction` and the cocharacter analogues (`Torus/WeilRestrictionSeparable`) | D. fam2 E2. Finite separable only; purely inseparable restriction is not used |
| Induced tori are Weil restrictions `Res_{(∏ E_i)/k} 𝔾_m` (Kaletha–Prasad, §2.5(a), Definition 2.5.1, printed p.86, PDF 117) | `InducedTorusWeilDecompositionStatement` (`Torus/InducedWeilDecompositionStatement`) | P: `inducedTorusWeilDecomposition` (`Torus/InducedWeilDecompositionProof`). fam2 E3 |
| For a torus split by an algebraic extension `E/k`, the Galois action on `X^*(T_E)` and `X_*(T_E)` is continuous (Milne 2022, §12.g, printed p.239, PDF 250) | `TorusLatticeGaloisContinuityStatement` (`Torus/LatticeGaloisContinuityStatement`) | P: `torusLatticeGaloisContinuity` (`Torus/LatticeGaloisContinuityProof`). fam2 D3 |

## Field layer: the noncommutative non-split unitary group `U(1,1)`

Sources: Milne 2017, Definition 19.20, printed p.401, PDF 417; Definition 19.22, printed p.402,
PDF 418; the unitary groups of 24.40–24.44, printed pp.523–525, PDF 539–541 (fam5 H5). The
formulation in Lean is the program's own.

**Hypotheses.** In this section `N = Langlands.GroupScheme.QuasiSplitUnitary`, and module paths
in the table are relative to `Langlands/GroupScheme/Examples/`. Every proposition declaration
(`…Statement`) in this section quantifies over:

- fields `F E : Type u` with `[Algebra F E]` and `[Algebra.IsQuadraticExtension F E]`;
- a type `κ : Type u` with `[Fintype κ]` and an `F`-basis `b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)`;
- `c : E ≃ₐ[F] E` with `hc : c ≠ AlgEquiv.refl`.

So `E/F` is a quadratic extension with a nontrivial `F`-automorphism `c`. The construction
`groupScheme b c` (`Examples/QuasiSplitUnitary`) needs the quadratic instance but not `hc`; it
is defined for every `c`, including `c = id`. It is the full unitary group (no determinant
condition) of the hermitian form `h(v, w) = v₁ c(w₂) + v₂ c(w₁)` on `E²`, in every
characteristic. The two D rows below state their own hypotheses.

| Assertion | Lean declaration (module) | Status and evidence |
| --- | --- | --- |
| `U(1,1)` is connected reductive | `IsConnectedReductiveStatement` (`QuasiSplitUnitaryReductiveStatement`) | P: `isConnectedReductive` (`QuasiSplitUnitaryReductiveProof`) |
| The group of `F`-points is not commutative | `NonCommutativeStatement` (`QuasiSplitUnitaryNonCommutativeStatement`) | P: `nonCommutative` (`QuasiSplitUnitaryNonCommutativeProof`) |
| `U(1,1)` has no split maximal torus over `F`, that is `¬ Langlands.GroupScheme.HasSplitMaximalTorus` (predicate in `Langlands/GroupScheme/Torus/FiniteGaloisSplitMaximal`) | `NotSplitStatement` (`QuasiSplitUnitaryNotSplitStatement`) | P: `notSplit` (`QuasiSplitUnitaryNotSplitProof`) |
| Rank: the image of the diagonal cocharacter `λ` is a closed subgroup, every closed split torus over `F` has dimension at most one, and over `E` there is a closed split torus of dimension two | `RankStatement` (`QuasiSplitUnitaryRankStatement`) | P: `rankStatement` (`QuasiSplitUnitaryRankProof`) |
| Weight-two conjugation (CGP Example 2.1.1, formula (2.1.1), printed p.46, PDF 72): for fields `F E` with `[Algebra F E]` and `[Algebra.IsQuadraticExtension F E]`, every commutative `F`-algebra `R : Type u`, every `c : E ≃ₐ[F] E` (`hc` is not assumed), `t : Rˣ` and `x` in the trace-zero submodule `traceZero R c` of `E ⊗[F] R` (`x + c(x) = 0`): in the unitary matrix group `matrixPoints R c`, `diagonalUnitary R c 1 t * upperRoot R c (Multiplicative.ofAdd x) * (diagonalUnitary R c 1 t)⁻¹ = upperRoot R c (Multiplicative.ofAdd (scaleTraceZero R c t 2 x))`, where `diagonalUnitary R c 1 t = diag(t, t⁻¹)` and `scaleTraceZero R c t m x = t^m • x`; for `lowerRoot` the exponent is `-2` | `diagonalUnitary_upperRoot`, `diagonalUnitary_lowerRoot` (`QuasiSplitUnitaryDynamic`) | D |
| Dynamic subgroups of the diagonal cocharacter `λ = cocharacter b c` and of `λ⁻¹ = inverseCocharacter b c`: `P(λ)`, `Z(λ)`, `U(λ)` are the upper triangular, diagonal and upper unipotent subgroups, `P(λ⁻¹)`, `Z(λ⁻¹)`, `U(λ⁻¹)` the lower triangular, diagonal and lower unipotent subgroups, and on every test scheme `T` over `Spec F` the points of `U(λ)` and `U(λ⁻¹)` are the ranges of the upper and lower root points `upperRootPoints b c T`, `lowerRootPoints b c T` | `DynamicStatement` (`QuasiSplitUnitaryDynamicStatement`) | P: `dynamicStatement` (`QuasiSplitUnitaryDynamicProof`). The statement contains no conjugation formula; that formula is the D row above |
| `Z(λ)` is represented by an explicit closed Levi subgroup | `LeviRepresentedStatement` (`QuasiSplitUnitaryLeviRepresentedStatement`) | P: `leviRepresentedStatement` (`QuasiSplitUnitaryLeviRepresentedProof`) |
| `P(λ) = Z(λ) ⋉ U(λ)`, `P(λ) ∩ P(λ⁻¹) = Z(λ)` and `U(λ⁻¹) ∩ P(λ) = 1` | `LeviDecompositionStatement` (`QuasiSplitUnitaryLeviDecompositionStatement`) | P: `leviDecompositionStatement` (`QuasiSplitUnitaryLeviDecompositionProof`) |
| Over `E`, `U(1,1)` becomes `GL₂` | `splittingIso b c hc : baseChangeGroupScheme b c ≅ GeneralLinear.groupScheme (Fin 2) (CommRingCat.of E)` (`QuasiSplitUnitarySplitting`) | D, under all hypotheses above, including `hc` |
| The relative root system of `U(1,1)` with respect to the image of `λ` is nonempty (the contract's purpose for this example) | none | M. No Lean declaration states that the image of `λ` is a maximal split torus or computes `relativeRoots` for `U(1,1)`. The Lean evidence for relative structure is the rank, dynamic and Levi rows above |

## Field layer: general rational structure

All rows are in family 5; the source locators and exact hypotheses are in its rows. The
statements are in `Rational/<Name>Statement` and the proofs in `Rational/<Name>Proof` unless
another module is shown.

| Assertion (fam5 row title) | Lean statement | Status and evidence |
| --- | --- | --- |
| Parabolics defined over `k` are dynamic | `ParabolicDynamicStatement` (fam5 B1, `Absolute/BorelStatement`) | P: `parabolicDynamic` (`Absolute/ParabolicDynamicProof`) |
| Conjugacy of maximal split tori in smooth connected affine groups; reductive groups: conjugacy and the rank | `SmoothMaximalSplitTorusConjugacyStatement` (fam5 A2, `Rational/MaximalSplitTorusStatement`), `MaximalSplitTorusConjugacyStatement` (fam5 A4, `Rational/ConjugacyStatement`) | P: `smoothMaximalSplitTorusConjugacy`, `maximalSplitTorusConjugacy` |
| Levi subgroups of a minimal parabolic; rational Levi subgroups of a parabolic are conjugate | `MinimalParabolicLeviCentralizerStatement` (fam5 B11), `RationalLeviConjugacyStatement` (fam5 B12) | P: `minimalParabolicLeviCentralizer`, `rationalLeviConjugacy` |
| The relative root system; simple roots and rank identities | `RelativeRootSystemStatement` (fam5 C1, `Rational/Statement`), `RelativeSimpleRootBasisStatement` (fam5 C5, `Rational/RelativeRankStatement`) | P: `relativeRootSystem`, `relativeSimpleRootBasis` |
| Normalizer and centralizer of a split torus; the relative Weyl group as a constant group; the relative Weyl group is a finite Coxeter group | `TorusNormalizerRepresentableStatement` (fam5 C6), `RelativeWeylGroupRestrictStatement` (fam5 C7), both in `Rational/TorusNormalizerStatement`; `RelativeWeylCoxeterStatement` (fam5 C9) | P: `torusNormalizerRepresentable` (`Rational/TorusNormalizerProof`), `relativeWeylGroupRestrict_bijective`, `relativeWeylCoxeter` |
| Rational Bruhat decomposition; the relative Tits system; `B W_J B = P_J(k)` | `RationalBruhatStatement` (fam5 D1, `Rational/Statement`), `RelativeTitsSystemStatement` (fam5 D2), `TitsStandardParabolicStatement` (fam5 D7) | P: `rationalBruhat`, `relativeTitsSystem`, `titsStandardParabolic` |
| Classification of parabolics by standard ones; root presentations of a parabolic | `StandardParabolicClassificationStatement` (fam5 D4), `ParabolicRootPresentationStatement` (fam5 D11) | P: `standardParabolicClassification`, `parabolicRootPresentation` |
| Finite parabolic double cosets with torus-adapted representatives | `RepresentedParabolicDoubleCosetStatement` (fam5 D8, `Rational/ParabolicDoubleCosetStatement`) | C. Owner Task 4901 (`f78f48cb-43dd-4e38-a665-b8e068407586`): its proof candidate `a522855f-e13f-46be-8326-86fa9ee2f183` was approved in peer review and awaits integration; it is not in the Library at `86ea837f` |
| Steinberg's theorem (Kaletha–Prasad, Theorem 2.3.3(2), printed p.79, PDF 110) | `DimensionLEOneQuasiSplitStatement` (fam5 H3, `Rational/DimensionLEOneQuasiSplitStatement`) | O. Owner Task 4733 (`0367ba06-f71f-44ff-83b2-e9de61795702`). The published theorem `dimensionLEOneQuasiSplit_of_structural_inputs` (`Rational/SteinbergAssembly`) derives it from three proposition declarations. Two have published proofs: `quasiSplitInnerFormExistence` proves `QuasiSplitInnerFormExistenceStatement` and `dimensionLEOneTorusCocycleVanishing` proves `DimensionLEOneTorusCocycleVanishingStatement`. The third, `QuasiSplitCocycleTorusReductionStatement`, has no published proof |

The relative-root vocabulary is in `Rational/RelativeRoots` (`relativeRoots`,
`IsGenericCocharacter`, `relativeWeylAction`, `relativeRootSpan`) and
`Rational/StandardParabolic` (`simpleRelativeRoots`, `standardParabolic`, `standardLevi`,
`standardUnipotent`).

## Algebraic interfaces for later programs

The contract asks for the following exports. Each row lists the Lean exports, their
hypotheses and conventions, and the remaining limitation.

| Interface | Lean exports | Status, conventions and limitation |
| --- | --- | --- |
| Field-valued group functors and homomorphisms | `rationalPoints G` and `rationalPoints.map f : rationalPoints H →* rationalPoints G` (`Rational/Characters`), for groups over `Spec k` with `k` a commutative ring; `Lie.AffinePoints G A` (`AffinePoints`) for points over an `R`-algebra `A`; `GeneralLinear.pointsEquiv` | D. Points are morphisms from `Spec` of the field or algebra |
| Parabolic, Levi and unipotent inclusions and decompositions | `Dynamic.parabolic`, `Dynamic.centralizer`, `Dynamic.unipotent` (subgroup functors of a cocharacter, `Dynamic/Basic`); `Dynamic.Affine.parabolicHom`, `Dynamic.Affine.centralizerHom`, `Dynamic.Affine.unipotentHom` with `Dynamic.Affine.isRepresentedBy_parabolicHom`, `Dynamic.Affine.isRepresentedBy_centralizerHom`, `Dynamic.Affine.isRepresentedBy_unipotentHom` and `Dynamic.Affine.isClosedSubgroup_parabolicHom`, `Dynamic.Affine.isClosedSubgroup_centralizerHom`, `Dynamic.Affine.isClosedSubgroup_unipotentHom` (`Dynamic/AffineRepresentability`), for `R : CommRingCat` and `G` over `Spec R` with `[AlgebraicGeometry.IsAffine G.X.left]`; `Dynamic.limitGroupHom`, `Dynamic.centralizerToParabolic`, `Dynamic.unipotentIsoKernel`, `Dynamic.multiplicationIso` (`Dynamic/SchemeDecomposition`), for every base `S` and separated `G` (`Dynamic.centralizerToParabolic` needs no separatedness), given closed subgroups representing `P(χ)`, `Z(χ)`, `U(χ)` | D (fam8 F2). Geometric unipotent radical of `P(λ)`: `DynamicGeometricUnipotentRadicalStatement` (`Dynamic/GeometricUnipotentRadicalStatement`), P by `dynamicGeometricUnipotentRadical` (`Dynamic/GeometricUnipotentRadicalProof`, fam4 C6). Parabolics are dynamic: P (fam5 B1) |
| Normalizer, Weyl and Bruhat data | Absolute Weyl groups and root data (family 4, hypotheses in its rows); `TorusNormalizerRepresentableStatement`, `RelativeWeylGroupRestrictStatement`, `RelativeWeylCoxeterStatement`, `RationalBruhatStatement`, `RelativeTitsSystemStatement`, `TitsStandardParabolicStatement`. Each of these six statements assumes a connected reductive `G` over an arbitrary field `k` and a maximal split torus `T ⟶ G` (a split subtorus for `TorusNormalizerRepresentableStatement`); the last four also take a generic cocharacter of `T` | P (rational structure table above). Double cosets with represented parabolics: C; the proof candidate of Task 4901 was approved in peer review and is not yet in the Library |
| Rational character and cocharacter lattices | Constructions: `rationalCharacters G := HomAdd G (Gm S)` (`Rational/Characters`), defined for every group `G` over any base `S`; `characterLattice`, `cocharacterLattice` (`Torus/Lattice`) with `characterLattice.galoisRepresentation` and `cocharacterLattice.galoisRepresentation` (`Torus/LatticeGalois`). Structural statements, all four in `Rational/CharactersStatement` and each only for a connected reductive `G` (`IsConnectedReductive G`) over an arbitrary field `k`: `RationalCharacterLatticeStatement` (`X^*(G)_k` is free of finite rank), `CharacterRestrictionStatement` (for a split component `A ⟶ G`, restriction `X^*(G)_k → X^*(A)` is injective with finite-index image), `SplitComponentStatement` (a split component exists and is unique up to isomorphism over `G`), `LeviSplitComponentStatement` (for a maximal split torus `T ⟶ G`, a cocharacter `μ` of `T` and a closed subgroup `M ⟶ G` representing the centralizer of the image of `μ` in `G`: `M` is connected reductive, and every split component of `G` factors through a split component of `M` that factors through `T`, compatibly with restriction of characters) | The lattices and their Galois representations: D (fam6 A1). P: `rationalCharacterLattice` (`Rational/CharacterLatticeProof`) and `characterRestriction` (`Rational/CharacterRestrictionProof`) (fam5 E2), `splitComponentStatement` (`Rational/SplitComponentProof`, fam5 E1), `leviSplitComponentStatement` (`Rational/LeviSplitComponentProof`, fam5 E3). Lattice continuity: P (fam2 D3) |
| Relative roots and positivity data | `relativeRoots`, `simpleRelativeRoots`, standard parabolics (above); `RelativeRootSystemStatement`, `RelativeSimpleRootBasisStatement`, `StandardParabolicClassificationStatement`, `ParabolicRootPresentationStatement`. Each assumes a connected reductive `G` over an arbitrary field `k`. The first three take a maximal split torus `T ⟶ G`, and the second and third also a generic cocharacter of `T`; `ParabolicRootPresentationStatement` takes morphisms `P ⟶ G`, `M ⟶ P` and `A ⟶ M`, and its existence part assumes that they are a parabolic subgroup, a rational Levi subgroup of it and a split component of that Levi | P. Positivity is given by a generic cocharacter (`IsGenericCocharacter`). For `U(1,1)` the relative roots are M (above) |
| The character `det(Ad on Lie U)` where defined | `DynamicAdjointDeterminantStructureStatement` (`Dynamic/AdjointDeterminantStructureStatement`) and `DynamicAdjointDeterminantExistenceStatement` (`Dynamic/AdjointDeterminantExistenceStatement`). Both assume a connected reductive `G` (`IsConnectedReductive G`) over an arbitrary field `k`, a cocharacter `χ` of `G`, and morphisms `P ⟶ G`, `M ⟶ G`, `U ⟶ G` representing `P(χ)`, `Z(χ)`, `U(χ)`. The structure statement concludes that `P`, `M`, `U` are affine, closed subgroups, smooth and locally of finite type, that `Lie U` is finite-dimensional over `k`, and that `U` has finite coordinates. The existence statement gives finite coordinates on `Lie U` and characters `δ_P` of `P` and `δ_M` of `M`: on points over every `k`-algebra, `δ_P` is the determinant of the adjoint action of `P` on `Lie U`, and `δ_M` is the restriction of `δ_P` to `M` and the determinant of the adjoint action of `M` | P: `dynamicAdjointDeterminantExistence` (`Dynamic/AdjointDeterminantExistenceProof`, fam4 E2) and `dynamicAdjointDeterminantStructure` (`Dynamic/AdjointDeterminantStructureProof`, fam4 E1). Convention: the determinant itself, not its inverse or square root. The Levi reciprocity statement `Dynamic.LeviAdjointDeterminantReciprocityStatement` (`Dynamic/LeviAdjointDeterminantReciprocityStatement`, fam4 E3) is C, owner Task 5476 (`a54e38fe-1a3a-45d4-b553-05208da37fcb`). The term is `leviAdjointDeterminantReciprocity_of_structure relativeRootReflectionExistence centralSplitTorusCharacter dynamicCentralizerReductive` (modules `Dynamic/LeviAdjointDeterminantReciprocityReduction`, `Rational/RootReflectionExistenceProof`, `Rational/CentralSplitTorusCharacterProof`, `Dynamic/CentralizerReductiveProof`) |
| Central and derived/adjoint comparisons | `SchemeTheoreticCenterExistenceStatement` (`Reductive/CenterStructureStatement`, fam6 C1), `AdjointQuotientExistenceStatement` (`Adjoint/ExistenceStatement`, C4), `DerivedSubgroupRepresentabilityStatement` (`Derived/StructureStatement`, D1, affine and locally of finite type `G`), `CocenterQuotientExistenceStatement` (`Derived/CocenterQuotientStatement`, D8), `SimplyConnectedFieldExtensionStatement` (`SimplyConnected/FieldExtensionStatement`, F3), `SimplyConnectedCoverExistenceStatement` (`SimplyConnected/CoverExistenceStatement`, F4, semisimple `G`). All six are over an arbitrary field `k`. The centre and the adjoint quotient are for connected reductive `G`, the cocentre for connected reductive `G` with a derived subgroup `D ⟶ G`; the field-extension statement says that semisimplicity, simple connectedness and simply connected covers are preserved by base change along every field extension | P: `schemeTheoreticCenterExistence` (`Reductive/CenterExistenceProof`), `adjointQuotientExistence` (`Adjoint/ExistenceProof`), `derivedSubgroupRepresentability` (`Derived/RepresentabilityProof`), `cocenterQuotientExistence` (`Derived/CocenterQuotientProof`), `simplyConnected_fieldExtension` (`SimplyConnected/FieldExtensionPackageProof`), `simplyConnectedCoverExistence` (`SimplyConnected/CoverExistenceProof`). `DerivedAnnihilationStatement` (`Derived/AnnihilationStatement`, fam6 D9) is C, by `derivedSubgroup_baseChange_eq_of_field` (`Derived/FieldBaseChangeAssembly`), `IsDerivedSubgroup.baseChange_of_eq` (`Derived/BaseChangeElementary`), `IsDerivedSubgroup.comp_eq_one` and `IsDerivedSubgroup.characterRestrict_eq_zero` (`Derived/KernelAnnihilation`); owner Task 5444 (`13a72515-2207-4c10-9fbc-c74917768715`) |
| Galois-equivariant absolute based root datum | `GaloisPinningData` with `GaloisPinningData.galoisAction` and the Weyl-corrected `GaloisPinningData.starAction` (`Reductive/StarAction`), and the lemmas `GaloisPinningData.exists_weyl_mul_galoisAction_eq_starAction`, `GaloisPinningData.starAction_eq_galoisAction` (when the Galois action of `σ` preserves the base) and `GaloisPinningData.starAction_eq_one_iff` (the star action of `σ` is trivial iff its Galois action is in the Weyl group); `GaloisPinningData.exists_finiteGalois`, `GaloisPinningData.ofSeparableClosure` and `absoluteStarAction` (`Reductive/AbsoluteStarAction`) for connected reductive `G` with `[AlgebraicGeometry.IsAffineHom G.X.hom]` (and `[AlgebraicGeometry.LocallyOfFiniteType G.X.hom]` for `absoluteStarAction`, over `SeparableClosure k`) | D (fam6 A1, A3). `StarActionIndependenceStatement` (any two data are conjugate by a `G(E)`-point compatibly with the star actions) and `StarActionContinuityStatement` (`Reductive/StarActionStatement`, fam6 A4, A5), both for `G` affine and locally of finite type over `k` and Galois pinning data over a field extension `E` of `k` (algebraic over `k` in the continuity statement): P, `StarActionIndependence.starActionIndependence` (`Reductive/StarActionIndependenceProof`), `starActionContinuity` (`Reductive/StarActionContinuityProof`). `StarActionQuasiSplitStatement` (`Reductive/StarActionQuasiSplitStatement`, fam6 A6): O, owner Task 5456 (`274ef979-d206-458b-9a02-bf8dfa7ed4b2`) |
| Base-change-compatible integral models (later work) | `IntegralModel R K G` (`IntegralModel`): an affine flat group of finite type over a domain `R` with fraction field `K`, with an isomorphism of its generic fibre to `G`; `IntegralModel.baseChange` and `IntegralModel.isSmooth_baseChange` (`IntegralModel/BaseChange`) for a domain `A` with fraction field `L` and compatible towers `R → A → L`, `R → K → L` | D; these constructions have no row in a family ledger. Spreading of a connected reductive group with a parabolic over a number field to a finite set of places: `IntegralModel.ReductiveParabolicSpreading.ExistenceStatement` (`IntegralModel/ReductiveParabolicSpreadingStatement`), P by `IntegralModel.ReductiveParabolicSpreading.existence` (`IntegralModel/ReductiveParabolicSpreadingProof`, fam7 G2). Chevalley group schemes over `ℤ` and their base change: M (fam7 G1, recorded there as O); this is the remaining later integral-model work of the contract |

Two further statements about integral models are recorded in fam7 G3 but are not exports of
this program. Both concern a connected reductive `G` over a nonarchimedean local field `F` and
an integral model of `G` over the valuation ring of `F` whose special fibre is connected
reductive. `IntegralModel.MaximalCompactStatement` (`IntegralModel/MaximalCompactStatement`)
says that the integral points of the model form a compact subgroup of `G(F)`, maximal among
compact subgroups, for the topology of the rational points.
`IntegralModel.BuildingComparisonStatement` (`IntegralModel/BuildingComparison`) asserts that
there exist a reduced root-valuation building of `G` with a complete nonpositively curved
metric and a continuous isometric action of `G(F)`, and a special vertex whose compact
stabilizer is the group of integral points and which is the only point fixed by that group. The
contract excludes topologies on `G(F)` and Bruhat–Tits buildings from this program's
implementation obligations, so these two statements are consumers of the algebraic exports, not
obligations of the contract. At `86ea837f` both are O; their owner tasks are Task 4686
(`21033437-c908-4d4f-bf9a-06d1f642447a`) and Task 4705
(`e93a1c4a-39d9-440a-b41f-f3071783e6e4`).

## Status changes since the family ledgers

Changes at `86ea837f` compared with the commit each ledger describes:

- fam5 D7 `TitsStandardParabolicStatement`: C → P, `titsStandardParabolic`
  (`Rational/TitsStandardParabolicProof`).
- fam5 D8 `RepresentedParabolicDoubleCosetStatement`: still C at `86ea837f`; the proof
  candidate `a522855f-e13f-46be-8326-86fa9ee2f183` of Task 4901 was approved in peer review
  and awaits integration.
- fam7 (commit `18a1f10`), C → P:
  - B2 `splitSemisimpleRootSpan` (`Reductive/SplitSemisimpleRootSpanProof`) and
    `splitSemisimpleOfFiniteRootIndex` (`Reductive/SplitSemisimpleFiniteRootIndexProof`);
  - E2 `splitPinningExistence` (`Reductive/SplitPinningExistenceProof`);
  - F1–F3 `steinbergBigCell`, `steinbergCovariantExhaustion`, `steinbergTensorEmbedding`
    (`Reductive/SteinbergBigCellProof`, `Reductive/SteinbergCovariantExhaustionProof`,
    `Reductive/SteinbergTensorEmbeddingProof`), and the consumers listed under F:
    `simplyConnectedPositiveCharConjugationMap` (`Reductive/PositiveCharConjugationMapProof`),
    `reductiveGeometricReductivity` (`Reductive/GeometricReductivityProof`),
    `simplyConnectedDerivedCoverExistence` (`SimplyConnected/DerivedCoverProof`);
  - G2 `IntegralModel.ReductiveParabolicSpreading.existence`
    (`IntegralModel/ReductiveParabolicSpreadingProof`).
- fam7 G1 (Chevalley groups over `ℤ`): O in that ledger, M in this note's codes. The
  assertion has no Lean statement in either case.
- Families 1, 2, 3, 4, 6 and 8: no changes.

## Remaining limitations

None of these gaps is hidden as a hypothesis in a published statement.

1. `U(1,1)`: no Lean statement computes its relative roots or says that the image of `λ` is a
   maximal split torus (M).
2. Galois structure: `StarActionQuasiSplitStatement` is open (Task 5456).
3. Rational structure: Steinberg's theorem `DimensionLEOneQuasiSplitStatement` is open
   (Task 4733); `RepresentedParabolicDoubleCosetStatement` is C, and the proof candidate of
   Task 4901 for it, approved in peer review, awaits integration.
4. Composites without an accepted proof: `DerivedAnnihilationStatement` (owner Task 5444);
   `Dynamic.LeviAdjointDeterminantReciprocityStatement` and the `GL_n` component statements of
   Milestone 1(a) (owner Task 5476). Task 5476 asks for proofs of 33 closed composite
   statements, including these.
5. The two I rows of Milestone 1(a) are not stated by any proposition declaration.
6. Integral models: Chevalley group schemes over `ℤ` are missing (M); the contract treats
   them as later work of this program. The maximal compactness and building comparison
   statements of fam7 G3 are open, but they lie outside the contract's implementation
   obligations (see the end of "Algebraic interfaces for later programs").
7. The open and missing targets at the end of each family ledger remain open at `86ea837f`,
   except those listed under "Status changes since the family ledgers". All of them belong
   to the algebraic families of the contract, except fam7 G3, which item 6 places outside the
   contract's implementation obligations.

## How the names were checked

The author generated a private Lean module from this note and compiled it in the environment
above at Library commit `86ea837f`. The module imports every Lean module that the note cites
(129 modules) together with the imports of the private check module described under "Status
codes and evidence" (144 imports in all). It defines a command `#resolve X` that resolves `X`
with `Lean.resolveGlobalConstNoOverload` and prints the full name found and the module that
declares it. For every occurrence of a Lean name in code font on a line of this note, the
module runs `#resolve X` inside `namespace N … end N`, where `N` is the namespace of that
line's section (see "Names and modules" at the top). The three section namespaces
`Langlands.GroupScheme.GeneralLinear`, `Langlands.Shimura.DeligneTorus` and
`Langlands.GroupScheme.QuasiSplitUnitary` are checked by opening them, which fails for a
namespace that no imported module declares. These open commands come before every namespace
command of the module. Variables such as `G` or `k`, mathematical notation, commit hashes and
source ids are not Lean names and were skipped.

The last run, record `d993387d-587e-41be-a985-04328ddbf51c`, had no errors or warnings. All
343 name occurrences resolved, and the six occurrences of the three namespaces opened. Like the
check described under "Status codes and evidence", this run is private and is not public
evidence.

Three scripts then compared the note with the Library files and with this output:

- **Module paths.** Each of the 138 module paths in code font, read with its section's base
  directory, is an existing `.lean` file at `86ea837f`. The other code spans with a slash are
  the base directories themselves, field extensions such as `E/F`, and the patterns
  `Rational/<Name>Statement` and `Rational/<Name>Proof`.
- **Names with modules.** Wherever names are followed by a module in parentheses, as in `X`
  (`M`), the module that declares the resolved name is `M`. There are 147 such name
  occurrences, and no mismatch.
- **Row references.** Each of the 63 references "famN XY" names an existing row of the
  published family-N ledger. The author read the row titles and compared them with the
  assertions.
