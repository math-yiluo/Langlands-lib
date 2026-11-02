# Algebraic and reductive group schemes: reuse ledger

Worker 1107 and Worker 207 wrote this ledger for the standing program task
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (revision 2), at the operator's request
of 1 November 2026. For each planned unit it decides whether to **port** an
outside Lean result, **adapt** its proof route, or **rewrite** the unit on the
Library's `Langlands.GroupScheme`, and gives the reason. Worker 1107 wrote §§1–5
and §7 (dynamic subgroups, unipotent and reductive definitions, reductivity of
GL_n, root data). Worker 207 wrote §6 (split tori, diagonalizable groups, Galois
lattices, and the Toric results already in our Mathlib). Worker 1107 wrote the two §6
rows on Weil restriction tori and on the classification of tori by Galois lattices.
Those rows cite TauCeti files present at the pinned commit but absent from the
audit snapshot.

The ledger establishes no theorem and adds or changes no Lean target. Its Lean
evidence comes from private `lean_check` runs in environment `3b864ddf`, cited
by diagnostic ID. None of it is an accepted Library result, and an outside
declaration that compiles here is not thereby reviewed mathematics.

## 1. Pins and sources

| Project | Commit | Lean | Mathlib |
|---|---|---|---|
| TauCetiProject/TauCeti | `8428d6217f74afa72531df0bc85d7b57ab72810f` | 4.36.0-rc1 | `2cabef97b63d3275776b8b060d802de6a6fa1055` (839 commits ahead of ours) |
| YaelDillies/toric | `bef9a1f3ff7cc80f56cbfb74770086c6bf75d17f` | 4.36.0-rc2 | 1008 commits ahead of ours |
| This project, environment `3b864ddf` | Library `dac2bb9e83346876770fced17af26f0cba7f4c98` | 4.34.0 | `5ed2965256430c3649e86755f9576b54eca72435` |

Both outside projects are Apache-2.0. The pins are those of Worker 139's audit,
registered as source `algebraic-groups-external-source-audit-2026-11-01`
(folder `Algebraic groups - pinned external source selections and bounded audit
(1 November 2026)`, file `REPORT.md`). File paths below are relative to each
repository root at its pin. Line numbers refer to those files.

The audit snapshot holds selected files, not import closures. Worker 1107
computed TauCeti closures from the files' `import` lines, fetching missing
modules from `raw.githubusercontent.com` at the pin. The 25 fetched files that
also occur in the snapshot are byte-identical to the snapshot copies. "Missing"
below counts Mathlib modules imported by a closure but absent at our Mathlib pin.

The mathematical reference for the dynamic units is Conrad, *Reductive group
schemes* (source `conrad-2014-reductive-group-schemes`), Theorem 4.1.7 and
Proposition 4.1.10 on pp. 112–114. Theorem 4.1.7 assumes a finitely presented
affine group over a ring. Its smoothness part (4) assumes `G` smooth and no
noetherian hypothesis. The remark after Example 4.1.9 notes that the
construction commutes with base change and works over any base scheme.

## 2. Decision vocabulary

- **Port**: copy the outside modules unchanged except for compatibility edits,
  keeping their licence headers. Then prove an adapter theorem identifying the
  ported object with the Library object.
- **Adapt**: prove the unit on `Langlands.GroupScheme`, following the outside
  proof route. No outside code is imported.
- **Rewrite**: construct or prove the unit on `Langlands.GroupScheme` from the
  original literature. The outside code serves only as a comparison.
- **Reuse**: use a declaration of our pinned Mathlib directly.

## 3. Dynamic subgroups P(λ), Z(λ), U(λ) (Worker 1107)

The Library definitions are categorical. `Langlands.GroupScheme.Dynamic` (candidate
`93b4cbe1-abe6-4ace-b39f-292681285be1`, approved and awaiting integration)
defines P(λ), Z(λ) and U(λ) as subgroup functors on all of `Over S`, for an
arbitrary base scheme `S` and every test scheme. TauCeti's
`TauCeti/Algebra/AlgebraicGroup/Dynamic/Parabolic.lean` defines `parabolic`
(line 154), `levi` (line 245) and `unipotent` (line 277) as subgroups of the
convolution group `WithConv (H →ₐ[R] A)`. Here `H` is a Hopf algebra over a
commutative ring `R`, and `A` runs over commutative `R`-algebras. So TauCeti
covers an affine group over an affine base, tested on affine schemes only.

| Unit | Outside file at pin | Decision | Reason | Adapter obligations |
|---|---|---|---|---|
| D1. Subgroup functors and the definitions of P(λ), Z(λ), U(λ) | TauCeti `Dynamic/Parabolic.lean` lines 154, 245, 277 | **Rewrite** (done: `93b4cbe1`) | The contract needs every base scheme and every test scheme, including nonreduced ones. TauCeti's definitions are affine-only. | None for the definitions. The comparison with TauCeti is part of D2. |
| D2. Representability by closed subgroups, for affine `G` over an affine base | TauCeti `Dynamic/Representability.lean`: `parabolicDefiningHopfIdeal` (line 98), `parabolicPointsIso` (line 152). Closure 31 modules, 8,530 lines, 0 missing. | **Port, then adapt** | Coordinate algebra and Hopf ideal are the same in both settings. The 7-module core compiled with one edit (§4). | (a) For `G = Spec H` over `Spec R`, identify P(λ)(T) with TauCeti's `parabolic (Γ_R T) l` for affine `T`. Use the Library's `Langlands.GroupScheme.Corepresented.pointsEquiv` (`CorepresentedPoints.lean`) and Mathlib's `algΓAlgSpecAdjunction` (`AlgebraicGeometry/Group/Affine.lean` line 301). (b) Extend the comparison to non-affine `T`, either by the Zariski-sheaf property or by bounding Laurent degrees through the weight grading. (c) For a non-affine base, glue over affine opens of `S` (rewrite). |
| D3. Limit map P(λ) → Z(λ), kernel U(λ), and Z(λ) ⋉ U(λ) ≅ P(λ) | TauCeti `Dynamic/LeviDecomposition/Basic.lean`: `limitToLevi` (line 67), `leviDecompositionMulEquiv` (line 191), on points. Closure 8 modules, 2,365 lines, 0 missing. TauCeti `Dynamic/Limit.lean`: `parabolicLimitKernelIso` (line 196), as Hopf schemes. Closure 114 modules, 29,677 lines. | **Port** the 8-module points layer. **Rewrite** the scheme-level kernel identification. | The points layer compiled here unchanged (§4). The Library kernel `Langlands.AbelianScheme.Kernel` has an all-test point equivalence, so kernel = U(λ) becomes a statement about points. Porting `Limit.lean`'s 114-module Hopf-ideal closure would not shorten it. | Adapter of D2. The limit morphism as a group-scheme map follows from representability (D2) and Yoneda. |
| D4. Smoothness of P(λ), Z(λ), U(λ) for smooth `G` | TauCeti `Dynamic/Smooth.lean` lines 207–237, under `[IsNoetherianRing R]`, `FiniteTypeCommHopfAlgCat` and `[Algebra.Smooth R H]`. Closure 49 modules, 12,543 lines, 0 missing. | **Port, then adapt**, keeping the noetherian hypothesis | Conrad 4.1.7(4) needs no noetherian hypothesis; Conrad (p. 114) attributes it to CGP Proposition 2.1.8(3). The first milestone works over fields, which are noetherian. | Every ported statement keeps `IsNoetherianRing`. Removing it is a separate unit. |
| D5. Base change of P(λ), Z(λ), U(λ) | TauCeti `Dynamic/BaseChange/Points.lean` (closure 12 modules, 3,145 lines) and `Dynamic/BaseChange/Ideals.lean` | **Rewrite** | With all-test definitions, a point of the base change `G_{S'}` with values in `T'` over `S'` is a point of `G` with values in `T'` viewed over `S`, by the pullback adjunction. So base change of P(λ), Z(λ), U(λ) is formal. The Library's `GroupScheme.baseChange` and `ConjugacyBaseChange` supply the comparison maps; no Hopf ideals are needed. | None. |
| D6. GL_n with a diagonal cocharacter: P, Z, U are the block upper triangular, block diagonal and block unipotent subgroups | TauCeti `GeneralLinear/Dynamic/Weight/Basic.lean` (closure 192 modules, 48,452 lines), `Weight/Parabolic/Basic.lean` (200, 50,295), `Weight/Levi/Decomposition.lean` (211, 53,081), `Weight/Unipotent/Radical.lean` (461, 104,187; 1 missing: `Mathlib.LinearAlgebra.TensorProduct.Lift`) | **Rewrite**, with a bridge to the Library's `Langlands.GeneralLinear.BlockShape` (`Langlands/Group/GL/Blocks.lean`) | The closures are large. TauCeti's GL_n is a determinant-localization Hopf model, so it would need an isomorphism with the Library's two-matrix `Langlands.GroupScheme.GeneralLinear` before use. The entries of g in GL_n(A[t,t⁻¹]) under conjugation are explicit monomials. TauCeti's weight convention (entry (i,j) of P vanishes when `w i < w j`) agrees with ours. | Bridge to `BlockShape.parabolic`, `leviSubgroup`, `unipotentSubgroup` and `leviProjection` through `indexEquiv`. Sources: CGP Example 2.1.1 (GL_n), and Conrad Example 4.1.8 (SL_n). |
| D7. P(λ) = G exactly when λ is central, for reductive `G` over a field | TauCeti `Dynamic/Reductive.lean`: `leviDefiningHopfIdeal_eq_bot_iff` (line 125). Closure 457 modules, 96,497 lines, 1 missing. | **Adapt** (deferred) | The proof is short given D3, D4 and reductivity. The closure is too large to port. | Follows R1 and D2–D4. |

## 4. Port test in the Lean service

To estimate the backport cost of D2–D4, Worker 1107 compiled the TauCeti
closure of `TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Basic` in a
private draft. This closure consists of `Dynamic.Parabolic` and its 7-module
closure plus `Dynamic.LeviDecomposition.Basic`. The 8 modules total 2,365 lines:
`Dynamic/Parabolic`, `Dynamic/Points`, `Dynamic/LeviDecomposition/Basic`,
`FunctorOfPoints`, `Hopf/Map`, `MultiplicativeGroup/Basic`,
`Polynomial/Laurent/Basic` and `Polynomial/Laurent/Polynomial`, all under
`TauCeti/Algebra/`. The files kept their `TauCeti.*` module names, licence
headers and `module` / `public import` headers. The Lean service accepts these.

- Check `f6f446ee-ae67-402b-bd12-56690951827f` (7-module Parabolic closure,
  unchanged): 4 errors, all in `Polynomial/Laurent/Basic.lean`, lines 396 and
  411. The lemma `MonoidHom.coe_ofClass` does not exist at our Mathlib pin.
- Edit: replace `MonoidHom.coe_ofClass` by `MonoidHom.coe_coe` (2 occurrences).
  No other file changed.
- Check `f6d282d6-e0eb-4dd6-b931-30b44125417f`: all 7 modules build, with 0
  errors and 0 warnings.
- Check `a8b5c726-be60-4fc0-bac9-9dd8fce69a37`, adding
  `Dynamic/LeviDecomposition/Basic.lean` unchanged: 8 modules build, with 0
  errors and 0 warnings. `TauCeti.Cocharacter.leviDecompositionMulEquiv` uses
  only `propext`, `Classical.choice` and `Quot.sound`.

So this core costs one lemma rename against an 839-commit Mathlib gap. That
supports porting the affine points layer (D2, D3). The 31-module closure of
`Dynamic/Representability` and the 49-module closure of `Dynamic/Smooth` were
not compiled. Their cost remains an estimate.

## 5. Unipotent and reductive groups, and GL_n (Worker 1107)

TauCeti states these notions as properties of finite-type commutative Hopf
algebras. `TauCeti/Algebra/AlgebraicGroup/Reductive/Basic.lean` line 71 defines
`reductiveCommHopfAlgProperty k` over a field `k`: smooth and geometrically
connected, and every normal Hopf ideal of `AlgebraicClosure k ⊗ H` with
geometrically connected smooth unipotent quotient is the augmentation ideal.
`Reductive/Over.lean` line 43 defines `reductiveCommHopfAlgPropertyOver R` over
a ring: `Algebra.Smooth R H`, and reductive base change to every algebraically
closed field `k` that is an `R`-algebra in the same universe.
`PseudoReductive/Basic.lean` line 80 defines `pseudoReductiveCommHopfAlgProperty`.

| Unit | Outside file at pin | Decision | Reason | Adapter obligations |
|---|---|---|---|---|
| R1. Unipotent, pseudo-reductive, connected reductive (over a field) and reductive (over a base) group schemes | TauCeti `Reductive/Basic.lean` line 71 (closure 173 modules, 38,540 lines), `Reductive/Over.lean` line 43 (215, 46,026), `PseudoReductive/Basic.lean` line 80 (448, 97,120). Each closure misses `Mathlib.LinearAlgebra.TensorProduct.Lift`. | **Rewrite** (done: candidate `bb8b6c40-f39b-41a5-b09b-0015ccef4ae2`, module `Langlands.GroupScheme.Reductive.Basic`) | The contract needs `Langlands.GroupScheme` over an arbitrary base scheme, including non-affine bases. TauCeti's notions are affine and finite type, and their closures are large. Our definitions follow Milne (2017) 6.45–6.47 and §19.b, Conrad–Gabber–Prasad Definition 1.1.1, and Conrad Definition 3.1.1. | Optional, and only if TauCeti's reductive layer is ever ported: for `S = Spec R` and `G = Spec H` of finite type, `IsReductive` agrees with `reductiveCommHopfAlgPropertyOver`. |
| R2. GL_n is reductive over every field, then over every base | TauCeti `GeneralLinear/Reductive/Basic.lean`: `reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra` (line 94), via `eq_augmentation_of_isNormal_of_smoothUnipotent` (line 66). TauCeti `GeneralLinear/Reductive/Over.lean` line 44, over every commutative ring. Closure 357 modules, 80,138 lines, 1 missing. | **Rewrite**, adapting the route | The closure is too large, and TauCeti's GL_n model differs from the Library's. We use Milne Lemma 19.16 and Example 19.19: for a normal unipotent subgroup N, the fixed space V^N of the standard representation is nonzero and GL_n-stable, so it is everything and N is trivial. Smoothness of GL_n is already published (`GeneralLinearSmoothProof`). Connectedness of the geometric fibres is new work. | Uses the fixed-vector definition from R1 and the Library's `MatrixRepresentation`. |

## 6. Tori, diagonalizable groups, Weil restriction and Galois lattices (Worker 207)

Sources: the pinned snapshots in the audit folder of source
`algebraic-groups-external-source-audit-2026-11-01`, i.e.
`literature/Algebraic groups - pinned external source selections and bounded audit (1 November 2026)/`.
Below, `toric/` means `YaelDillies--toric/source/` (commit
`bef9a1f3ff7cc80f56cbfb74770086c6bf75d17f`, Apache-2.0) and `tauceti/` means
`TauCetiProject--TauCeti/source/` (commit `8428d6217f74afa72531df0bc85d7b57ab72810f`,
Apache-2.0). Host means the Library's `Langlands.GroupScheme`
(`GroupScheme S := Grp (Over S)`). "Mathlib" means the pinned
`5ed2965256430c3649e86755f9576b54eca72435`.

### Port test

I copied the Toric chain `Toric/Mathlib/Algebra/Category/Ring/Under/Basic.lean`,
`Toric/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`, `Toric/MvLaurentPolynomial.lean`,
`Toric/Hopf/GrpAlg.lean`, `Toric/Hopf/Diagonalisable.lean`,
`Toric/GroupScheme/MonoidAlgebra.lean`, `Toric/GroupScheme/Diagonalizable.lean`,
`Toric/GroupScheme/Torus.lean` and `Toric/GroupScheme/Character.lean` into a private draft under
the namespace prefix `Langlands.PortTest`. I changed only the following:

- removed the module-system keywords (`module`, `public`, `@[expose]`);
- renamed the `Toric.*` imports;
- deleted the one `sorry` lemma, `isDiagonalisable_iff_span_isGroupLikeElem_eq_top`
  (`toric/Toric/GroupScheme/Diagonalizable.lean`, line 431);
- removed the name `AddMonoidHom.coe_ofClass`, which does not exist in the pinned Mathlib, from
  one `simp only` list in `Character.lean` (line 188).

With these changes the whole chain compiles in the project Lean service against the pinned
Mathlib, with no errors and no warnings. The private `lean_check` records are:

- `57711153-d504-439f-912f-9e6ef3e7a2ce`: the chain with the first three changes only.
  `GrpAlg`, `Hopf/Diagonalisable`, `MonoidAlgebra`, `Diagonalizable` and `Torus` build;
  `Character.lean` fails with one error, unknown constant `AddMonoidHom.coe_ofClass` at
  line 188. This is the initial failure.
- `6e3313ee-5ea1-40fc-952b-61ad7d25f97f`: after the fourth change, `Character` builds on the
  same chain with no errors and no warnings. Its inspection of `isPerfPair_charPairing` reports
  only `propext`, `Classical.choice` and `Quot.sound`.
- `0c0f92f1-0138-40a6-8898-bdf094aa2d1f`: the same sources (same source hash as
  `6e3313ee`), no errors. Its inspection of `diagHomEquiv` reports the same three axioms.

Porting this code therefore costs almost nothing. The real work is the host adapters listed
below.

### Rows

| Planned unit | Outside file@commit (audit snapshot path) | Decision | Reason | Host adapter obligations / hypotheses |
|---|---|---|---|---|
| Finite-rank split-torus predicate | `toric/Toric/GroupScheme/Torus.lean`@bef9a1f3 (`IsSplitTorusOver`, `SplitTorus`, `exists_iso_diag_finite_of_isSplitTorusOver_locallyOfFiniteType`) | Keep the host predicate; adapt Toric as a bridge | The host `IsSplitTorus G := ∃ I, Finite I ∧ Nonempty (G ≅ splitTorus S I)` (candidate fed41e78, accepted in review) is stated on `Grp (Over S)` with finite rank, the usual convention (Milne AG Def 12.14; Conrad App. B). Toric's `IsSplitTorusOver` allows any free ℤ-module, so infinite rank too. Its finite-rank lemma needs `LocallyOfFiniteType (G ↘ S)` and `Nonempty S`. | Bridge theorem: host `IsSplitTorus G` ↔ (Toric `IsSplitTorusOver` ∧ `LocallyOfFiniteType`). This needs (i) `splitTorus S I ≅ Diag S (FreeAbelianGroup I)` in `Grp (Over S)` for finite `I`, and (ii) `Diag S (M × N) ≅ Diag S M ⊗ Diag S N`, which is not in Toric (prove pointwise with host `isoOfPoints`). |
| Diagonalizable groups `D_S(M)` | `toric/Toric/GroupScheme/Diagonalizable.lean`@bef9a1f3 (`Diag`, `diagMonFunctor`, `diagFunctor`, `Diag.map`, `Diag.mapIso`, `diagSpecIso`, `diagPullbackIso`, `locallyOfFiniteType_diag(_iff)`, `faithful_diagFunctor`, `full_diagFunctor`, `HomGrp`, `diagHomGrp`, `diagHomEquiv`, `IsDiagonalisable`) | Port | Compiles once the `sorry` lemma at line 431 is deleted, and `diagHomEquiv` depends only on the standard axioms. Nothing like it exists in Mathlib or the host. Over `Spec R` with `R` a domain, fullness gives `diagHomEquiv : (N →+ M) ≃+ Hom(D(M), D(N))`. | Toric works with a scheme `G` carrying `[G.Over S]` and `[GrpObj (G.asOver S)]`. Host objects are `Grp (Over S)`, so the port needs a wrapper `Diag.toGroupScheme S M : GroupScheme S := Grp.mk (asOver (Diag S M) S)`. Toric `HomGrp G G' S` must be identified with host homomorphisms (`Grp.mk _ ⟶ Grp.mk _`; definitional after unfolding). Key comparison: host `Gm S ≅` Toric `𝔾ₘ[S] = Diag S (FreeAbelianGroup PUnit) ≅ Diag S ℤ` (`Diag.mapIso`; both sides are pullbacks of `Spec` of the Laurent ring over `ULift ℤ`; prove with host `Gm.isoOfPoints`, which needs a natural points equivalence `(T ⟶ Diag S M) ≃* (Multiplicative M →* Γ(T)ˣ)`; Toric's `SplitTorus.representableBy` is commented out, so this is new work). |
| Hopf side: group algebras and diagonalisability | `toric/Toric/Hopf/GrpAlg.lean`, `toric/Toric/Hopf/Diagonalisable.lean`@bef9a1f3 (`commMonAlg`, `commGrpAlg`, fully faithful over a domain; `Bialgebra.IsDiagonalisable`, `isDiagonalisable_iff_span_isGroupLikeElem_eq_top` over a domain with `NoZeroSMulDivisors`) | Port | Proved, and compiles with only the header edits listed above. Builds on Mathlib's `RingTheory/Bialgebra/MonoidAlgebra.lean` (see the last section). | None at the algebra level. Keep the Apache-2.0 header and authors, and add a `licenses/` entry for Toric when porting. |
| Base change of `D_S(M)` as a monoid functor | `toric/Toric/GroupScheme/MonoidAlgebra.lean`@bef9a1f3 (`specCommMonAlgPullback`, `specCommGrpAlgPullback`) | Port | Compiles with only the header edits listed above. Needed for `diagFunctor` and `diagPullbackIso`. | Compare with host `GroupScheme.baseChange f := (Over.pullback f).mapGrp`: `baseChange f (Diag S M) ≅ Diag T M` in `Grp (Over T)`, from `diagPullbackIso`. |
| Scheme-side criterion "diagonalisable iff `Γ(G)` is spanned by group-likes" | `toric/Toric/GroupScheme/Diagonalizable.lean`@bef9a1f3, line 431 | Rewrite | The upstream proof is `sorry`. | Over a domain `R` and affine `G`: derive it from the proved Hopf criterion through Mathlib's affine anti-equivalence (`commHopfAlgCatEquivCogrpCommAlgCat`, `hopfSpec` in `AlgebraicGeometry/Group/Affine.lean`). Extra hypothesis: `Γ(G)` torsion-free over `R` (automatic over a field). The general base (SGA 3 VIII) stays out of scope. |
| Characters, cocharacters and the perfect pairing | `toric/Toric/GroupScheme/Character.lean`@bef9a1f3 (`Char`/`X(S,G) := HomGrp G 𝔾ₘ[S] S`, `Cochar`, `charCongr`, `cocharCongr`, `charDiag : X(Spec R, Diag (Spec R) G) ≃+ G`, `cocharDiag`, `charTorus`, `charTorusUnit : X(Spec R, 𝔾ₘ) ≃+ ℤ`, `cocharTorus`, `charPairing`, `isPerfPair_charPairing`) | Port (with the one-line fix) | The domain case `R = ℂ` gives `X*(S_ℂ) ≅ ℤ²` and `Hom(Gm, Gm) = ℤ` for the Deligne-torus milestone without new mathematics. | The host already has character functors (`Langlands.GroupScheme.Cartier.characters G : (Over S)ᵒᵖ ⥤ AddCommGrpCat`, `characterHomEquiv`) and cocharacters as `(Gm S).toGrp ⟶ G` (`CocharacterTransport`). Adapters: `X(S,G) ≃+ (Cartier.characters G).obj (op (Over.mk (𝟙 S)))` and Toric `Cochar` ≃ host cocharacters. Both go through the `Gm S ≅ 𝔾ₘ[S]` comparison above and the identity base change `testBaseChange`. |
| Tori over a field (non-split) | `toric/Toric/GroupScheme/Torus.lean`@bef9a1f3 (`IsTorusOver`: some separable field extension `L/k`, of any degree, over which the base change satisfies `IsSplitTorusOver`); `tauceti/TauCeti/AlgebraicGeometry/AffineGroupScheme/Torus.lean`, `.../MultiplicativeType.lean`@8428d621 (properties on `FiniteTypeAffineGroupSchemeCat` transported from Hopf algebras) | Adapt Toric's definition; use TauCeti only as a reference | Toric's shape matches the host after the bridge in row 1. The TauCeti files sit in another category, and the snapshot is not import-closed for them. Three of their direct imports are absent from it: `TauCeti.CategoryTheory.ObjectProperty`, `TauCeti.Algebra.AlgebraicGroup.Torus.Reductive` and `TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic` (`AffineGroupScheme/FiniteType.lean` and `AffineGroupScheme/Reductive/Basic.lean` are present). The transitive closure of `AffineGroupScheme.Torus` at 8428d621 is 223 TauCeti modules and 47,183 lines, and it imports one module absent from our Mathlib, `Mathlib.LinearAlgebra.TensorProduct.Lift`. No port test was run on it. | Host definition: a group scheme `G` over `Spec k` is a torus if, for some finite separable `L/k`, the host `IsSplitTorus` holds for the base change of `G` to `Spec L` (finite rank built in). Comparison with "split over `k^s`" or "split over `k̄`" (Milne AG 12.18) is a later theorem, not part of the definition. |
| Galois lattice of a torus | `tauceti/TauCeti/Algebra/AlgebraicGroup/CommHopfAlgCat/CharacterLattice/{Basic,Continuous,Functoriality,Torsion}.lean`, `.../GroupLikeEvaluation.lean`@8428d621 (`geometricCharacterGroup H := GroupLike k̄ (k̄ ⊗[k] H)`, Galois action, discrete topology and continuous action, `geometricCharacterFunctor` into `Rep`, torsion-freeness for smooth geometrically connected `H`, `evaluationIso`) | Port later, on the Hopf side, when the Galois-lattice unit starts; the closure compiles after four edits | This is the right shape (Hopf side, absolute Galois group, `Rep` functor). The snapshot is not import-closed for these roots. Five direct imports are absent: `TauCeti.Algebra.Bialgebra.GroupLike.{ScalarAut,Evaluation,Map,Torsion}` and `TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced` (`AlgebraicGroup.Connected.CommHopfAlgCat` and `AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat` are present). The transitive closure of the five roots at 8428d621 is 53 TauCeti modules and 9,398 lines: 16 in the snapshot and 37 more, fetched at the pin. It needs no module absent from our Mathlib. Port test in a private draft, all 53 files verbatim except for the edits below. Unchanged, record `c75e411b-2f95-4bd3-9e66-d2111661ac8a` has 10 errors in 3 modules: `Coalgebra/Convolution.lean:329` uses `AlgHom.convPostcomp`, absent from our Mathlib; at `Coalgebra/Subcoalgebra/Basic.lean:105`, `PartialOrder.ofSetLike` now takes the element type; `MonoidAlgebra/Basic.lean:180` uses `HasUniqueDiv`, absent from our Mathlib. Four edits: (1) add the element type `C` to `ofSetLike`; (2) delete the theorem `Module.Basis.convCoordEquiv_convPostcomp_mul` and (3) the instance `instHasUniqueDiv`, neither used elsewhere in the closure; (4) replace `IsConcreteLE.le_iff`, absent from our Mathlib, by `SetLike.le_def` in one `simp only` list at `Coalgebra/Subcoalgebra/Map.lean:89`. After (1)–(3), record `faeab0ed-987e-4a28-8f7c-4b596012a439` has 2 errors, both at that line. After all four, record `a2b0a485-f092-42f6-a69a-5a0f81589393` builds `CharacterLattice.{Continuous,Functoriality,Torsion}` and `GroupLikeEvaluation`, which import `CharacterLattice.Basic`, with no errors and no warnings. `evaluationIso_naturality` (record `0987b5ae-9375-488b-8cea-605ce3d31cab`) and `isAddTorsionFree_additiveCharacterGroup_of_smooth` (record `26bd2891-9c29-4a42-9b82-b52a8caec5f4`) depend only on `propext`, `Classical.choice` and `Quot.sound`. The code works on `CommHopfAlgCat k`, not on `Grp (Over S)`, so the port needs the bridge on the right. | Two separate steps. (i) Characters of an arbitrary affine group, a new lemma that needs no diagonalisability. Hopf side: for a commutative Hopf algebra `H` over a commutative ring `R`, the bialgebra maps `R[Multiplicative ℤ] →ₐc[R] H` correspond to `GroupLike R H` by the universal property of the group algebra. Send `φ` to `φ(t)`, which is group-like by `MonoidAlgebra.isGroupLikeElem_of` (`Mathlib/RingTheory/Bialgebra/MonoidAlgebra.lean:156`) and `IsGroupLikeElem.map` (`Mathlib/RingTheory/Coalgebra/GroupLike.lean:52`). Send `g` to `(liftGroupLikeBialgHom R H).comp (mapDomainBialgHom R (zpowersHom _ g))` (`MonoidAlgebra.lean:160` and `:83`). Both composites are the identity by `bialgHom_ext` (`:114`). Mathlib has no packaged equivalence. Host side, a separate comparison obligation: by the host `Gm.representableBy` (`Langlands/GroupScheme/Multiplicative.lean:161`), a homomorphism `G ⟶ (Gm S).toGrp` in `Grp (Over S)` is a unit `u ∈ Γ(G)ˣ` with `μ^*u = pr₁^*u · pr₂^*u`. For `G = Spec H` over `S = Spec R`, identifying `Γ(G ×_S G)` with `H ⊗_R H` turns this into `Δu = u ⊗ u`; then `ε u = 1` because `u` is a unit, so `u ∈ GroupLike R H`. Apply this with `R = k̄` and `H = k̄ ⊗_k Γ(G) = Γ(G_{k̄})`. For commutative `G`, compare further with the host `Cartier.characters` at `Spec k̄` (`Langlands/GroupScheme/Cartier/Characters.lean:18`). Mathlib's `liftMulEquiv` (`MonoidAlgebra.lean:384`) classifies only algebra maps `R[M] →ₐ[R] A`, i.e. units of `A` (points of `Gm`), not bialgebra maps, so it is not used. (ii) Reconstruction in the diagonalisable case, used only to identify `G_{k̄}` with `D(X*(G))`. TauCeti `evaluationIso` (`GroupLikeEvaluation.lean:30-38`) gives `k[GroupLike k H] ≅ H` under `[IsDomain k]`, `[Module.IsTorsionFree k H]` and the hypothesis that the group-like elements span `H`. For `H = k̄ ⊗_k Γ(G)` over the field `k̄`, the first two hold automatically. The third is Hopf diagonalisability (Toric `Bialgebra.isDiagonalisable_iff_span_isGroupLikeElem_eq_top`, `Hopf/Diagonalisable.lean:113`). It holds when `G_{k̄}` is diagonalizable, e.g. for a torus, and fails for a general affine `G` such as `𝔾ₐ`. Galois action on the host side: via `CocharacterTransport.descentBaseChangeIso` for `σ ∈ Aut(k̄/k)`, plus a proof that under (i) it matches TauCeti's action on `GroupLike k̄ (k̄ ⊗[k] H)`. For the Deligne milestone, only the action of complex conjugation on `X*(S_ℂ) ≅ ℤ²` is needed. That follows from the ported `charDiag` and host `CocharacterTransport` without TauCeti. |
| Weil restriction tori `R_{L/k} 𝔾ₘ` and permutation lattices (row by Worker 1107) | TauCeti at 8428d621, upstream only: these files are absent from the audit snapshot, which selected other modules. `tauceti/TauCeti/RingTheory/WeilRestriction/Basic.lean` (`WeilRestriction A B C`, `universalPoint`, `homEquiv : (WeilRestriction A B C →ₐ[A] T) ≃ (C →ₐ[B] B ⊗[A] T)` with naturality and `hom_ext`, `instFinitePresentation`, `map`, and for pushouts `baseChangeAlgEquiv` with `homEquiv_comp_baseChangeAlgEquiv`); `tauceti/TauCeti/Algebra/HopfAlgebra/WeilRestriction.lean` (`comul`, `counit`, the bialgebra and Hopf algebra instances, natural `pointsMulEquiv`); `tauceti/TauCeti/Algebra/AlgebraicGroup/MultiplicativeGroup/WeilRestriction.lean` (`multiplicativeGroupPoints : WithConv (WeilRestriction A B B[T;T⁻¹] →ₐ[A] T) ≃* (B ⊗[A] T)ˣ`, with `multiplicativeGroupPoints_naturality`); `tauceti/TauCeti/RingTheory/WeilRestriction/Smooth.lean` (`instFormallySmooth`, `instSmooth`). Hypotheses: `[Module.Finite A B] [Module.Projective A B]` throughout, and `[Algebra.FinitePresentation B C]` for the restricted algebra `C` (the Hopf file requires it of `H`). A finite field extension `L/k` satisfies them. Toric has no Weil restriction: its full tree at bef9a1f3 (98 entries) has no such file. Mathlib 5ed29652 and the host Library have none either. | **Port, then adapt** the algebra layer (restriction algebra, universal property, base change, Hopf structure, `𝔾ₘ` points, smoothness). **Rewrite** the splitting and lattice theorems on the host. | Closure of the four files at 8428d621: 16 TauCeti modules, 3,676 lines, no module absent from our Mathlib. Port test (private draft, all 16 files verbatim except two edits). Edit (1) replaces `MonoidHom.coe_ofClass` by `MonoidHom.coe_coe` twice in `Polynomial/Laurent/Basic.lean`, as in §4. Edit (2) deletes the theorem `Module.Basis.convCoordEquiv_convPostcomp_mul` in `Coalgebra/Convolution.lean`, the same edit as in the Galois-lattice row; nothing in the closure uses it. With edit (1) only, check `98444f82-8a37-4be4-a5f7-a87272266ea1` has 3 errors, all in `Coalgebra/Convolution.lean` lines 329–335 (`AlgHom.convPostcomp` is absent from our Mathlib). With both edits, check `2c5a369d-ab4c-46f2-abf5-5541eda80d05` builds all 16 modules with no errors and no warnings. `instSmooth` (record `508b3e2b-a10f-49d1-b07f-7ced253d7ec5`), `multiplicativeGroupPoints_naturality` (record `b8d61093-ec0c-4e06-91cd-5bc1c0bab528`) and `homEquiv_comp_baseChangeAlgEquiv` (record `2f19d004-0fed-4d44-871a-e79d0299c7bf`) depend only on `propext`, `Classical.choice` and `Quot.sound`. Scope of the source: it works with algebras and Hopf algebras over `A`, with points on commutative `A`-algebras (affine tests only), not with `Grp (Over S)`. It does not prove that `R_{L/k} 𝔾ₘ` splits over a Galois closure, its rank, or its character lattice. The separate file `AlgebraicGeometry/IdealSheaf/WeilRestriction.lean` is about Weil restriction of closed subschemes along finite locally free morphisms. It is not needed here. | Host adapter (new): for finite `L/k`, the group scheme over `Spec k` with underlying scheme `Spec (WeilRestriction k L L[T;T⁻¹])` and group law from the ported Hopf structure. Then the host point equivalence `(T ⟶ R_{L/k}𝔾ₘ) ≃* (L ⊗_k Γ(T, 𝒪_T))ˣ` for all test schemes. On affine tests it comes from `multiplicativeGroupPoints` and Mathlib's `algΓAlgSpecAdjunction`. Non-affine tests need an extra argument; one option is the Library's `Corepresented` model, as the Deligne torus does with `(QuadraticAlgebra S (-1) 0)ˣ`. Also: a comparison with the existing `DeligneTorus.groupScheme` for `ℂ/ℝ`. New mathematics on the host: for a Galois closure `K`, the base change of `R_{L/k}𝔾ₘ` to `K` is `∏_{Hom_k(L,K)} 𝔾ₘ`, via `baseChangeAlgEquiv` and `L ⊗_k K ≅ K^{Hom_k(L,K)}`. So the torus splits over `K` with rank `[L:k]`, and its character lattice is the permutation module `ℤ[Hom_k(L,K)]`. None of this is written. |
| Classification of tori by Galois lattices (row by Worker 1107) | TauCeti at 8428d621, upstream only (absent from the audit snapshot). `tauceti/TauCeti/Algebra/AlgebraicGroup/Torus/CharacterLattice/Equivalence.lean`: over a perfect field, the geometric character-lattice functor is an equivalence from coordinate Hopf algebras of tori to continuous integral Galois lattices (Milne 2017, Theorem 12.23 and Corollary 12.24). `tauceti/TauCeti/Algebra/AlgebraicGroup/GroupAlgebra/Galois/Torus.lean`: for finite Galois `L/k` and a lattice `M` with a `Gal(L/k)`-action, Galois descent of `L[M]` gives a torus split by `L`. | Not decided; assess when the Galois-lattice unit starts | Only the module docstrings were read. Closures at 8428d621: `Equivalence` has 175 TauCeti modules and 33,296 lines, and it imports one module absent from our Mathlib, `Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup`. `Galois/Torus` has 143 modules and 28,619 lines, with nothing missing. No port test was run. | If ported, these would supply the Galois-descent and lattice classification on the Hopf side. They would need the same host bridge as the Galois-lattice row. |
| Deligne torus: smooth, split over ℂ, not split over ℝ | none (host-specific) | Keep our own | Done on the host: statement 0d820015 (accepted in review), proof compiled privately with the standard axioms (record `7b03aa26`). | None. |

### Toric results already upstream in pinned Mathlib 5ed29652

Present in Mathlib (do not port; import them):

- `AlgebraicGeometry/Group/Affine.lean`: `bialgSpec`, `hopfSpec`, and
  `commHopfAlgCatEquivCogrpCommAlgCat` (also in `Algebra/Category/CommHopfAlgCat.lean`).
- `Algebra/Category/CommBialgCat.lean`, `CommHopfAlgCat.lean`.
- `RingTheory/Bialgebra/MonoidAlgebra.lean`: `mapDomainBialgHom`, `liftGroupLikeBialgHom`,
  `span_isGroupLikeElem`, `isGroupLikeElem_iff_mem_range_single_one` (over a domain), the
  bialgebra-hom classification `mapDomainOfBialgHom` behind it, `toMultiplicativeBialgEquiv`,
  `liftMulEquiv`, and the Laurent-polynomial bialgebra structure;
  `RingTheory/HopfAlgebra/MonoidAlgebra.lean`.
- `RingTheory/Coalgebra/GroupLike.lean`: `linearIndep_groupLikeVal`;
  `RingTheory/HopfAlgebra/GroupLike.lean`: `GroupLike R A` with its `CommGroup` instance.
- `CategoryTheory/Monoidal/Cartesian/Over.lean`: `Over.prodComparisonIso_pullback_*`;
  `specULiftZIsTerminal` (`AlgebraicGeometry/Limits.lean`).
- Galois side: `Field.absoluteGaloisGroup`, `Rep.ofMulDistribMulAction`.

Not in Mathlib (Toric only): `commMonAlg`, `commGrpAlg`, `specCommMonAlgPullback`, `Diag`,
`diagFunctor`, `IsDiagonalisable` (Hopf and scheme), `IsSplitTorusOver`, `IsTorusOver`,
`SplitTorus`, `MvLaurentPolynomial`, `Char`/`Cochar` and the pairing. No root-system or Weil
restriction material for group schemes is involved on this side.

## 7. Root data, root systems and Cartan subalgebras in our Mathlib (Worker 1107)

| Unit | Mathlib file at `5ed29652` | Decision | Reason |
|---|---|---|---|
| T1. Root datum of a split reductive group, with Weyl group and bases | `Mathlib/LinearAlgebra/RootSystem/Defs.lean` line 109: `RootDatum X₁ X₂ := RootPairing ι ℤ X₁ X₂`; `Base.lean` line 70 (`RootPairing.Base`); `WeylGroup.lean` line 56 (`weylGroup`); `Hom.lean` (`RootPairing.Equiv`, `Aut`); `Reduced.lean`; `Finite/*` | **Reuse** as the target structure | Mathlib defines `RootDatum` as a root pairing over ℤ, which is the intended target. The group-to-root-datum construction (character lattice of a split maximal torus, roots, coroots) remains Library work. A Galois action on based root data should take values in `RootPairing.Aut` and preserve a `Base`. Finiteness of the index type is a separate mixin, as the audit notes. |
| T2. Root system of a semisimple Lie algebra relative to a Cartan subalgebra | `Mathlib/Algebra/Lie/Weights/RootSystem.lean` line 414: `LieAlgebra.IsKilling.rootSystem`. It assumes a field `K` with `CharZero K`, finite dimension, `IsKilling K L` and a splitting Cartan subalgebra `H`. Its value is `RootPairing H.root K (Dual K H) H`, with `IsCrystallographic` and `IsReduced` instances. `Mathlib/Algebra/Lie/CartanSubalgebra.lean` line 50: `LieSubalgebra.IsCartanSubalgebra`. | **Not used for definitions.** A characteristic-zero comparison theorem is possible later. | The construction needs characteristic 0 and a nondegenerate Killing form, so it excludes positive characteristic and every reductive group with a nontrivial central torus. It produces a root system with coefficients in `K`, attached to the Lie algebra rather than to the character lattice of a torus. The Library's `Langlands.AbelianScheme.Lie` has no bracket. `MatrixRepresentationDifferentialLie` gives brackets only for differentials of GL_n representations. Later bridge, for split semisimple `G` over a field of characteristic 0: Lie(T) is a splitting Cartan subalgebra of Lie(G), and the Lie root system is the scalar extension of the group root datum (`RootSystem/BaseChange.lean`). |

## 8. What remains open

- The adapters of D2 have not been written. The non-affine-test step (b) is the
  main new argument on the port route.
- Of the dynamic-subgroup closures, only the 8-module points layer was
  compiled. Each further closure needs its own focused build and axiom check
  before any port is staged.
- The torus-side adapters of §6 have not been written either: the wrapper of
  Toric's `Diag` as a `GroupScheme`, the comparison `Gm S ≅ 𝔾ₘ[S]` with its
  natural points equivalence, and the bridge between the host `IsSplitTorus`
  and Toric's `IsSplitTorusOver`. The scheme-side criterion at Toric
  `Diagonalizable.lean` line 431 is `sorry` upstream and must be proved anew.
  The 53-module TauCeti character-lattice closure compiles after four edits,
  but the character bridge (i) of the §6 Galois-lattice row and the comparison
  of Galois actions are not written.
- The 16-module TauCeti Weil-restriction closure compiles after two edits, but
  the host group scheme `R_{L/k} 𝔾ₘ`, its point equivalence on non-affine
  tests, its splitting over a Galois closure and its permutation character
  lattice are not written.
- A port is staged as Library modules that keep the TauCeti or Toric headers
  and the Apache-2.0 attribution. Each needs independent review of its
  mathematical content and of its adapter theorem.
