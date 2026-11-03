# General Aubert support category, corrected filtration and consequence targets: source map

This note maps the support category `Alg({I})`, the corrected support filtration
of the Jacquet modules `r_I(E_J)`, its graded targets, and the finite-length and
irreducible consequence targets (Aubert's Corollaire 3.9) of the general Aubert
program to their Lean/Markdown pairs. It records the source passages behind each
declaration, which declarations are constructions or proved laws and which are
proposition targets, and the remaining prerequisites with their owners.

Author: Worker 379, task `0a1bd7fb-66c2-4dcc-a3c8-6619f6fa10b4` revision 1, with
first executor Worker 194, for parent `46df6a68-5db4-4428-8044-05151d6ce1f6`
(Worker 76). Generic-helper reuse update: Worker 76, checked on 3 November 2026
against Library `6eec947454b4466fab00fb115b09f2dc49fe158b`.
Worker 194's companion note
`notes/aubert/smooth-complex-construction-source-map.md` covers the actual
smooth complex, its terminal cokernel `E#`, the corrected Theorem 3.6 target, the
p.4690 terminal-Jacquet comparison, the structural ownership table and the
classification import audit. That note may not yet be published. This note does
not repeat those parts. The
[general source map](general-program-source-map.md) gives the overall correction
policy and the [Chapter V ledger](../renard/chapter-v-structural-inputs.md)
defines the S rows used below.

None of the targets below is proved here. A target is a `Prop`-valued definition
of generic subgroup and Weyl data. It is meant to hold for the standard families
of a connected reductive group, and it can fail for arbitrary data of the same
shape. Proving the targets belongs to the parent task.

## Publication-status snapshot (2 November 2026)

This section records the status at submission against Library
`4103487976e26033768519d7c8e53adf6d10c898`. Later publications are not
reflected in this snapshot.

| Module (under `Langlands/Representation/`) | Candidate | Kind | Status |
| --- | --- | --- | --- |
| `Aubert/RankOrderedSupports` | `cee5aa83-cc9e-4216-b953-31a583b26877` | definition | published |
| `Aubert/General/SupportCategory`, `…/SupportCategoryStatements`, `…/SupportCategoryReductions`, `Category/IrreducibleSubquotientExistence` | `19947d93-60c4-401f-bdb7-146008333dca` | definition | published |
| `Aubert/General/CorrectedFiltration` | `1c48a424-f7e9-4aec-b326-4d81e098fbf0` | definition | published (Library `4103487976e26033768519d7c8e53adf6d10c898`) |
| `Aubert/General/SharpConsequenceStatements` | `6da10c90-35c3-45d0-a60b-cc0ee8169807` | statement | approved by independent review (Reviewer 9445), not yet in the Library |
| `Aubert/General/CorrectedFiltrationStatements` | `bd7db6bd-c5d0-4a71-bdc3-dbd14b3f789b` | statement | approved by independent review (Reviewer 9540), not yet in the Library |

The last two rows were candidates, not accepted Library results, at that
snapshot. Check the current Library before relying on their names.
The later generic-helper check below does not update this historical status
table or establish any general Aubert target.

## Conventions

- **Index and families.** `ι` is a finite, linearly ordered type of simple
  roots and `S = Finset.univ`. `P M U : Finset ι → Subgroup G` are the standard
  parabolic, Levi and unipotent-radical families, with `P I = M I ⋉ U I`
  (`h`), closed radicals (`hclosed`, or `hU` in the support modules), closed
  Levis (`hM`), and the Levi-in-Levi decompositions `hL`. For the complex,
  `P` is monotone, `U` is antitone and every radical has unimodular modulus
  (`hδ`). The intended data are the published rational-point families
  `Langlands.Aubert.General.RationalPointFamily.parabolic`, `levi` and
  `unipotent`. Proving that they satisfy these hypotheses is the structural
  work listed in Worker 194's table.
- **Removed-root indexing.** The complex terms use Worker 194's
  `StandardComplex.removedFamily`. A term is indexed by the removed roots `s`,
  with `J = S \ s`. Hence `CorrectedFiltration.term P M U h hclosed E s` is
  `E_J = i_J r_J E`, and `transition … hst` for `s ⊆ t` is the actual map
  `φ^J_{J'}` with `J' = S \ t`.
- **Association.** `IsAssociate : Finset ι → Finset ι → G → Prop` is a
  parameter. Every association test pairs it with the membership condition
  `∀ x, x ∈ M J ↔ n⁻¹ * x * n ∈ M I`, that is `M J = n (M I) n⁻¹`. Two
  instantiations are faithful. The first is "`n` represents `v ∈ W` with
  `v(I) = J`", the erratum's `v(I) ⊂ S ∩ Φ⁺`. The second is the trivial
  relation `fun _ _ _ => True`. It is equivalent to the first given the
  structural fact that standard Levis conjugate in `G` are `W`-associated
  (rows S08, S10, S15, S16). The pairing is needed because the trivial relation
  carries no information without the membership condition.
- **Conjugation direction.** `conjugationFunctor g hMN`, with
  `hMN : ∀ x, x ∈ N ↔ g⁻¹ * x * g ∈ M`, sends representations of `M` to
  representations of `N = g M g⁻¹` by `x ↦ σ(g⁻¹ x g)`. In the support category
  it realizes `Ad(v)(σ)` on `L_{v(I)}`. In the filtration targets, `m ∈ N_G(T)`
  lifts `w⁻¹` and `hK : ∀ x, x ∈ M I ↔ m⁻¹ * x * m ∈ M K`, so
  `M K = m⁻¹ (M I) m = w L_I w⁻¹`. Then `conjugationFunctor m hK` is Aubert's
  `Ad(w⁻¹)`, from representations of `L_K = w L_I w⁻¹` to representations of
  `L_I`.
- **Weyl group.** `Group.RelativeWeyl.Weyl T = N_G(T)/Z_G(T)` is the
  full-centralizer quotient, following Renard V.4.1. The filtration assumes it
  is finite and supplies a Coxeter system `cs : CoxeterSystem Mx (Weyl T)`
  indexed by `ι`. The parabolic subgroups `W_J` are
  `Group.RelativeWeylIndexing.standardSubgroup cs J`. The comparison of `cs`
  with the actual relative roots is structural (rows S09, S13, S17, S18).
- **Filtration order.** Aubert's `Θ` consists of the sets `θ ⊆ W` that contain
  every element longer than one of their members. The Lean filtration grows
  with its index. `Support.rankOrderedSupport cs.length i` is the set of the
  first `i` elements in decreasing length order, and step `i` is built from its
  two-sided core `θ_i'`. The erratum's decreasing chain `θ_1 = W ⊃ … ⊃
  θ_{t+1} = ∅` is the same chain read backwards.
- **Universes.** Support and filtration objects have carriers in
  `Type (max uG uV)`. The Corollaire 3.9 targets use `Type (max uI uG uV)`, the
  universe of `StandardComplex.sharpObject.{uI, uG, max uI uV}`, so that `E`,
  `E#` and `(E#)#` lie in one category.
- **No finite length.** `Alg({I})` has no finite-length premise, and neither do
  the filtration or the support targets. The filtration is finite because the
  Weyl group is finite, not because `E` has finite length. Finite length enters
  only in `SharpFiniteLengthTarget` and `SharpClassFormulaTarget`, through the
  exact finite-length Grothendieck group.

## Declaration map

### Generic layers (no reductive structure)

| Declaration | Content | Source |
| --- | --- | --- |
| `Langlands.Aubert.Support.IsRankUpper` | Aubert's class `Θ` for a rank function `W → ℕ` | erratum p.4687 |
| `…Support.rankOrderedList`, `rankOrderedEquiv`, `rankOrderedSupport`, `rankOrderedElement` | Decreasing-rank enumeration of a finite type and its prefixes `θ_i`. The prefixes are monotone, start at `∅`, end at `univ`, and are in `Θ` (`rankOrderedSupport_isRankUpper`). | erratum p.4689 chain `θ_i − θ_{i+1} = {w_i}` |
| `…Support.modifiedRankSupport` | Largest left-`H`, right-`K`-invariant subset of a prefix, via the published `twoSidedCore` | BJ p.161, two-sided `θ'` |
| `modifiedRankSupport_step`, `_succ_ne_iff`, `_succ_diff`, `_succ_minimal`, `_succ_eq` | The core changes at step `i` exactly when the new element lies in it. The change is its whole double coset, and the new element has minimal rank in that coset. | BJ p.161 minimality argument |
| `Langlands.SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` | Every nonzero smooth representation of any topological group has an irreducible subquotient in the same carrier universe. No finite length is assumed. | Renard III.1.4, end remark, p.60 |
| `Langlands.Aubert.General.subtype_mkQ_isShortExact` | The inclusion and the quotient map of a subrepresentation form a short exact sequence. | generic |
| `Langlands.Aubert.General.jacquet_subsingleton_of_isSubquotient` | Vanishing of a Jacquet module passes to subquotients when `U` is a limit of compact subgroups. Uses the adapter's `jacquetFunctor_map_isShortExact`. | BZ exactness of `r` |

### Support category (`Aubert/General/SupportCategory`, namespace `Langlands.Aubert.General`)

Definitions:

| Declaration | Content | Source |
| --- | --- | --- |
| `IsCuspidalFor` | Vanishing of every normalized Jacquet module along a family of decompositions | Aubert p.2181 after BZ §2.4 |
| `IsCuspidal` | `r^G_{L_I}(π) = 0` for every `I ⊊ S` | Aubert p.2181 |
| `IsLeviCuspidal J hM hJ σ` | Cuspidality inside `M J`, for its parabolics `P K ∩ M J` with `K ⊊ J` | Aubert p.2181 for `L_J` |
| `IsInCuspidalSeries` | `𝔈(I)`: `π` is irreducible and a subquotient of `i^G_{L_I}(σ)` for some irreducible cuspidal `σ` of `L_I` | Notation 1.6, p.2181 |
| `IsInSupportCategory IsAssociate I hM hI E` | `Alg({I})`: every irreducible subquotient of `E` is a subquotient of `i^G_{L_J}(Ad(n)σ)` for an association `(J, n)` and some irreducible cuspidal `σ` of `L_I` | erratum p.4687 |

Proved intrinsic laws: `IsInSupportCategory.of_isSubquotient`, `.of_iso` and
`.of_subrepresentation_quotient` (closure under subquotients, isomorphism and
extensions); `isInSupportCategory_inducedConjugate`;
`conjugationFunctorOneIso`; `isInSupportCategory_cuspidalInduction` and
`IsInCuspidalSeries.isInSupportCategory`, both under `IsAssociate I I 1`.
These laws use only the definitions and generic subquotient facts.

Targets (`SupportCategoryStatements`):

| Target | Assertion | Source |
| --- | --- | --- |
| `CuspidalSeriesExistenceTarget` | Every irreducible `π` lies in some `𝔈(I)`. | Renard VI.2.1 Corollaire, p.139 |
| `CuspidalSupportAssociationTarget` | If `π` lies in two cuspidal series, the cuspidal data are associated, with `σ' ≅ Ad(n)σ`. | Renard VI.5.4 (iv)⇒(i), pp.173–174 |
| `SupportCategoryAssociationInvarianceTarget` | `Alg({I})` depends only on the association class of `I`. | erratum p.4687 |
| `SupportCategoryIrreducibleJacquetDetectionTarget` | An irreducible member of `Alg({I})` has a nonzero Jacquet module along *some* associated `L_J`, not necessarily along every one. | proof of Renard VI.5.4, p.174 |
| `SupportCategoryZeroDetectionTarget` | A member of `Alg({I})` whose Jacquet modules along all associated `L_J` vanish is zero. | erratum p.4687 |
| `SupportCategoryExactnessDetectionTarget` | For `B ∈ Alg({I})`, exactness of `A → B → C` at `B` is equivalent to exactness of all associated Jacquet sequences. | erratum p.4687, "Par définition de la catégorie Alg({I})" |
| `SupportCategoryInductionJacquetTarget` | `Alg({I})` is stable under `i_K ∘ r_K`. | Renard VI.7.2 Théorème p.182, VI.7.3 Proposition p.185 |
| `SupportCategoryJacquetVanishingTarget` | If no `L_J` with `J ⊆ K` is associated to `L_I`, then `r_K` vanishes on `Alg({I})`. | Renard VI.5.3 (i) p.173, VI.7.3 p.185 |
| `SupportCategoryDecompositionTarget` | Every smooth `E` is an internal direct sum of subrepresentations `S I ∈ Alg({I})`. Uniqueness is not asserted. | Renard VI.7.2 Théorème p.182 |

`SupportCategoryReductions` proves one implication between targets:
`supportCategoryZeroDetection_of_irreducibleJacquetDetection` derives zero
detection from irreducible detection when every `U J` is a limit of compact
subgroups. Under the same hypothesis, exactness detection reduces to zero
detection by exactness of `r`. That reduction has not been formalized.

### Corrected filtration (`Aubert/General/CorrectedFiltration`, namespace `Langlands.Aubert.General.CorrectedFiltration`)

| Declaration | Content | Source |
| --- | --- | --- |
| `functionSupport σ X` | Smooth induced functions whose nonzero set lies in `X`. Since these functions are locally constant, this matches "support compact contenu dans `G_θ`" when `P_J\G` is compact. | erratum pp.4687–4688 |
| `jacquetImage hQ hN A S hS` | Image of a `Q`-stable subspace in the normalized Jacquet module, as an `L`-subrepresentation | erratum p.4688, `Ẽ^θ_{J,I}` as an image in `r_I(Ẽ_J)` |
| `cellSupport T B Q θ`, `IsBruhatCover T B Q` | `⋃_{w∈θ} B n_w Q` over all lifts `n_w ∈ N_G(T)`; the covering hypothesis `G = ⋃ B n Q` | erratum p.4687, `G_θ := ⋃_{w∈θ} B w P_I`; rows S13, S16 |
| `modifiedSupport cs J I i` | BJ's two-sided `θ_i'` for `W_J`, `W_I` and Coxeter length | BJ p.161 |
| `mem_modifiedSupport_succ_iff` | `θ_i'` changes at `i` exactly when the `i`-th element is minimal in `W_J w W_I`. Uses the published `minimalRepresentativeUnique_proof`. | BJ p.161 |
| `term`, `transition` | `E_J` and `φ^J_{J'}` in removed-root indexing (Worker 194's complex) | Aubert (3.5), p.2187 |
| `groupSupport`, `inductionStep`, `step` | `G_{θ_i'}` with `B = P ∅`; functions supported there; their image in `r_I(E_J)` | erratum pp.4687–4688 |
| `step_monotone`, `step_zero`, `step_length` (under `IsBruhatCover T (P ∅) (P I)`) | The steps increase, start at `⊥` and end at `⊤`. | erratum p.4689 chain endpoints |
| `transition_mem_inductionStep`, `transition_mem_step` | The actual maps `r_I(φ^J_{J'})` preserve every step. | erratum p.4689, "elles respectent la filtration par Θ" |
| `step_succ_eq` | The step does not change when the new element is not minimal in its double coset. | BJ p.161 |

Targets (`CorrectedFiltrationStatements`, candidate `bd7db6bd`, approved):

| Target | Assertion | Source |
| --- | --- | --- |
| `CorrectedGradedVanishingTarget` | For `E ∈ Alg({I})`, suppose `step (i+1) ≠ step i` in `r_I(E_J)`. Then for every lift `m` of `w⁻¹` there is a standard `K ⊆ J` with `M K = m⁻¹ (M I) m`. | erratum pp.4688–4689: `w L_I w⁻¹ ⊂ L_J` and "w(I) est formé de racines simples et est contenu dans J" |
| `CorrectedGradedTransitionTarget` | Fix `w`, a lift `m` of `w⁻¹` and `K` as above. Then there are surjections `β_s` from step `i+1` onto `Ad(w⁻¹)(r_K E)`, defined for every surviving `s` (`K ⊆ S \ s` and `w` minimal in `W_J w W_I`). Each has kernel step `i`, and `β_t ∘ r_I(φ) = β_s` for surviving `s ⊆ t`. | erratum p.4689 (isomorphism onto `Ad(w⁻¹)∘r^G_{wL_Iw⁻¹}(E)`), p.4690 (transitions are the identity up to sign); BJ pp.161–162 |

The transition target fixes no integral formula for `β_s`. The erratum's
formula `f ↦ (l ↦ ∫ f(wul) du)` is one way to prove it. The sign of the
graded transition is carried by the differential of the complex, not by `β`.

### Consequences (`Aubert/General/SharpConsequenceStatements`, candidate `6da10c90`, approved)

`E#` is `StandardComplex.sharpObject … E I`, the cokernel at removed-root
degree `|S| − |I|`. The definitions of `E#` and the corrected Theorem 3.6
target `CorrectedTheorem36Statement` are Worker 194's.

| Target | Assertion | Source |
| --- | --- | --- |
| `SharpFiniteLengthTarget` | `E` has finite length ⇒ `E#` has finite length. | derived; Renard VI.6.2 p.178, VI.6.4 p.179 |
| `SharpClassFormulaTarget` | For finite-length `E ∈ Alg({I})`: `alternatingOperator … hfl [E] = (-1)^{|I|} • [E#]`. | Corollaire 3.9 (a), p.2189; erratum p.4690 |
| `SharpSupportRetentionTarget` | `E ∈ Alg({I})` ⇒ `E# ∈ Alg({I})`. | derived (termwise support and closure laws) |
| `SharpIrreducibleTarget` | `E ∈ 𝔈(I)` ⇒ `E#` is irreducible, hence nonzero. | Corollaire 3.9 (b), p.2189 |
| `SharpCuspidalSeriesTarget` | `E ∈ 𝔈(I)` ⇒ `E# ∈ 𝔈(I')` for some associated `I'`. | derived, used by (c) |
| `SharpInvolutionTarget` | `E ∈ 𝔈(I)` ⇒ `Nonempty ((E#)# ≅ E)`, with both cokernels taken at the same `I`. | Corollaire 3.9 (c), p.2189 |

Aubert states Corollaire 3.9 for `E ∈ 𝔈(I)`. The class formula target extends
(a) to finite-length members of `Alg({I})`, as erratum p.4690 does. Aubert's
proof of (b) already applies (a) to a possibly reducible induced
representation. Taking `(E#)#` at the same `I` is faithful because
`sharpObject` depends on `I` only through `|S| − |I|`, and associated
standard subsets have equal cardinality.

## Intended proof route (derived, for the parent's proofs)

This is the route of the erratum with the Ban–Jantzen repair, written in terms
of the declarations above. It is guidance, not a claim that any step is proved.

1. `SupportCategoryExactnessDetectionTarget` reduces `CorrectedTheorem36Statement`
   to exactness of the Jacquet sequences `r_I` of the complex along associated
   `I` (erratum p.4687).
2. Each `r_I(E_J)` carries the finite filtration `step`. It runs from `⊥` to
   `⊤` (`step_zero`, `step_length` under `IsBruhatCover`), and the differentials
   preserve it (`transition_mem_step`). The published
   `Langlands.FiniteFiltered.range_eq_ker_of_graded_exact` and
   `Langlands.FiniteFiltered.injective_of_graded_injective` supply the generic
   lifting step, with the hypotheses detailed below. The general application
   still needs degreewise filtrations, identification of their actual induced
   quotient differentials, and graded exactness or injectivity in the required
   degrees. Termwise filtration preservation alone does not establish these.
3. In the graded complex at `w`, only minimal `w` contribute (`step_succ_eq`),
   and only targets `J ⊇ w(I)` contribute (`CorrectedGradedVanishingTarget`).
   The surviving pieces are `Ad(w⁻¹)(r_K E)` with identity transitions
   (`CorrectedGradedTransitionTarget`). The graded complex is therefore that
   module tensored with the Koszul complex of `S_w − w(I)`, shifted. It is
   acyclic except when `S_w = w(I)`, where only the terminal term survives
   (erratum p.4690).
4. For finite-length `E`, exactness before the terminal degree, termwise finite
   length and an Euler-characteristic identity in the exact Grothendieck group
   give `SharpClassFormulaTarget`. The terms with `r_J E = 0` vanish by
   `SupportCategoryJacquetVanishingTarget`.
5. Corollaire 3.9 follows Aubert p.2189, in this order. Theorem 1.7 is the
   sibling task's (`e3d69272`): (2) is `InductionCompatibilityStatement`,
   (3) is `InvolutivityStatement` and (4) is `CuspidalEigenvalueStatement`.
   - **(b), `SharpIrreducibleTarget`.** Let `E ∈ 𝔈(I)` be a subquotient of
     `i_I(σ)` with `σ` irreducible cuspidal, and let `E_1, …, E_n` be the
     irreducible constituents of `i_I(σ)`. All of them lie in `Alg({I})`
     (`isInSupportCategory_cuspidalInduction`,
     `IsInSupportCategory.of_isSubquotient`) and have finite length.
     `SharpClassFormulaTarget` for `i_I(σ)`, with Theorem 1.7 (2) and (4),
     gives Aubert's (3.10): `[(i_I σ)#] = (-1)^{|I|} D_G [i_I σ] = [i_I σ]`,
     a class of length `n`. The same target for each `E_k`, with
     `SharpFiniteLengthTarget` for `E_k#` and additivity of `D_G`, gives
     `[(i_I σ)#] = [E_1#] + … + [E_n#]`. Each `E_k#` is nonzero because
     `D_G` is injective by Theorem 1.7 (3). Aubert leaves this step
     implicit. So `n` nonzero classes of actual representations add up to a
     class of length `n`, and every `E_k#` is irreducible. This argument
     assumes no irreducibility of any output and does not use
     `SharpCuspidalSeriesTarget`.
   - **`SharpCuspidalSeriesTarget`, after (b).** `SharpSupportRetentionTarget`
     puts `E#` in `Alg({I})`. By (b), `E#` is irreducible, so it is its own
     irreducible subquotient. It is therefore a subquotient of
     `i_{I'}(Ad(n)σ)` for an association `(I', n)`. Conjugation preserves
     irreducibility and cuspidality, so `E# ∈ 𝔈(I')`.
   - **(c), `SharpInvolutionTarget`.** By `SharpCuspidalSeriesTarget`, (b)
     applies to `E#`, so `(E#)#` is irreducible. For actual standard
     families `|I'| = |I|`, so the cokernel at `I'` is the cokernel at `I`.
     `SharpClassFormulaTarget` for `E` and for `E# ∈ Alg({I})` and Theorem
     1.7 (3) give `[(E#)#] = (-1)^{|I|} D_G [E#] = D_G D_G [E] = [E]`. Two
     irreducible representations with the same class in the finite-length
     Grothendieck group are isomorphic, so `(E#)# ≅ E`. The generic final
     implication is already published as
     `Langlands.SmoothRep.ofRepresentation_eq_irreducible_iff`, followed by
     `Langlands.SmoothRep.mkIso`. Its scope and the remaining double-sharp
     obligations are detailed below.

## Published generic helpers and remaining applications

The following reuse check concerns declarations in Library
`6eec947454b4466fab00fb115b09f2dc49fe158b`, separately from the historical
publication table above. Both Lean/Markdown pairs were read and their complete
declaration types checked. These are generic algebraic results, not proofs of
the general Aubert targets.

- [Finite filtered exactness](../../Langlands/Representation/Filtration/FiniteFilteredExactness.md)
  constructs the actual adjacent quotients `FiniteFiltered.Graded` and the
  induced maps `FiniteFiltered.gradedMap`. For maps `f : A →ₗ[R] B` and
  `g : B →ₗ[R] C` preserving submodule families `S,T,U`,
  `range_eq_ker_of_graded_exact` assumes `Monotone S`, `T 0 = ⊥`,
  `T n = ⊤`, the actual identity `g (f a) = 0`, and equality of the range
  and kernel of these induced quotient maps in every grade `i < n`.
  It concludes `LinearMap.range f = LinearMap.ker g`. It needs no zero or
  full endpoints for `S` or `U`. The injectivity theorem assumes preservation,
  `S 0 = ⊥`, `S n = ⊤` and injectivity of the actual graded maps for
  `i < n`; it needs no monotonicity of either family or endpoints for `T`.
  Both results work over any commutative ring, with independent module
  universes and no finite-length premise.
- [Irreducible class detection](../../Langlands/Representation/Smooth/IrreducibleClassDetection.md)
  proves `Langlands.SmoothRep.ofRepresentation_eq_irreducible_iff`: for actual
  smooth representations `A,τ`, with supplied finite-length proofs for both
  and an irreducibility proof for `τ`, equality of their canonical exact
  Grothendieck classes is equivalent to
  `Nonempty (A.representation.Equiv τ.representation)`. The coefficient field,
  group topology and carrier universe are arbitrary and independent.
  [The smooth-category constructor](../../Langlands/Representation/Category/Basic.md)
  `Langlands.SmoothRep.mkIso` converts such an equivariant linear equivalence
  to an actual categorical isomorphism. This does not assert that equal
  classes distinguish arbitrary finite-length representations.

For the filtration application, the existing GL adapter
[`CorrectedJacquetCutFiltration`](../../Langlands/Representation/Aubert/CorrectedJacquetCutFiltration.md)
shows how `degreeDifferential_exact_of_correctedGraded` and
`degreeDifferential_injective_of_correctedGraded` use the first helper. Its
GL-specific degree filtrations and comparisons do not supply the missing
general ones. The actual general graded identifications, differential
comparisons and support detection remain obligations of
`RationalCorrectedTheorem36Statement`, in successor task
`613611a4-9c0e-43e3-82aa-f91d2044cfe2`. No terminal-vanishing conclusion or
finite-length restriction on its smooth input follows from this reuse.

For double sharp, one can take `A = (E#)#` and `τ = E` only after proving
finite length and the exact equality `[(E#)#] = [E]` for the actual cokernels.
The helper then gives the object isomorphism; it does not construct those
cokernels, establish that equality or provide a natural isomorphism of
functors. Those application obligations remain in
`RationalSharpInvolutionStatement`, successor task
`9d570c9e-e376-4437-8d15-3cbe9e9a0027`, with the support, class-formula and
operator-involution inputs of the route above. Neither generic helper uses a
parabolic, Aubert or representation-classification theorem.

These reuse locations do not change either successor's exact target or its
hypothesis scope. Any additional Coxeter, Bruhat or structural inputs needed
by this proof route must be derived, rather than appended to the proposition.

## Prerequisites and owners

| Prerequisite | Where it enters | Owner |
| --- | --- | --- |
| Proofs of all targets in this note and of `CorrectedTheorem36Statement`, including the actual general applications of the published generic helpers | the parent task and its focused proof successors | Worker 76, `46df6a68-5db4-4428-8044-05151d6ce1f6` |
| Theorem 1.7 and the geometric lemma for the general operator (`InvolutivityStatement`, `JacquetCompatibilityStatement`, `InductionCompatibilityStatement`, `CuspidalEigenvalueStatement`) | Corollaire 3.9 (b), (c); graded identification | Workers 165/1186, `e3d69272-2599-4a08-a934-cb11f2493e30` |
| Normalized functors, exactness on smooth and finite-length sequences, `conjugationFunctor`, `alternatingOperator` | all modules | Workers 23/1180, `593ef603-6672-4424-976c-14e11e920d9c` (published adapters) |
| Bruhat covering `IsBruhatCover T (P ∅) (P I)`, a Coxeter system on `N_G(T)/Z_G(T)` matching the actual roots, the `W`-association of conjugate standard Levis, and `IsLimitOfCompactSubgroups (U J)` | `step_length`, the targets, `SupportCategoryReductions` | structural rows S08–S10, S13, S15–S18, S20–S22, with owners as in Worker 194's structural table |
| Renard Chapter VI cuspidal-support theory: existence, association, Jacquet detection and vanishing, Bernstein decomposition, finite length of `i` and `r` | `SupportCategoryStatements`, `SharpFiniteLengthTarget` | parent proof plan. On 2 November 2026 the Library's `Representation/CuspidalSupport` modules treated only the product (block) Levis of `GL_n`; no development for general standard families was found. |

## Classification

No declaration in this note has a classification premise. As for Worker 194's
modules, the imports reach classification modules. `SupportCategory` imports
`Category.ConstituentDichotomy`, which imports
`Classification.SupercuspidalSupport`. Import reachability neither shows that a
classification theorem is used nor that none is. If a later proof follows
Ban–Jantzen Proposition 4.1 (3) (p.158, which uses Langlands classification,
linear independence of characters and the geometric lemma), it must record
that dependency.

## Replaced and corrected source passages

- Aubert 1995, Proposition 3.2 (p.2186): its proof is withdrawn by the erratum
  (p.4687, "je ne sais pas si cette proposition est vraie"). Neither the
  proposition nor the original proof of Theorem 3.6 (p.2188) is used.
- Erratum pp.4688–4689 forms `θ'` as the largest member of `Θ_J` (left
  `W_J`-invariance only) contained in `θ`. It is replaced by
  the Ban–Jantzen two-sided `θ'` (BJ p.161, "a minor correction"), implemented
  by `modifiedRankSupport` and `modifiedSupport`.
- On erratum p.4689, the sentence saying that the elements of `θ_{i+1}` (and
  hence of `θ_i`) have length "inférieure" to that of `w` has its direction
  reversed relative to the definition of `Θ`. The formalization uses the
  definition: prefixes in decreasing length order.
- BJ p.161 justifies `W_J w W_I ⊂ θ_i'` "using θ_i' ≠ θ_i". The needed fact is
  `θ_i' ≠ θ_{i+1}'`, the case distinction of `modifiedRankSupport_succ_ne_iff`.
- BJ p.160 calls the complex ending in `Ẽ_∅ → 0` exact. The formalization
  keeps the erratum's sequence (`*`), which ends at `|J| = |I|` with no final
  zero, so the terminal homology `E#` is retained.

## Registered sources and direct reading

All hashes were recomputed on 2 November 2026. The passages listed were read in
the originals for this note and its modules.

| Source | SHA-256 | Passages (printed / one-based PDF) |
| --- | --- | --- |
| `aubert-1995-duality` | `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693` | pp.2180–2181 / 2–3 (W, `L_I`, Definition 1.5, Notation 1.6, cuspidality, Theorem 1.7); p.2186 / 8 (Proposition 3.2); p.2187 / 9 ((3.5), Theorem 3.6); p.2189 / 11 (Corollaire 3.9 and proof) |
| `aubert-1996-duality-erratum` | `d76b3ef9ea2310d1a3129da990c1abd6c304027e3e939a5a1f06c666978c145f` | pp.4687–4690 / 1–4 (all) |
| `ban-jantzen-2016-duality` | `7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4` | p.158 / 6 (Proposition 4.1); pp.160–162 / 8–10 (Section 4 repair) |
| `renard-2026-representations-groupes-reductifs-padiques` | `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c` | III.1.4 p.60 / 66; VI.2.1 p.139 / 145; VI.5.3–VI.5.4 pp.173–174 / 179–180; VI.6.2 p.178 / 184; VI.6.4 p.179 / 185; VI.7.2 p.182 / 188; VI.7.3 p.185 / 191 |

The page offsets are: Aubert 1995, PDF = printed − 2178; erratum,
PDF = printed − 4686; Ban–Jantzen, PDF = printed − 152; Renard,
PDF = printed + 6.
