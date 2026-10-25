# Renard 2026: initial passage-level audit

This companion to [the coverage ledger](coverage.md) records the first source
reading. Locators refer to the registered 9 July 2026 French edition identified
there. Every row below remains open as a Renard correspondence or proof
obligation unless its status explicitly says otherwise. Related short
assertions are grouped for planning; later submission rows must identify their
individual Lean declarations and acceptance/publication evidence.

“In-book” describes the source's argument, not a Lean proof already supplied.
No proof-route correspondence is claimed for an unimplemented row. “External”
identifies the source's reference boundary, not an installed Lean axiom.

## Chapter I conventions and initial algebra

All ring rows permit associative noncommutative nonunital rings. Ambient
modules are abelian groups with associative distributive actions; a ring unit
need not act as identity. Ring and module universes must remain independent.
Right actions use the opposite-ring convention.

For every I.1.4–I.1.5 row below, `A` is idempotented and the module `M`
being completed is **nondegenerate**. Completion has domain `M(A)` and
codomain `A-mod`. Its embedding and recovery assertions concern this `M`;
the completed module itself need not be nondegenerate. In the adjunction,
`N` may be any ambient `A`-module:
`Hom_A(N, completed M) ≃ Hom_A(N_A, M)`.

| ID and source locator | Printed / PDF | Assertion or construction | Route and current obligation |
| --- | --- | --- | --- |
| I-open-finite | 5 / 11 | Finite-group complex representations correspond to unital modules over the group algebra. | Motivating assertion; cross-reference a checked general equivalence. No coverage claimed. |
| I-open-actions | 5–6 / 11–12 | Left/right module categories, commuting bimodule actions, algebraic dual and evaluation; unital modules form a full subcategory. | Actual actions/categories needed. Left/right ambient categories are assigned to module task `de5a8c55-bfa0-4ff5-8110-c3a8696ed2f1`; bimodules and duality remain successors. |
| I-open-splitting | 6 / 12 | As abelian groups, `M = eM ⊕ {m − e m}`; `e` acts as identity on the first summand and zero on the second. | Elementary splitting with actual maps remains open. The symbol `1` in `(1−e)M` is not an ambient ring unit. |
| I-open-corner-action | 6 / 12 | `eAe` has unit `e`, and `eM` is a unital module over it. | Ring part is in Worker 323's candidate; the actual corner action/splitting bridge remains open. |
| I.1.1-corner | 6 / 12 | Idempotents, corner `eAe`, membership iff `eae=a`, and equality with `eA ∩ Ae`. | Ring candidate `d68b4d83-2484-40a5-888e-368d81d825b0`; independent acceptance/publication pending. Verify the intersection assertion separately against its eventual names. |
| I.1.1-order | 6 / 12 | Order by corner inclusion; equivalence with `e∈fAf` and `e=fef`; then `ef=fe=e`. | In-book lemma (i). Candidate proposes `Idempotent.le_iff_sandwich` and `le_iff_mul`; publication pending. |
| I.1.1-absorption | 6 / 12 | If `e≤f` and `ea=a`, then `fa=a`. | In-book lemma (ii); included in the same ring candidate. |
| I.1.2-ring | 7 / 13 | Every finite family lies in one idempotent corner. | Candidate definition `Langlands.Algebra.IsIdempotented`; no accepted import yet. |
| I.1.2-directed | 7 / 13 | Every finite family of idempotents has a common upper bound. | In-book elementary lemma; ring candidate. |
| I.1.2-ring-union | 7 / 13 | The ring is the union of its corners. | Ring candidate includes the set-theoretic equality. |
| I.1.2-ring-colimit | 7 / 13 | The ring is the directed colimit of the corner inclusions. | Separate open universal-property obligation, with nonunital transition maps; Appendix A.IV.2 cited. Union equality alone does not discharge it. |
| I.1.2-module | 7 / 13 | Nondegeneracy means every vector is fixed by some idempotent. | Definition and actual full subcategory assigned to module task. |
| I.1.2-module-colimit | 7 / 13 | Nondegeneracy is equivalent to the displayed directed-colimit description by `eM`. | Open categorical correspondence; identify the correct ambient category, since `eM` is not generally an ambient `A`-submodule. |
| I.1.2-unital | 7 / 13, Remark 1 | A unital ring is idempotented; its unital modules are exactly the nondegenerate modules. | Ring assertion in ring candidate; elementwise module comparison in module task. |
| I.1.2-cofinal | 7 / 13, Remark 2 | A subsystem dominating every finite family of ambient idempotents suffices; the ring and module colimits can be taken over it. | Open definition/cofinality and colimit obligations. The source's condition is stronger than merely being directed internally. |
| I.1.2-relative | 7 / 13, Remark 3 | Nondegeneracy relative to an internally directed family of idempotents. | Open relative definition and exact scope of its claimed generalization. |
| I.1.2-part | 7 / 13 | Largest nondegenerate submodule `M_A`, described by the union of `eM`. | Actual submodule, maximality and nondegeneracy in module task; colimit description remains separate. |
| I.1.2-abelian | 7 / 13 | Nondegenerate modules are closed under submodules and quotients; their category is abelian. | Open statement/proof and Appendix A.VI.2 correspondence; fullness alone is insufficient. |
| I.1.2-functor | 8 / 14 | An intertwiner restricts to nondegenerate parts, defining a functor. | Intrinsic maps and functor laws in module task. |
| I.1.2-exact | 8 / 14, Proposition | The nondegenerate-part functor is exact. | In-book lift-and-apply-idempotent proof; separate statement/proof after the categories and maps publish. |
| I.1.3-topology | 8 / 14 | `A=A(1−e)⊕Ae`; `A(1−e)={a : ae=0}` is the left annihilator of `e`, equivalently the kernel of right multiplication by `e`. These subgroups give a translation-invariant uniformity and neighborhood basis; the zero/one pseudometrics give the same topology. | Open actual uniformity, basis, pseudometric and comparison constructions. Source cites [10] and [26] for general topology. |
| I.1.3-limit | 8–9 / 14–15 | Transition `Af→Ae`, `b↦be`; inverse-limit compatible families; canonical continuous embedding of `A`. | Open constructions and universal-property/topology proofs. |
| I.1.3-ring-completion | 9 / 15 | Multiplication by choosing `f` with `f b(e)=b(e)` is independent of choice; it extends the ring and gives a unit with coordinates `e`. | Open intrinsic ring laws, embedding compatibility and choice independence. |
| I.1.3-density-completeness | 9 / 15 | The embedded ring is dense; the compatible-family space is the uniform completion. | Density is argued in-book. Completeness is explicitly left to the reader and remains a required assertion, not an expository omission. |
| I.1.3-extension | 9 / 15 | Every nondegenerate module gets a unital action of the completed ring via an idempotent fixing a vector; the orbit map extends continuously. | Open choice independence, action laws and continuity/uniform-continuity correspondence. |
| I.1.4-module-completion | 9 / 15 | For nondegenerate `M`, its module uniformity, compatible-family inverse limit of `eM`, and canonical embedding into that limit. | Open actual constructions and completion proof. |
| I.1.4-Hom | 10 / 16, Proposition | Evaluation on idempotents identifies `Hom_A(A,M)` with the completion. | In-book inverse `a↦a·m(e)` for `ae=a`; open well-definedness and isomorphism. |
| I.1.4-action | 10 / 16 | The completion has action `(a·φ)(b)=φ(ba)` extending the original action; it need not be nondegenerate. | Open actual action and comparison. The right-module version identifies the completed ring with `End_{Aᵒᵖ}(A)`. |
| I.1.5-functor | 10 / 16 | Completion `M(A)→A-mod` acts on morphisms by coordinatewise extension. | Open actual functor, independent of the exactness theorem. |
| I.1.5-adjunction | 10 / 16, Proposition and (I.1.5.1–2) | For nondegenerate `M`, the nondegenerate part of its completion recovers `M`; completion `M(A)→A-mod` is faithful and right adjoint to nondegenerate-part formation `A-mod→M(A)`. | Statement and opening proof read; proof continues on PDF 17. Do not claim the proof has been fully audited in this initial pass. |

The cited ring candidate was rejected by independent review for an order-instance
conflict in its transparent idempotent subtype; the current evidence and
correction boundary are in the coverage ledger. Its proposed names below
remain navigation leads, with no accepted import.

The completed ring in I.1.3 uses the right regular module. The subsequent
module completion uses left modules. This orientation must remain visible in
the `End` comparison and action formulas.

## Chapter II topology, functions and distributions

Here a t.d. space means **Hausdorff with a compact-open neighborhood basis**.
No countability hypothesis is part of that definition. Functions and
distributions in II.1 have complex coefficients, and the distribution dual is
algebraic, without a topology imposed on the function space. Vector-valued
extensions allow arbitrary complex vector spaces, not just finite-dimensional
ones.

| ID and source locator | Printed / PDF | Assertion or construction | Route and current obligation |
| --- | --- | --- | --- |
| II.1.1-space | 30 / 36 | Exact t.d.-space predicate. | Definition/Mathlib correspondence task `09579afe-1e74-4559-ab2a-f6e74051da6a`; no candidate at publication. |
| II.1.1-group | 30 / 36 | Underlying t.d. topological group; equivalence with a compact-open subgroup basis at the identity. | Van Dantzig remains separate. Existing `Langlands.compactOpenSubgroupBasis` starts from `NonarchimedeanGroup` and weak local compactness; Hausdorffness must be accounted for in the source bridge. |
| II.1.1-subspace | 30 / 36, Lemma (i) | A locally closed subspace is t.d. | In-book local compact-open restriction proof; open exact target/reuse audit. |
| II.1.1-refinement | 30 / 36, Lemma (ii) | A compact set's open cover has a finite subordinate cover by pairwise disjoint compact opens. | In-book compactness and clopen refinement proof; open exact target/reuse audit. Cover members need not be contained in the compact set. |
| II.1.1-Baire | 30 / 36, Proposition | Countable intersections of dense open sets are dense. | Source invokes [26], XI.10.1. Audit Mathlib's locally compact Hausdorff Baire result; no extra second-countability premise. |
| II.1.2-functions | 30 / 36 | Locally constant functions, their compactly supported subspace, algebraic distributions, and function support. | Reuse leads: `LocallyConstant`, `SchwartzBruhat`, `Langlands.HarmonicAnalysis.Distribution`; exact object/support correspondences remain open. |
| II.1.2-simple | 31 / 37, Lemma | Every compactly supported locally constant function is a finite sum of scalar multiples of disjoint compact-open characteristic functions. | In-book use of II.1.1(ii). Existing `Langlands.Hecke.TestFunction.characteristic` supplies individual functions, not by itself the decomposition. |
| II.1.2-exact-functions | 31 / 37, (II.1.2.1) | For open `U` with closed complement `Z`, extension by zero and restriction form the short exact sequence of test functions. | In-book extension/refinement proof; actual maps and exactness open. |
| II.1.2-exact-dual | 31 / 37, (II.1.2.2) | The dual distribution sequence is exact. | In-book algebraic duality; open maps, surjectivity and exactness correspondence. |
| II.1.2-support | 31 / 37 | Distribution support; distributions supported on closed `Z` identify uniquely with distributions on `Z`. | Open actual support, restriction and unique extension statement/proof. |
| II.1.2-compact-dual | 31–32 / 37–38 | Compactly supported distributions and their pairing with all locally constant functions. | Open construction through restriction to the compact support and independence/linearity laws. Integral notation here denotes algebraic evaluation. |
| II.1.2-vector | 32 / 38 | Vector-valued locally constant and test functions; extension of the preceding results. | Open assertion expansion at arbitrary coefficient-carrier universe and dimension. |
| II.1.2-tensor-injections | 32 / 38, (II.1.2.3–4) | Scalar-function tensor maps to vector-valued functions are injective; the compact-support map is an isomorphism. | In-book finite decomposition establishes compact-support surjectivity. Do not claim surjectivity for all locally constant functions. |
| II.1.3-product-space | 32 / 38 | Product t.d. topology and finite disjoint compact-open rectangle decompositions for compact opens. | Open product/refinement correspondence. |
| II.1.3-test-tensor | 32 / 38 | Test functions on `X×Y` identify with the tensor product of test-function spaces, by pointwise product. | In-book rectangle decomposition; open actual linear equivalence. |
| II.1.3-distribution-tensor | 32 / 38 | Tensor product of distributions with its pure-tensor evaluation rule and both Fubini formulas. | In-book reduction to finite sums; open actual tensor construction and identities. |
| II.1.3-support-product | 32 / 38, Proposition | Tensor-distribution support is the product of supports; compact supports remain compact. | In-book restriction to product neighborhoods; open proof correspondence. |
| II.2.1-basis | 33 / 39 | Basis of a topology and its determination of the topology. | Opening definition read; audit existing Mathlib basis API. |
| II.2.1-presheaf | 33 / 39 | Presheaves on a basis, restrictions, their category and morphism compatibility (II.2.1.1). | Open comparison with actual functor categories. The source additionally requires `F(∅)=0` when the empty open belongs to the basis; unrestricted presheaves do not automatically satisfy that convention. |
| II.2.1-extension | 33 / 39 | A sheaf on a basis extends naturally to all opens; the analogous claim is not made for arbitrary presheaves. | Announced assertion only at this reading boundary; subsequent definitions/proof remain unread. |

The inspected test-function module proves that its function support is clopen,
compact and equal to topological support. Those declarations are useful exact
leads (`isClopen_support`, `isCompact_support`, `tsupport_eq_support`), but they
do not establish all the source's distribution-support assertions.

## Chapter V local fields and initial structural inputs

The actual local field, valuation, integer ring, residue field and topology
must agree throughout. The source sets up arbitrary nonarchimedean local
fields in V.1–V.2; the finiteness of rational conjugacy classes of maximal tori
in V.2.1 explicitly adds characteristic zero. That restriction must not be
propagated to unrelated rows or dropped from its own row.

| ID and source locator | Printed / PDF | Assertion or construction | Route and current obligation |
| --- | --- | --- | --- |
| V.1-valuation | 103 / 109 | Surjective additive valuation into `ℤ∪{∞}`; integer ring, maximal ideal and valuation-zero units. | Source refers to [21]. Reuse `Langlands.FML.ord`, `ord_nonneg_iff_mem_integer`, `ringOfIntegers` and `unitGroup`; surjectivity and remaining exact characterizations need checked bridges. |
| V.1-uniformizer | 103 / 109 | Uniformizer of order one and unique unit-times-uniformizer-power expression for every nonzero element. | Source refers to [21]. Uniformizer API planned with normalization; unique decomposition remains a separate statement/proof or exact reuse bridge. |
| V.1-residue | 103 / 109 | Actual finite residue field with prime-power cardinality. | Source refers to [21]. Audit Mathlib's actual residue field; do not replace it with an arbitrary finite field of a stipulated cardinality. |
| V.1-absolute-value | 103 / 109 | Residue-normalized absolute value `q^(−v(x))`, with zero value at zero. | Definition/adapter task `36c76186-09b4-4977-a59f-e14ff6f85fcf`, explicitly reusing FML order. No construction accepted by this program yet. |
| V.1-topology | 104 / 110 | Absolute-value metric gives the field topology; powers of the maximal ideal give a compact-open additive neighborhood basis. | Open topology and ideal/lattice bridges, including depth conventions. Existing `FML.lattice` alone is not this theorem. |
| V.1-Haar | 104 / 110 | Additive Haar measure, unit volume for the integer ring, and the integral change of variables by `|a|⁻¹`. | Reuse lead: `Langlands.HarmonicAnalysis.generalScalarHaarScalingStatement`; it assumes the normalization certificates and states a measure map. Exact source integral specialization remains open. |
| V.1-algebraic-data | 104 / 110 | Algebraic/separable closures and the multiplicative algebraic group with its field points. | Actual definitions or checked existing models remain to be identified. |
| V.1-linear-topology | 104 / 110 | Finite-dimensional vector-space topology; matrix and GL topology; compact-open congruence subgroup basis. | General-field source adapter open. Keep matrix rank and congruence depth distinct despite the displayed source's repeated `n` notation. |
| V.2.1-radicals | 104 / 110 | Radical and unipotent radical, their uniqueness/maximal properties; reductive and semisimple predicates; derived group and its field of definition. | Proposed external structural entries, source [42]. Actual data and precise Prop assertions are not yet constructed. |
| V.2.1-derived | 104 / 110 | For reductive groups: central radical, semisimple derived group, product generation, finite intersection, radical equal to identity component of centre, rationality of radical and centre. | Proposed separate external inputs from [42]; no representation-theoretic conclusions included. |
| V.2.1-tori | 104 / 110 | A maximal torus centralizes only itself; existence of rational maximal tori; characteristic-zero finiteness of rational conjugacy classes; conjugacy of maximal split tori. | Proposed external entries from [42], with distinct hypotheses retained. |
| V.2.1-split-component | 104 / 110 | Split component and its uniqueness in the reductive case. | Definition plus in-book deduction from centrality and conjugacy. The uniqueness derivation remains a proof obligation even if its inputs are external. |
| V.2.1-group-topology | 104 / 110 | Rational linear embedding gives an embedding into GL and a t.d. topology independent of embedding; reductive rational points are unimodular. | Proposed explicit external assertions from the source's [42] boundary; actual embeddings/topology/data and precise hypotheses must be supplied. |
| V.2.2-characters | 105 / 111 | Algebraic and rational character groups; characters factor through the abelian quotient; radical quotient description; finite-rank torsion-free lattices and full-rank inclusion. | Definitions and displayed in-book reductions must be separated from imported algebraic-group facts. All exact interfaces and proofs remain open. |
| V.2.2-dual | 105 / 111 | Dual character lattices, evaluation and double-dual identification. | Actual finitely generated free abelian groups and duality; exact Mathlib reuse audit open. |
| V.2.2-torus-pairing | 105 / 111, Remark 1 | Torus cocharacters as algebraic maps, exponent pairing, character basis of regular functions, group algebra and spectrum description. | Proposed external torus facts; actual algebraic data and scope still to audit. |
| V.2.2-torus-splitting | 105 / 111, Remark 2 | Anisotropic/split torus definitions, unique maximal split and anisotropic subtori, almost-direct product. | Proposed external inputs, with the source's exact definitions retained; realization open. |
| V.2.3-valuation-map | 105 / 111, (V.2.3.1) | `H_G(g)` evaluates on a rational character as its additive valuation; kernel and image give an exact sequence. | Actual homomorphism, kernel/image and intrinsic proofs remain open; the target lattice is written additively. |
| V.2.3-kernel | 105 / 111 | The kernel of `H_G` is the intersection of kernels of absolute-valued rational characters. | In-book immediate deduction; needs the normalized-absolute-value/order-zero bridge. The rest of V.2.3 is unread. |

The source's references located for this pass are [10] Bourbaki, *General
Topology*, Chapters 1–4; [21] Cassels and Fröhlich (editors), *Algebraic Number
Theory*; [26] Dugundji, *Topology*; [29] Godement, *Algebraic Topology and Sheaf
Theory*; and [42] Springer, *Linear Algebraic Groups*. These English labels
identify bibliography entries; this pass has not independently audited those
books or registered their entire contents as required formalization work.

## Evidence still required

For every open row, future updates must record the exact Lean construction or
Prop-valued target, complete hypotheses, actual implemented proof route, task
owner, independent review and current publication evidence. A definition task,
an inspected module name, a successful local compile, or this reviewed planning
note cannot stand in for those mathematical results.
