# External Library audit: global adeles, norms and Shimura conventions

Author: Worker 50. Verification task: `91e06186-d4aa-45d6-8a61-b97e5a870d0f`, revision 1.

This note checks the nine findings assigned to this area from *External Library audits 2026-10-22*. All nine hold as documentation defects at the historical verification baseline. All nine are repaired at the final checked Library commit, through six independently accepted and published corrections to ten Markdown files. None required changing Lean mathematics. The corrections preserve the distinction between an imported statement, a conditional reduction, a separately proved theorem, and an independently accepted publication.

## Scope and checked baseline

The historical verification baseline is Library `b26cde6370d6c0976d0002a7f4c955db801efd02`. The first verdict table records locations at that baseline, not the reports' historical line numbers. The final publication check is Library `4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`: all 42 files listed below were rehashed, all 21 Lean files are unchanged, and exactly ten Markdown files have the reviewed corrections listed in the publication ledger. All checked files match the audit workspace. The final repair table and corrected-file fingerprints, together with the unchanged baseline fingerprints, identify the complete current evidence.

The original reports were read as allegations, not acceptance evidence: ISSUES-1 used Library `c5a40b0f54880b1825ea05214c2b066f68bfc156` and ISSUES-2 used `f9c1742752d97c488fc1a835070bf50b534f4427`. Their registered source is `external-library-audits-2026-10-22`, folder fingerprint `975133657fad9fc7d0806e2cf4aaefac907edd151ec4df6cdd5d92b18a95a93b`.

The conclusions are restricted to the assigned wording and the declarations needed to check it. They do not certify all local or global class field theory, the local Langlands correspondence, or compatible automorphic Galois-family existence. In particular, a completed norm construction does not prove every reciprocity target that mentions it.

## Per-finding verdicts

All paths in this table begin at the Library root. The analysis below gives the complete hypotheses and source comparisons behind the concise rows.

| Finding | Verdict at baseline | Baseline location and decisive evidence | Correction decision |
| --- | --- | --- | --- |
| I012 | Holds: omitted assumptions in prose | `Langlands/Shimura/Unitary/Adelic.md:6–20,31–35`; paired Lean `Points` topology and multiplier at 32–48, topological-group instance at 36–40, `coordinateEquiv` at 54–65, coefficient continuity at 82–106 explicitly distinguish `TopologicalSpace` from `IsTopologicalRing` and finiteness. | State the assumptions separately for each level; keep the actual finite-adelic specialization and all Lean bytes. Shimura correction task. |
| I013 | Holds: omitted argument in Hodge notation | `Langlands/Shimura/Unitary/Reflex.md:55–59` says `n = r`; paired Lean `hodgeNumber_correctedComplexHom_conj` at 79–87 proves a Hodge number equals `r` under `r ≤ n`, and the conjugate theorem at 90–102 gives `n-r`. Kottwitz defines ambient dimension `n` separately from `n(i)`. | Replace the equality by `n(i)=r` or `hodgeNumber=r`, retaining the rank and hypothesis. Shimura correction task. |
| I028 | Holds: obsolete existence and residue-comparison status | `Langlands/Galois/CompatibleFamily.md:84–93`; `FrobeniusLift.lean:34–65` proves the cardinality-power formula, residue-action surjectivity and `exists_geometricFrobeniusLift` for the same local objects. `hasEulerPolynomialAt_iff` at 82–90 identifies matching at a chosen lift. | Refer to the published intrinsic construction and residue comparison; distinguish closure transport and global existence. Frobenius correction task. |
| I029 | Holds: obsolete Library-wide status | `Langlands/Global/AdelicFunctoriality/Norm.md:50–54` says finite bijectivity, principal compatibility and descent remain unproved. The accepted `completedTensorComparison`, `normCompatibility`, and `ideleClassNorm` supply these separately. | Explain what `Norm` constructs and where the additional results are supplied. Norm correction task. |
| I030 | Holds: obsolete premise status | `Langlands/Global/AdelicFunctoriality/NormAssemblyProof.md:49–53` calls the finite comparison outstanding. `CompletedTensorComparisonProof.lean:15–22` proves both finite and infinite comparison; `IdeleClassNorm` specializes the assembly. | Retain `normAssembly` as two conditional reductions and cite their separately discharged premises. Norm correction task. |
| I031 | Holds: obsolete status and proof-route description | `Langlands/Global/AdelicFunctoriality/NormStatement.md:31–40` calls finite comparison and global norm identity unproved, determinant reduction proposed, and quotient norm unconstructed. `NormReduction.lean:19–143`, `NormCompatibilityProof.lean:11–13`, and `IdeleClassNorm.lean:19–63` implement the stated steps. | Keep `NormStatement` as proposition definitions; describe the separate proofs and construction accurately. Norm correction task. |
| I032 | Holds: obsolete rationale, valid norm-image definition | `Langlands/Global/Arithmetic/ArtinNormStatement.md:23–34` motivates the direct norm image by unfinished descent. `IdeleClassNorm.lean:25–63` already supplies the principal-unit identity, quotient norm and its laws. | Retain the direct image of ideles under norm followed by quotient; explain that it is independent of the quotient-norm construction, which is now available. No claim that its four CFT goals follow. Norm correction task. |
| ISSUES-1 DOC-06 | Holds in both named consumers | `Langlands/Automorphic/ConstantTerm.md:16–18,141–144` and `Langlands/Automorphic/CuspidalForms.md:53–56`; `AdeleQuotientCompactProof.lean:182–209` proves compactness for the actual quotient under number-field hypotheses. | Cite the proof and explain local installation of `compactSpace_adeleQuotient K`; preserve consumer instance parameters. Compactness correction task. |
| ISSUES-1 DOC-07 | Holds in all three named files | The I030 and I031 locations, plus `Langlands/Global/AdelicFunctoriality/NormDescentReduction.md:3–8,26–31`. The latter's explicit principal formula and finite-comparison premises remain valid; their description as globally unproved is stale. | Correct all three documents, cross-reference the accepted comparison, compatibility and quotient construction, and keep the reductions conditional. Norm correction task. |

The valid scope qualifications in I012, I029–I032 and DOC-06/DOC-07 are not counterexamples to these verdicts. The reports already distinguish the sound constructions and conditional statements from the defective wording. No additional allegation of a Lean error is accepted here.

## Shimura coefficients and Hodge numbers

In [Adelic.lean](../../../Langlands/Shimura/Unitary/Adelic.lean), the algebraic data are independent carriers `R : Type u`, `A : Type v`, with `[CommRing R] [Ring A] [Algebra R A]` and an `AlgebraInvolution R A`. A coefficient algebra `S : Type w` has `[CommRing S] [Algebra R S]`. The group `σ.Points S` is algebraic and needs no topology. Its installed topology and `Points.continuous_multiplier` require only `[TopologicalSpace S]`. The former is built from the module topology of `S ⊗[R] A`, units recording value and inverse, and the subgroup topology.

The `IsTopologicalGroup` instance additionally requires `[IsTopologicalRing S] [Module.Finite R A]`. `coordinateEquiv` additionally requires `[IsTopologicalRing S]` and a supplied basis `b : Module.Basis ι R A` with `[Finite ι]`, where `ι : Type z`; its finite basis supplies the relevant finiteness. It is not a result for an arbitrary infinite basis or arbitrary coefficient topology. Both `continuous_changeCoefficients` and `continuous_pointsMap` require topological rings `S` and `T`, `[Module.Finite R A]`, and an algebra map `f : S →ₐ[R] T` with `Continuous f`. The base algebra `A` needs no independently supplied topology. Rational finite adeles and their actual local completions satisfy the coefficient assumptions; `finiteLocalMap` explicitly retains `[Module.Finite ℚ A]`.

The pinned Mathlib `Topology/Algebra/Module/ModuleTopology.lean:681–700` assumes a topological commutative base ring and a finite module algebra before proving `IsModuleTopology.isTopologicalRing`. Its universal-property lemmas at 301–370 explain the continuity argument; they do not remove the explicit assumptions of the public interface. The environment is Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

Kottwitz (1992), §1, printed pp.654–655 (PDF pp.2–3), gives the rational coefficient point functor and multiplier, then defines `n(i)=dim_C V₁` inside a simple module of ambient dimension `n`. It does not claim arbitrary coefficient topologies yield topological groups. Harris (1997), §2, printed pp.88–90 (PDF pp.14–16), and Harris (1999), §4, printed pp.308–309 (PDF pp.10–11), provide the finite-adelic/level context. The general module-topology argument is an internal implementation, not a theorem attributed to those articles.

In [Reflex.lean](../../../Langlands/Shimura/Unitary/Reflex.lean), `hodgeSubspace h` is the complex submodule of `Fin n → ℂ` on which `h(z)` acts as multiplication by `z`, and `hodgeNumber h` is its complex finrank. The signature theorem has arbitrary natural numbers `n,r` with `r ≤ n`; it counts the first `r` coordinates. Nothing asserts `n=r`. Kottwitz's complementary relation is `n(i)+n(i′)=n`, matching the second implemented count `n-r`. The correction changes only the erroneous displayed explanation, with no revision of a theorem, rank, signature, or reflex-field claim.

## Geometric Frobenius and the actual residue comparison

The full declarations in [CompatibleFamily.lean](../../../Langlands/Galois/CompatibleFamily.lean) and [FrobeniusLift.lean](../../../Langlands/Galois/FrobeniusLift.lean) use a number field `K : Type uK` and an actual `v : Global.FinitePlace K`. `LocalGroup v` is the absolute Galois group of `Global.FiniteCompletion K v`. `LocalResidueClosure v` is the residue field of the spectral valuation on its algebraic closure. `localResidueAction` is the existing `Langlands.LocalGalois.residueHom`, and inertia is its kernel. The geometric condition says the inverse automorphism acts by `x ↦ x^(residueCardinality v)`, where the exponent is the absolute ideal norm.

[CompletionResidue.lean](../../../Langlands/Global/CompletionResidue.lean):98–116 constructs the ring equivalence from `𝓞_K/v` to the residue field of the same norm valuation ring, proves the cardinality identity, and transports the characteristic. The proof uses the actual integer embedding, its kernel and integral approximation. `Langlands.GaloisRepresentation.residueArithmeticFrobenius_apply` uses this identity, not an assumed identification. `localResidueAction_surjective` specializes the published spectral surjectivity theorem, deriving characteristic zero of the completion from `K`. The generic spectral result requires a complete nontrivially normed ultrametric base field, a Galois extension, and a finite base residue field; these are supplied at this actual completion. Lifting arithmetic Frobenius and taking its inverse proves `exists_geometricFrobeniusLift`; classical choice then defines `geometricFrobeniusLift`.

For a coefficient field `L : Type uL` with its topology and `A : Objects.{uK,uL,uV} K L`, `hasEulerPolynomialAt_iff` is precisely the conjunction of `IsUnramifiedAt A v` and equality with `frobeniusEulerPolynomial A v`. Lift independence requires unramifiedness. The carrier universe remains independent. The family specialization retains the finite coefficient exclusions, one finite base exceptional set, and distinct residue characteristics. These statements use the fixed global-to-local closure restriction; they do not establish independence under changing that restriction or construct compatible families from automorphic forms.

Tate (1979), §1.4.1, printed p.6 (Part II PDF p.15), uses inverse Frobenius for the uniformizer convention. Harris (1998), §1, printed p.183 (PDF p.7), uses geometric Frobenius in `det(1-rho(Frob_v)T)` and the same exclusions for compatibility. Serre (1979), II §1, printed pp.26–27 (PDF pp.34–35), gives residue-field preservation under completion; the global-integer quotient realization is the explicit internal specialization described above. These originals were read. The correction must not describe intrinsic lift existence, residue identification or cardinality comparison as unproved.

## Completed tensors, determinant norms and quotient descent

All the relevant number-field declarations in `Langlands.Global.AdelicFunctoriality` retain independent `K : Type u` and `L : Type v`, `[Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]`. Relative finite dimension and separability are supplied by number-field instances, not extra comparison or compatibility assumptions. Neither a Galois nor an abelian hypothesis is needed for these norm constructions.

[Norm.lean](../../../Langlands/Global/AdelicFunctoriality/Norm.lean) constructs `adeleNorm` as products of actual completed-field determinant norms and `ideleNorm` by passing to units. The finite restricted-product continuity proof controls the finitely many nonintegral coordinates. The canonical comparison has source `K_p ⊗[K] L` and target the dependent product over the actual places above `p`. At finite places those indices are height-one primes of `𝓞_L` whose ideals lie above `p.asIdeal`; at infinite places they use Mathlib's `LiesOver`. Its action on `x ⊗ y` is the product of the completed scalar image of `x` and the diagonal image of `y` in each factor. The infinite comparison is already proved in this module by weak approximation, closed finite-dimensional image and the local-degree sum.

[CompletedTensorComparisonProof.lean](../../../Langlands/Global/AdelicFunctoriality/CompletedTensorComparisonProof.lean):15–22 proves exactly `CompletedTensorComparison.{u,v}`, including both conjuncts. At a finite place, [FiniteComparisonReduction.lean](../../../Langlands/Global/AdelicFunctoriality/FiniteComparisonReduction.lean) gives surjectivity by weak approximation and closedness. [CompletedLocalDegreeProof.lean](../../../Langlands/Global/AdelicFunctoriality/CompletedLocalDegreeProof.lean):65–71 supplies each arithmetic degree lower bound using the completed DVR degree theorem, completed/global ramification, and the finite residue-cardinality inertia comparison. Summing these bounds and using the global ramification-inertia identity supplies the reverse dimension bound. No such bound remains a hypothesis of `completedTensorComparison`.

[NormReduction.lean](../../../Langlands/Global/AdelicFunctoriality/NormReduction.lean) proves `norm_baseChange`, `norm_prod`, `norm_pi`, and `norm_tensor_pi`. Thus determinant reduction is implemented, not merely proposed. The infinite principal formula is unconditional; the finite and combined formulas in this reduction still take finite comparison bijectivity. [NormAssemblyProof.lean](../../../Langlands/Global/AdelicFunctoriality/NormAssemblyProof.lean) proves `NormAssembly`: the implication from completed comparison to principal compatibility, together with `IdeleClassNormDescent`, which itself assumes principal compatibility. These implication types remain unchanged.

[NormCompatibilityProof.lean](../../../Langlands/Global/AdelicFunctoriality/NormCompatibilityProof.lean):11–13 proves exactly `NormCompatibility.{u,v}` by combining the completed comparison with `normAssembly.1`. The principal identity quantifies every `x : L`, including zero, and equates the actual adele norm with the diagonal image of `Algebra.norm K x`; it is not merely equality of valuations or absolute values.

[NormDescentReduction.lean](../../../Langlands/Global/AdelicFunctoriality/NormDescentReduction.lean) remains a conditional quotient construction. Given the principal formula, it proves the unit equation, preservation of the principal subgroup, continuity of `QuotientGroup.map`, and uniqueness by quotient induction. [IdeleClassNorm.lean](../../../Langlands/Global/AdelicFunctoriality/IdeleClassNorm.lean):19–63 supplies the proved principal formula, using `normAssembly.1 completedTensorComparison`. It gives `ideleNorm_principal` with field-unit norm `Units.map (Algebra.norm K)`, subgroup preservation, and the actual continuous homomorphism `ideleClassNorm : C_L →ₜ* C_K`. The representative equation, continuity, principal-class equation and uniqueness are proved there. It does not assume norm surjectivity.

[ArtinNormStatement.lean](../../../Langlands/Global/Arithmetic/ArtinNormStatement.lean) instead uses the range of `ideleClassMap K` composed with the raw `ideleNorm`, whose domain is `Ideles L`. This definition is valid without importing quotient descent. Once a quotient norm with the representative formula is available, surjectivity of the quotient projection gives equality of the two images as a mathematical consequence; no new Lean equality theorem is claimed here. The four targets add a Galois hypothesis and explicit commutativity of `L ≃ₐ[K] L`; the normalized reciprocity targets also take their specified continuous surjection. They remain separate proposition definitions in this module, irrespective of which results exist elsewhere. Nothing in the norm construction alone proves those reciprocity goals.

Weil (1973), III §3, printed pp.53–54 (PDF pp.70–71), supplies the determinant norm and scalar-extension/product context. III §4, Theorem 4 and Corollary 3, printed pp.56–58 (PDF pp.73–75), gives the actual completion decomposition and local/global norm formula; IV §1, Corollary 3, printed p.64 (PDF p.81), gives the adelic coordinate product. IV §§3–4, printed pp.71–76 (PDF pp.88–93), provides the units topology via value and inverse, continuous norm, and principal quotient. All these passages were read. The Lean tensor factors occur in the equivalent reversed order, and its finite product is a dependent function type. The comparison target does not assert Weil's additional almost-everywhere lattice statement. Artin–Tate (2009), VII §3, proof of Theorem 10, printed p.52 (PDF p.61), describes the idele kernel as principal elements times idele norms; VIII §1, Theorem 2 and continuation, pp.55–56 (PDF pp.64–65), gives the local/global norm intersection, including infinite places. These explain the separate statement scope, not a proof supplied by this audit.

## Additive quotient compactness and consumers

[AdeleQuotientStatement.lean](../../../Langlands/Global/AdeleQuotientStatement.lean) defines the actual `AdeleQuotient K = Adeles K ⧸ principalAdeles K`, with the quotient topology, and `AdeleQuotientCompactStatement K = CompactSpace (AdeleQuotient K)`. In [AdeleQuotientCompactProof.lean](../../../Langlands/Global/AdeleQuotientCompactProof.lean):182–209, `Langlands.Global.adeleQuotientCompact` proves that target for every `K : Type u` with `[Field K] [NumberField K]`. There is no assumed compactness certificate. The proof constructs a compact product of an archimedean fundamental set and the integral finite adeles. Clearing denominators, local approximation and the Chinese remainder theorem give a principal translate integral at finite places; a further global integer puts the infinite component in the fundamental set. Its continuous image covers the actual quotient, proving compactness. `compactSpace_adeleQuotient` states the result directly with the instance type.

[ConstantTerm.lean](../../../Langlands/Automorphic/ConstantTerm.lean) imports the statement module, not the compactness proof. Its Haar measures, integrability, constant terms and cuspidality still accept `[CompactSpace (AdeleQuotient K)]`. [CuspidalForms.lean](../../../Langlands/Automorphic/CuspidalForms.lean):112–181 retains that instance for its cusp-form constructions. These parameters are sound. A caller can import `Langlands.Global.AdeleQuotientCompactProof` and use `haveI := Langlands.Global.compactSpace_adeleQuotient K` locally. The theorem is not declared as a global instance.

Weil (1973), IV §2, Theorem 2 and proof, printed pp.64–65 (PDF pp.81–82), asserts compactness of the additive quotient, with a compact-set argument. Borel–Jacquet (1979), §3.3, printed p.194 (Part I PDF p.189), defines vanishing of constant terms and permits representatives of maximal proper parabolics; §4.4, printed p.196 (PDF p.191), defines cusp forms. These passages were read and agree with the consumer's documented provenance. This status correction does not change its chosen Haar normalization, block-parabolic interface, or any definition of cuspidality.

## Verified companion publications

The following original artifacts have independent approving semantic reviews with no review qualifications, accepted original machine evidence, and publication records with accepted fresh integrated validation. Their Lean/Markdown pair hashes match the checked current Library. Exact artifact records and publication receipts, not theorem names or adjacent prose, establish these statuses. These are supporting mathematical publications; the documentation corrections have separate records below.

| Result / artifact | Original validation | Independent reviewer | Publication commit |
| --- | --- | --- | --- |
| `FrobeniusLift` / `88845882-20e5-49d4-96ca-d282e661b114` | `91b54725-1a52-4b5e-b2b0-ceba13e4dc3d`, `lean.definition@1`, accepted | Reviewer 506, approve | `e7e1cf75d8341a5fe60f25d4e6bb64d251921cbf` |
| `AdeleQuotientCompactProof` / `ae2a07e5-9538-48b8-92fd-771f7e4a243a` | `387b16d6-92df-4cd4-845b-14be022c9b66`, `lean.proof@1`, accepted | Reviewer 935, approve | `f9c1742752d97c488fc1a835070bf50b534f4427` |
| `CompletedTensorComparisonProof` / `80416983-3beb-4160-b101-6cd3aff260ef` | `c225fba7-48bd-491d-9f1f-6c44dba41358`, `lean.proof@1`, accepted | Reviewer 488, approve | `3afe6f3ba5efc4d00cccb18dba321ef341bbaf68` |
| `NormCompatibilityProof` / `b79c434f-c59d-4c62-88ca-c0e8ef9a89a8` | `38c89462-8ce6-4970-87e9-dd16f1ced19a`, `lean.proof@1`, accepted | Reviewer 580, approve | `754bb6611525faf16de017eba5f7947f3f6e993c` |
| `IdeleClassNorm` / `2d8a3f12-180a-4831-bbf3-0797853cc815` | `100ecb07-35d5-48d0-b1ab-9646f4b2f907`, `lean.definition@1`, accepted | Reviewer 567, approve | `7c81d0a237386f36202562546586b28c306f0121` |

The three proof artifacts target, respectively, `AdeleQuotientCompactStatement`, `CompletedTensorComparison`, and `NormCompatibility` by their full published names. Their proof acceptance is distinct from the definition-artifact acceptance of `FrobeniusLift` and `IdeleClassNorm`, whose intrinsic laws are included in the independently reviewed source. The archived receipts do not convert the latter into separate exact-target proof artifacts.

## Correction publication ledger

Six corrections are independently accepted and published. Their authoritative exact records report `accepted=true` and `public=true`, successful original machine validation, independent approval without qualifications, and accepted fresh integrated Lake builds. Every correction preserves the Lean bytes; paired Markdown uses the ordinary mathematical-artifact review path. The integrated build is source-compilation evidence; the final proof correction's original validation additionally checks the exact target and unchanged statement. Independent semantic approval is recorded separately in every row.

| Unit / coverage | Task | Candidate, validation, semantic review and publication |
| --- | --- | --- |
| Shimura: I012, I013; `Adelic.md`, `Reflex.md` | `51b9adea-5217-4bf7-84d2-59bfe19c670e` | Accepted/public `e71428d4-45da-46c1-bd51-50a5402d6737`; `lean.definition@1` validation `16897c9a-c0cc-4850-9316-3e8dfc1bd994` accepted; Reviewer 1550 approved in `d3c276db-a18b-41af-a122-ae9f217bfe48`, no qualifications; publication `4ab35fd7cc442c437d97a7e9a247b902533aa199`, integration `43ba8fe89a5f4565b6e8a865e91a873e`, accepted fresh integrated build. |
| Frobenius: I028; `CompatibleFamily.md` | `783c62bb-12fc-4427-ae15-329afe05d0d5` | Accepted/public `466d2734-a91a-409f-a50f-52cf0b2d377a`; `lean.statement@1` validation `80eed57f-076d-4c61-823a-524a06671821` accepted; Reviewer 1553 approved in `5208f5a6-a032-4ab0-8dd1-42bc06703846`, no qualifications; publication `4ab35fd7cc442c437d97a7e9a247b902533aa199`, integration `74743296612546ac87f27e0e5699b307`, accepted fresh integrated build. |
| Norm construction: I029 and the `NormDescentReduction.md` part of DOC-07 | `a302f0e5-6a5e-4cfa-898e-847724f27be8` | Accepted/public `f804b474-0c14-4a62-83f0-14201eacb0c3`; `lean.definition@1` validation `3a4a1800-7e97-41b1-8a9a-34f5a0c566ee` accepted; Reviewer 1544 approved in `b4c0ae7a-c807-4ae3-972b-e031ae9cf78e`, no qualifications; publication `4ab35fd7cc442c437d97a7e9a247b902533aa199`, integration `7b95380009ed4a15a3e746a772b3d8fb`, accepted fresh integrated build. |
| Norm statements: I031, I032 and the `NormStatement.md` part of DOC-07 | `a302f0e5-6a5e-4cfa-898e-847724f27be8` | Accepted/public `c6a15db0-c917-4291-bcfe-8789b3602d26`; `lean.statement@1` validation `52a08878-d7b0-4d20-b944-64319680673c` accepted; Reviewer 1566 approved in `881679bc-468e-4296-859b-e5ec2ce6407d`, no qualifications; publication `50b69fcc3f4b78a7df7bdd07a8e0663c6bee3d79`, integration `983d1a164deb4904a3ee441673044256`, accepted fresh integrated build. |
| Compactness: DOC-06; `ConstantTerm.md`, `CuspidalForms.md` | `349636a6-29ec-450a-8c25-27a6f8aa19e7` | Accepted/public `1f796422-9424-4f2b-ab78-b491bec9f01b`; `lean.definition@1` validation `8340a3eb-f2c1-4acb-b108-3984a8f197b1` accepted; Reviewer 1542 approved in `1466b4e7-ac3b-4920-a630-06a9ee60fe8d`, no qualifications; publication `4ab35fd7cc442c437d97a7e9a247b902533aa199`, integration `baff343b9aed4bf99739a1e10df0bd0f`, accepted fresh integrated build. |
| Norm assembly: I030 and the `NormAssemblyProof.md` part of DOC-07 | `a302f0e5-6a5e-4cfa-898e-847724f27be8`, revision 2 | Accepted/public `3e1ac863-83a7-4518-b353-bf25f981f965`; `lean.proof@1` validation `94544d3b-9d86-48f8-9a45-b16b348660e9` accepted with Lake build, exact-target, unchanged-statement and frozen-input checks; Reviewer 1620 approved in `68fc9d53-1867-41a4-b03a-862de1641b87`, no qualifications; publication `4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`, integration `fe11cf2904a3466381d5168b83c8f7ce`, accepted fresh integrated build. |

The six exact records and their independent reports were checked. The frozen overlays have no removals and unchanged Lean bytes. The norm-statement overlay also carried the same definition-documentation edits, but its selected integration paths contain only the two statement pairs. All selected Lean/Markdown pairs match their reviewed hashes in the publication commits and current Library. The Frobenius author scope notes retain noncanonical choice and unramifiedness; review approval has no qualifications. The norm-statement candidate introduction's I030/I032 label is a numbering slip: its coverage is I031/I032, and I030 belongs to NormAssemblyProof.

Current repair locations at `4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9` (all paths begin at the Library root). Each finding no longer holds for its assigned wording after these published corrections; this does not revise its historical verdict:

| Finding | Current status and precise corrected Markdown locations |
| --- | --- |
| I012 | Repaired: `Langlands/Shimura/Unitary/Adelic.md:6–39` separates topology, topological-ring and finiteness assumptions. |
| I013 | Repaired: `Langlands/Shimura/Unitary/Reflex.md:55–63` states `n(i)=hodgeNumber=r` under `r≤n`, preserving ambient rank. |
| I028 | Repaired: `Langlands/Galois/CompatibleFamily.md:100–133` names the published lift and residue comparison with separate global/transport boundaries. |
| I029 | Repaired: `Langlands/Global/AdelicFunctoriality/Norm.md:50–74` distinguishes the construction from the comparison, compatibility and descended norm. |
| I030 | Repaired: `Langlands/Global/AdelicFunctoriality/NormAssemblyProof.md:3–8,50–69` preserves the exact two conditional reductions and identifies the separate comparison, compatibility and quotient-norm results. |
| I031 | Repaired: `Langlands/Global/AdelicFunctoriality/NormStatement.md:31–60` documents the implemented comparison, determinant reductions, compatibility and quotient norm. |
| I032 | Repaired: `Langlands/Global/Arithmetic/ArtinNormStatement.md:23–47` preserves the direct norm image and cites the independently constructed quotient norm. |
| ISSUES-1 DOC-06 | Repaired in both consumers: `Langlands/Automorphic/ConstantTerm.md:11–38,157–163` and `Langlands/Automorphic/CuspidalForms.md:51–65` retain explicit compactness parameters and explain the available theorem. |
| ISSUES-1 DOC-07 | Repaired in all three files: `Langlands/Global/AdelicFunctoriality/NormDescentReduction.md:26–58`, `NormStatement.md:31–60`, and `NormAssemblyProof.md:50–69` distinguish conditional interfaces from separately proved arithmetic premises and the constructed quotient norm. |

Published corrected-file fingerprints (also the current Library fingerprints):

| Path | SHA256 |
| --- | --- |
| `Langlands/Shimura/Unitary/Adelic.md` | `78797a744ff798a41ff3a309060502355a220811c945237d5a8285e6f4234698` |
| `Langlands/Shimura/Unitary/Reflex.md` | `194864158791af72348cc853526ba60ec2d68f98f94f03aff992212e0ddd4dd2` |
| `Langlands/Galois/CompatibleFamily.md` | `f509dfa9084587ef397278e6014060b4fc754772c60a3c435bcfce142e8d487e` |
| `Langlands/Global/AdelicFunctoriality/Norm.md` | `88654b17b73f3d9b5e87255e9d3ed54950f412d1fb6d341bc2d812465a30671b` |
| `Langlands/Global/AdelicFunctoriality/NormAssemblyProof.md` | `4b331240c114505bb8e679e3b8d9f9fd19339c3d90e0facff339497f70a2574e` |
| `Langlands/Global/AdelicFunctoriality/NormDescentReduction.md` | `96c3e39080c1490602f45e25bbd907e4b61459585d31857283987f5223def200` |
| `Langlands/Global/AdelicFunctoriality/NormStatement.md` | `8b15bcc6fdb26bb9ae59c7b42f3bde0e6677c55ae10bbd672eb9bcc907c7fc77` |
| `Langlands/Global/Arithmetic/ArtinNormStatement.md` | `fe20811ebaea66f8a4dbaca2f4d7c27ed31a9f429141ac914c561d5b2508ee59` |
| `Langlands/Automorphic/ConstantTerm.md` | `390d8d14db7f9893cd4ca40b783f36c01dd3e915d7445040d93b02b167557994` |
| `Langlands/Automorphic/CuspidalForms.md` | `05b3bd3874e04f423cc57dee4aa3df0594044ed5c692c5f1112224ff16e6a81f` |

No assigned corrective item remains open at the final checked snapshot. This consolidated note and its README entry follow the separate public-note review and publication process; their own receipt is separate from the six mathematical-artifact receipts above. Accurately disclosed class-field-theory goals and global Galois-family construction remain outside this correction task.

## Source register and reading extent

These source IDs are already registered in the project literature index. Original file hashes were recomputed for this audit. No source-specific errata files were present under the checked Library's or project notes' `errata/` directories. Harris (1997) is read with the correction context identified by the existing paired documentation; the present verdict does not rederive its corrected Shimura homomorphism. The explicit reading extents are listed in the analyses above; this note does not claim complete reading of any book or article.

| Registered source ID | Original-file SHA256 |
| --- | --- |
| `kottwitz-1992-lambda-adic-simple-shimura` | `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799` |
| `weil-1973-basic-number-theory` | `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b` |
| `tate-1979-number-theoretic-background` | `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6` |
| `harris-1998-local-langlands` | `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b` |
| `harris-1997-drinfeld-cohomology` | `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9` |
| `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d` | `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26` |
| `borel-jacquet-1979-automorphic` | `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5` |
| `serre-1979-local-fields` | `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112` |
| `artin-tate-2009-class-field-theory` | `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd` |

The source files are the exact retained originals identified by these IDs in [Literature](../../../wiki/literature.md) and the project's central-library pointer index. PDF page numbers above are one-based. The proof descriptions in this audit follow the implemented Lean route, which need not duplicate the source proof.

## Checked file fingerprints

All entries in this table are SHA256 at baseline `b26cde6370d6c0976d0002a7f4c955db801efd02`. The first column is the common path of the `.lean` and `.md` pair. Paired Markdown is evidence of the claim being checked, not by itself proof or acceptance.

| Module path | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- |
| `Langlands/Shimura/Unitary/Adelic` | `3260d72eaed089e3062047c8119201c1fc9ad71fe22c02531c039d40cf72169c` | `2c4ba2fb0e6900ee5ce4178456185f3f5cb5e016cb1f642d15427de1ab03a042` |
| `Langlands/Shimura/Unitary/Reflex` | `9240517277aea83abd4e88895762bbc09ef429ef698ad700be3c96828d0d2e1d` | `24f85e693397306a94052f122deceba89430102d5694359ffb809e8aecc73c4a` |
| `Langlands/Galois/CompatibleFamily` | `016a81b7efdb6e33a837ca297620bf313445270db45c855b9643017b4621bf84` | `113fe05562d9c177e85b8b1f24cd7864b93102a039d22a0239c1c1cac670592e` |
| `Langlands/Galois/FrobeniusLift` | `e187e1ec6df1603e25d175d35d3c69baf84482c616d62743f5bc84e65e6ff01d` | `755d817cdd6f208fc1416c21099fc7a225cfa3993ba0e16d0720d76e728a32fb` |
| `Langlands/Global/AdelicFunctoriality/Norm` | `22cca7bbbdf85f7ed70b4c9a8efe8b4b917609fd868621a56c91115100433b38` | `a6444f747e893b7b608886bb4356a5812041d28c64cacc251611eb8624387b62` |
| `Langlands/Global/AdelicFunctoriality/NormStatement` | `fd4479e3559cf848ac80a705d16646ca7b3ce34a4e384c3952cfd63b006216da` | `8617d3c6346374bdbd6b0b6ed8f49336de5f1fc3bf8072cb8a8fe3a0bf7b1f93` |
| `Langlands/Global/AdelicFunctoriality/NormAssemblyStatement` | `c5bd854abe36e9550db5999039eb6d86ddf3d417b8d1f2e97b5f26668932808c` | `01f3924658d874058f4d2d412aa5f784602c9137a15f0112697510518c426dfa` |
| `Langlands/Global/AdelicFunctoriality/NormAssemblyProof` | `1f95b27064917e328d087bc67270891b0ee90d143280b20542c01ec46a69e8c8` | `a223dc5b573f0a49f6921bd68fbbcf4761728d371e5e921b7879ea93813121bb` |
| `Langlands/Global/AdelicFunctoriality/NormDescentReduction` | `48a733ad301415154d68a9d110240262ac122334b77f34629c96c740a345be18` | `c0cd4674a38d97e4000527e67a8f22d2331034462f7e85226768e1ea92c019ab` |
| `Langlands/Global/AdelicFunctoriality/NormReduction` | `6a0786caa58c4966a0ce049bb3a3deb8f9c1fc9b696570b413d5c41f8f7a3d27` | `123b195fcbe990b57d6378d3bf77a74e7c535776da3f84e88c5501d6bfe4f2b6` |
| `Langlands/Global/AdelicFunctoriality/FiniteComparisonReduction` | `845a597535f99226dfec51f6fa00b91c91db885d85e488d3d2026fdfa7b3a790` | `53317bb01527e434a47f61be7341ebef113bcd7e2664a1e02d96775a9b876c4b` |
| `Langlands/Global/AdelicFunctoriality/CompletedLocalDegreeProof` | `25d32a5833822d2aab170ab1ca33d7be7937a316df2d72aeb52bf454c7850ed8` | `fce28f91e4fc8c3a320e937b1a44c26e367494ca1fa5e323e3344e90bed09e38` |
| `Langlands/Global/AdelicFunctoriality/CompletedTensorComparisonProof` | `f39657cc0269a08a6e4cd42b92979c62df83aa2451edc7bb37ef9f3b6d46a53c` | `8d63f9ab74bb927654f122af76cbce647a899305e25b8356f90319814960541a` |
| `Langlands/Global/AdelicFunctoriality/NormCompatibilityProof` | `581bab5dc2b6187a851804f1b10258fa0fa49f56e58fad029e15ec9bd24665db` | `e2058010ce9bc24c12c8b9b6179d76d18c09a2c692a12d28e659ab614cbeb370` |
| `Langlands/Global/AdelicFunctoriality/IdeleClassNorm` | `ddffc9ffbefee23c41d92029a31429eb2fbaa1ba75f50134030360b797d511b2` | `fd837c6a8d5a053bb534224117eeb76e8ab5292b39fabb51a54e919d0ef21cbd` |
| `Langlands/Global/Arithmetic/ArtinNormStatement` | `92bf450fb7e715db685cd4a69a8442152dac44fc1f7cc0771d407ef79efb6ae7` | `8f709d169c10bd2e5a37fee93e7c51f7963bd39db9be0cb246d6dcb4302b5848` |
| `Langlands/Automorphic/ConstantTerm` | `c83f402c4a7579d6691143a470727b8036cafb818334f7208d623d037cf2715d` | `c8a8e5b29a61d2d3aeecde70a83b41b57b5dbcd96347b123ab2273cd41137fb1` |
| `Langlands/Automorphic/CuspidalForms` | `843afae75e27d0863c4acde2c23b628c70c3e54d0b47ec2c94c7b975a63ef18f` | `ec2523f789455f163935612f1645291b3150560500209602b0e8e4d5c4fcf1d8` |
| `Langlands/Global/AdeleQuotientStatement` | `3a4a69feb5a7e4f9fa3a1ccfbdccfdd084644392d0441c92503cb8367f698103` | `2d1326165e19de760c2cd93708e1ffc426208b8d5b79a4b74a71a135becaffcb` |
| `Langlands/Global/AdeleQuotientCompactProof` | `3a4f5d0d57166b03058a2b1a54355fe9d8fe7d861b7a7a0530cedac64a00d214` | `1f9dc64f149235cd6b715cbf20c319f622354a6ff1b8f920086229620fe1f712` |
| `Langlands/Global/CompletionResidue` | `d2ae565f5ad144e7002fdd17cd1fda9990934fa81de39ec6cae5fde502ac0f10` | `289c33fc7ffa32aed26d08f8f507c5594ade4d935168b61d39cc112ab59fee80` |

Additional inspected dependency declaration fingerprints:

| Path | SHA256 |
| --- | --- |
| `Langlands/Galois/Local/SpectralProof.lean` | `0ec2c48c4e49e166a62db849a3f5a2f5b65dac72a9f23e28984d2a3a880e3c14` |
| `Langlands/Global/AdelicFunctoriality/Extension.lean` | `d80b486975f4272cf442044e647b123ab9c16e1a42d39b3090a7a668bc623a4a` |
| Pinned Mathlib `Mathlib/Topology/Algebra/Module/ModuleTopology.lean` | `4964b7ffee7ab7bcece606af6d6ef454f99156fe6c4635fc90b7cf2a2d27eb1b` |
