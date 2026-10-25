# Anthropic Brauer trace induction and the actual character-lattice bridge

Worker 18, 2026-10-25. Audit task `6f660c3b-fd16-4067-8f6a-611939522624`, revision 1.

**Verdict: adapt the trace-induction proof in focused mathematical units.** The eight-module source closure compiles privately on the project pin after four bounded compatibility edits. Its matrix trace theorem is useful for the existing character-lattice endpoint. It does not prove the character formula for the Library's actual quotient induction, nor injectivity of virtual-character realization. Preserve those as separate obligations. Reuse the Library's existing representation classes, induction and split Grothendieck group; defer a public port to separately authorized definition, statement and proof tasks.

This is a source and interface audit with development compilation evidence. The experiments are not accepted mathematical artifacts. Independent review and publication of this note do not admit the external theorem. No frozen target or public Lean module is changed by this note.

## Source, scope and evidence

The registered source is `anthropic-flt-complete-lean-source-6e837e75`, content SHA256 `a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`, from [Anthropic's FLT repository at the audited commit](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2). The project source directory is `literature/Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2`. The complete selected closure was read, including all theorem wrappers, definitions, three solution files, and `P2M.Util`.

| Input | Exact pin |
| --- | --- |
| Anthropic source | `6e837e75355538c7f80bab5b956861e86c4eacc2` |
| Upstream toolchain | Lean 4.33.1 |
| Upstream Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Project environment | `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` |
| Project toolchain | Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| Project Mathlib | `5ed2965256430c3649e86755f9576b54eca72435` |
| Library comparison verified in this activation | `13a081dfafb3be77f947b586115e69bcabd924c8` |

The [evidence appendix](anthropic-brauer-evidence/index.md) contains the original per-file SHA256 hashes, import lists, final adapted hashes, complete compatibility patch, private experiment recipes, full unapplied declaration displays, axiom output, and links to complete terminal service reports. It also fingerprints all four host Lean/Markdown pairs. The [source notices](anthropic-brauer-evidence/notices.md) preserve LICENSE and NOTICE and record the attribution check. No closure path or filename matches an upstream `ATTRIBUTION.md` row, and no individual author header occurs in the selected original files. The global notice is Copyright 2026 Anthropic, PBC, Apache-2.0; it also acknowledges Mathlib and notes that shorter restatements were not individually traced. No applicable source-specific errata file was present at the checked public/library paths on the audit date. This is a bounded provenance finding, not an assertion of original authorship of every underlying argument.

Recomputing textual imports from both requested root modules, stopping at `Mathlib` and `Lean`, gives exactly **8 local modules and 2,099 original lines**. The count is a file import closure, not a minimal declaration dependency proof:

| Component | Original lines | Boundary |
| --- | ---: | --- |
| `Definitions/Def_ClassFunction_Induced.lean` | 212 | Normalized function induction, congruence, conjugation, linearity, multiplication by a class function, induction in stages |
| `P2M/Util.lean` | 127 | Wrapper elaboration and namespace utilities; imports Lean |
| `Theorems/Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean` | 13 | Public Solomon wrapper |
| `P2M/Sol/S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean` | 660 | Solomon proof |
| `Theorems/Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean` | 19 | Public monomial wrapper |
| `P2M/Sol/S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean` | 867 | Monomial trace proof |
| `Theorems/Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean` | 16 | Requested public root |
| `P2M/Sol/S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean` | 185 | Brauer assembly |

All mathematical modules import Mathlib. The Solomon and monomial branches depend on the normalized induction definition but not on each other. The Brauer assembly imports both theorem wrappers and the definition. Each theorem wrapper refers to its corresponding `P2MW.S_….solution`; names and module paths are unchanged in the experiment. The helper namespaces `SolomonProof`, `MonomialProof` and `BrauerProof` remain in their original enclosing namespaces, including the explicit private root helpers used by the source. No replacement public names have been introduced.

## What the external root actually says

With `open scoped MatrixGroups` and classical decidability, the exact source telescope and conclusion of `BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter` are:

```lean
{G : Type} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
  ∃ (k : ℕ) (H : Fin k → Subgroup G)
    (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
    ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
      ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
        ∑ x : G, if hx : x⁻¹ * g * x ∈ H i then
          (((ψ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0)
```

The inspected root has **no universe parameters**. Its group lives in `Type 0`; its coefficient field is specifically ℂ and its carrier is a finite matrix coordinate space. The rank `n` can be zero. The coefficients are signed integers; no irreducibility or positive-rank hypothesis occurs. There is no representation-class or Grothendieck-group equality in the conclusion. The name's `zsmul` is displayed as integer coercion times a complex value.

The underlying `ClassFunction.induced` is a function operation with independent group and field universes:

```lean
{G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]
-- H : Subgroup G, φ : G → K
fun g => (Nat.card H : K)⁻¹ *
  ∑ x : G, if x⁻¹ * g * x ∈ H then φ (x⁻¹ * g * x) else 0
```

Its input need not be a class function; congruence on the subgroup makes the extension outside the subgroup irrelevant. Several identities, including induction in stages, require characteristic zero. This definition itself neither constructs an induced representation nor proves its trace formula.

The Solomon wrapper has `{G : Type} [Group G] [Fintype G]` and produces `k`, subgroups `H : Fin k → Subgroup G`, and integers `a`. Each `H i` admits a prime `q` and a cyclic subgroup `C ≤ H i` with `(Nat.card C).Coprime q`, conjugation stability under `H i`, and `∀ h ∈ H i, ∃ n : ℕ, h ^ q ^ n ∈ C`. Its equation is
`(1 : ℚ) = ∑ i, (a i : ℚ) * ClassFunction.induced (H i) (fun _ => (1 : ℚ)) g` for every `g`.
The proof develops integral permutation characters by fixed-coset counts, their multiplication, and a span/ideal argument. Its arithmetic part supplies hyperelementary subgroups detecting values modulo primes, then a maximal-ideal argument forces the constant function into the integral span.

The monomial wrapper also has a Type 0 finite group. It assumes a prime `p`, a normal subgroup `A`, commutativity `∀ a ∈ A, ∀ b ∈ A, a * b = b * a`, and `∀ g : G, ∃ n : ℕ, g ^ p ^ n ∈ A`. For every complex `GL (Fin n)` representation it expresses the trace as an **unsigned finite sum** of normalized inductions of unit-valued linear characters. The proof uses common weight spaces, finite-order semisimplicity, trace on permuted summands, a group-theoretic enlargement argument, and induction through smaller groups/dimensions. It has its own internal `Representation` bookkeeping, but the final target is still a character formula.

The Brauer assembly casts Solomon's identity to ℂ, multiplies it by the conjugation-invariant trace, applies the monomial result to the hyperelementary restrictions, and uses induction in stages. It then flattens the finite sums. These are the only two external theorem branches used by the root. Their complete displayed types and axiom output are retained in the evidence appendix.

## Compatibility and machine evidence

The final patch changes four source files without changing any theorem statement:

1. Close the residual definitional equality in `ClassFunction.induced_conj` with `rfl`.
2. In the Solomon proof, replace the old application of `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` with `Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ)` for the same contracted ideal.
3. In the monomial proof's `extChar_lift`, use explicit `change` to preserve the dependent conditional and unfold `lift` before cancelling the subgroup equivalence.
4. In the Brauer assembly, similarly reconstruct the dependent conditional with `change` instead of the failing coercion simplification.

The four modified files carry modification notices. The experiment retains `P2M.Util` and the wrapper tactic; no global attribute-reset module occurs in this closure. `p2m_exact_reverting` reverts the local telescope, elaborates the referenced proof at that type, and rejects remaining metavariables. Its elaboration is not a substitute for checking the resulting theorem; the root and dependency axiom outputs supply that separate evidence. Removing wrappers in a later port is a separate recorded change, not something tested here.

Successful check `4d218106-a903-4467-9b9d-92a576141c2b` compiled and inspected the root and printed the two dependency roots' axioms. After the modification comments were added, `5bab0732-36c7-4627-8d82-e253c503897e` rebuilt both experiment modules with zero errors, but its root inspection failed because the last module did not import the root. Corrected check `ff9426d5-6c84-4f22-865c-eff614d87b0b` inspected the root successfully. The root's axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`; the two dependency roots print the same set. Failed elaboration checks are retained as failures; their diagnostic recovery placeholders are not assumptions of the successfully checked source.

Bridge check `63b0c413-d9ca-4c8b-9b51-ac83307704f5` passes without errors or warnings, as does final API check `75c17d9b-4b2b-44e6-a6d0-2dc3f75e9181`. All five bridge theorems print only the standard axioms, and the inspected induction-sum transport retains separate `u` and `w` universes. These are private `lean_check` results, all with `proof_accepted: false`. They establish compilation and reported assumption checks, not independent semantic acceptance or exact proof coverage of a published Brauer target.

Full terminal JSON reports and complete printed types are preserved. Raw inspection-expression scratch files were removed by the service before copying; only their exact hashes and byte counts remain. Those raw expressions are explicitly unavailable. One interrupted restart job was terminally cancelled, as recorded in the appendix, and is not counted as a successful check.

## Exact host interfaces and the remaining bridge

All following names are in **`Langlands.FiniteRep`**, not nested `Classes`, `Induction` or `Virtual` namespaces. The files are [Classes](../../Langlands/Representation/Finite/Classes.lean), [Induction](../../Langlands/Representation/Finite/Induction.lean), [Virtual](../../Langlands/Representation/Finite/Virtual.lean), and [BrauerStatement](../../Langlands/Representation/Finite/BrauerStatement.lean). Full unapplied `#check` output with universes is in the appendix; the table gives its mathematical content.

| Declaration | Verified type or consequence |
| --- | --- |
| `ofRepresentation` | For `k : Type u`, `G : Type v`, `V : Type w`, `[Field k] [Group G] [AddCommGroup V] [Module k V] [Module.Finite k V]`, sends `Representation k G V` to `FDRep k G` |
| `modelEquiv ρ` | `Representation.Equiv ρ (ofRepresentation ρ).ρ`; independent source carrier universe |
| `classOfRepresentation ρ` | Actual isomorphism class `RepClass k G` of that coordinate model |
| `classOfRepresentation_eq_iff ρ σ` | Equality of these classes iff `Nonempty (Representation.Equiv ρ σ)`, allowing independent source/target carrier universes; it is not a character criterion |
| `character_classOfRepresentation ρ` | `character (classOfRepresentation ρ) = ρ.character` |
| `induceRepEquiv S V` | For `[S.FiniteIndex]`, an equivariant linear equivalence from `Representation.ind S.subtype V.ρ` to `(induceRep S V).ρ` |
| `character_induce_classOf S V` | `character (induce S (classOf V)) = (Representation.ind S.subtype V.ρ).character` |
| `virtualRep_exists_difference x` | `∃ a b : RepClass k G, x = ofClass a - ofClass b` |
| `virtualCharacter_ofClass a` | `virtualCharacter (ofClass a) = character a` |
| `mem_virtualCharacters_iff f` | `f ∈ virtualCharacters ↔ ∃ a b : RepClass k G, f = character a - character b` |
| `character_oneDimensional χ h` | `(oneDimensional χ).character h = (χ h : k)` |
| `inducedCharacterLattice_le` | For `[Finite G]`, `inducedCharacterLattice ≤ virtualCharacters` |

The requested name `virtualCharacter_oneDimensional` is absent from these Library modules. Use `virtualCharacter_ofClass`, the class-character definition, and `character_oneDimensional`. The right side of `character_induce_classOf` is the trace of Mathlib quotient induction, not syntactically the trace of `induceRep`; `induceRepEquiv` and `Representation.char_iso` supply that identification. None of these APIs computes the normalized conjugation sum.

The existing target `FiniteInducedCharacterFormulaStatement G`, for arbitrary `G : Type uG` with `[Group G] [Fintype G]`, is precisely:

```lean
∀ (S : Subgroup G) (V : FDRep ℂ S) (g : G),
  (induceRep S V).character g =
    (Nat.card S : ℂ)⁻¹ *
      ∑ x : G, if h : x⁻¹ * g * x ∈ S then
        V.character ⟨x⁻¹ * g * x, h⟩ else 0
```

The normalization and conjugation direction agree exactly with the external formula: inverse subgroup cardinality, `x⁻¹ * g * x`, and no inversion of the subgroup character. This agreement alone does not identify the two constructions. The host target concerns an actual induced action for every `FDRep`; the source defines an operation on functions. Its proof remains a separate task, or a weaker actual rank-one trace formula must be proved if that suffices for the immediate lattice endpoint. The weaker bridge would not discharge the full formula target.

The private theorem `BrauerAudit.rankOneBridge` assumes `h : FiniteInducedCharacterFormulaStatement G`, specializes it to `oneDimensional χ`, and proves

```lean
inducedCharacter (⟨S, χ⟩ : MonomialDatum ℂ G) g =
  ClassFunction.induced S
    (fun y => if hy : y ∈ S then (χ ⟨y, hy⟩ : ℂ) else 0) g
```

It is a checked adapter conditional on `h`; it does not prove `h`.

## Matrix and universe feasibility

The private `BrauerAudit.matrixModel` sends `ρ : Representation ℂ G V` to `G →* GL (Fin (Module.finrank ℂ V)) ℂ` by applying `Representation.asGroupHom`, then `Units.map` to `LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)`. `matrixModel_trace` proves equality of matrix trace and `ρ.character` using `LinearMap.trace_eq_matrix_trace`. Its group and carrier universes are independent. This reuses Mathlib and the existing coordinate-model approach; no second representation-class infrastructure is needed.

For the source's Type 0 restriction, `BrauerAudit.smallGroup` checks the specialization of `Finite.exists_type_univ_nonempty_mulEquiv` giving a finite Type 0 group `K` and `G ≃* K` from any finite `G : Type u`. Given an equivalence `e : G ≃* K`, `subgroupCard` proves
`Nat.card (S.comap e.toMonoidHom) = Nat.card S`. `inducedTransport` then proves

```lean
ClassFunction.induced (S.comap e.toMonoidHom) (f ∘ e) g =
  ClassFunction.induced S f (e g)
```

for independent group universes. It uses `Subgroup.comap_equiv_eq_map_symm`, `Subgroup.card_map_of_injective`, and `Fintype.sum_equiv`, preserving the conditional subgroup membership and conjugation product.

The proposed full adapter would restrict the coordinate representation along `e.symm`, apply the Type 0 source theorem, pull each subgroup and unit character back along `e`, and transport the finite sums and cardinalities as above. **That full assembly has not been implemented or compiled in this audit.** The checked constituents demonstrate feasibility without claiming complete arbitrary-universe root coverage. A later implementation must retain both the independent group/carrier universes and the zero-dimensional case, and explicitly finish the subgroup character transport and final integer-sum conversion.

## Character-lattice endpoint and separate representation-group endpoint

The first host endpoint is the unchanged proposition
`IntegralBrauerCharacterLatticeStatement G`, namely
`inducedCharacterLattice (k := ℂ) (G := G) = virtualCharacters (k := ℂ) (G := G)`.
It is equality over ℤ, not equality after tensoring with ℚ or ℂ, and not a finite-index assertion.

After a reviewed trace port, full universe adapter and actual rank-one induction bridge, each genuine trace character lies in the integral span of `inducedCharacter`. Convert `(a i : ℂ) * f g` to pointwise integer scalar multiplication. Use quotient induction on `RepClass` representatives and `mem_virtualCharacters_iff` to handle differences; the submodule is closed under subtraction. The reverse inclusion is already `inducedCharacterLattice_le`. This is a precise remaining proof plan, not a checked lattice theorem.

`IntegralBrauerSpanningStatement G` instead asserts surjectivity of `brauerExpansion G` into **`VirtualRep ℂ G`**. Matching characters of a proposed finite integer sum and a virtual representation does not establish equality there. One additional route is `FiniteVirtualCharacterFaithfulnessStatement G`, exactly `Function.Injective (virtualCharacter (k := ℂ) (G := G))`, plus the identification of the character image of `brauerExpansion` with the induced-character span. A separately proved cancellation argument could replace this route, but no such argument was found or proved here. The source's monomial weight decomposition does not by itself supply faithfulness for all actual complex representation classes. A Brauer–Nesbitt theorem requiring the representation image to span the entire endomorphism algebra cannot be substituted for general semisimple faithfulness.

The full `FiniteBrauerTheoryStatement` also includes finite order of rank-one characters, induced degree, and an irreducible basis assertion. The audited root does not discharge those targets merely by proving a trace expansion.

## Smallest proposed units and ownership

This table is a dependency proposal, not a new task assignment or authorization. Publish definitions first, then any missing Prop-valued statement targets, and submit proofs only against published targets. Group small bookkeeping lemmas with their natural unit.

| Unit | Dependencies and exact remaining work |
| --- | --- |
| Normalized function induction | Definition and elementary sum/conjugation/transitivity API; preserve source formula and provenance; avoid confusion with actual induction |
| Solomon trace identity | Function-induction API; port the fixed-coset, integral-span and maximal-ideal argument with its exact hyperelementary predicate |
| Monomial trace identity | Function-induction API; port the weight-space and induction argument with normal commutative subgroup and prime-power quotient hypotheses |
| Brauer trace assembly | Solomon and monomial targets/proofs; preserve integer coefficients and all ranks |
| Matrix and group-universe adapter | Mathlib/Library coordinate APIs plus trace assembly; finish subgroup/unit-character transport and the arbitrary-universe conclusion |
| Actual induced-character formula | Existing quotient induction and `induceRepEquiv`; prove the full existing formula target, or explicitly scope a sufficient rank-one subtarget |
| Integral character-lattice equality | Trace adapter plus actual rank-one bridge and existing `mem_virtualCharacters_iff` / `inducedCharacterLattice_le` |
| Faithfulness and virtual spanning | Separate faithfulness/cancellation proof; then combine character expansion with injectivity to prove `IntegralBrauerSpanningStatement` |

The Solomon and monomial units can be developed after the common function API; the actual induction-character formula can proceed independently of the external port. No bulk import of the source's 60,478-module tree is proposed.

Worker 24 retains construction/realization task `46c1335f-c68d-48e9-b805-9e5113eef3ea`; Worker 30 retains statement task `62ea68fa-e1f4-4187-811b-7436743bba6a`. Their consultations supported this bounded audit and reported no competing private Brauer proof. The existing constructions by Worker 18 are reused by Lean name. The accepted note is to be sent to Workers 0, 24 and 30 with the actionable interfaces above; this audit creates no competing implementation ownership.
