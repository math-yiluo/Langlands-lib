# Anthropic abelian Hasse–Arf: audit against actual p-adic ramification groups

Worker 25, 25 October 2026. The private adapter's faithful-action argument is adapted from Worker 40's Library proof. This is a source and interface audit, with reproducible development checks; publishing this note does not accept or publish the external mathematics.

**Verdict: adapt.** The complete selected source import closure was read: **53 modules, 8,170 original lines**, recomputed from imports and checked against original SHA256 hashes. Two compatibility edits suffice for the source root to compile in the approved environment. A complete private adapter also compiles with conclusion `Langlands.Ramification.Padic.HasseArfIntegrality K L T`, preserving arbitrary prime `p`, independent universes for `K` and `L`, their supplied compatible algebras, `IsGalois K.Carrier L.Carrier`, and every supplied `T : L.TopologicalData`. Both inspected theorems use only `propext`, `Classical.choice`, and `Quot.sound`. No mathematical defect was identified in this bounded reading. Independent semantic review of a future mathematical port, its Lake build, and exact-target validation remain necessary.

The deliverable is this note and its [evidence index](anthropic-hasse-arf-evidence/index.md). The experimental Lean remains outside the public module tree; its text is retained as an evidence block. This audit covers the named Hasse–Arf clause, not the entire `FiniteHerbrandArithmetic` conjunction.

## Pins, source scope and evidence

The registered source is `anthropic-flt-complete-lean-source-6e837e75`, content SHA256 `a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`, at [Anthropic FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2). The retained project literature directory is `literature/Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2`. The exact root is:

```text
Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean
IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative
```

Upstream pins Lean 4.33.1 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Every development check here uses project environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. No upstream build or external verification wrapper was used as acceptance evidence.

The [inventory](anthropic-hasse-arf-evidence/inventory.md) records every original path, module, hash, line count and import, in dependency order, with all external imports. This is a textual module closure terminating at Lean and pinned Mathlib, not a minimal declaration dependency graph. In particular, `Def_Compat_Mathlib430` and `Def_DifferentFiltrationFormula` bring material not needed at the final interface. The [reproduction procedure](anthropic-hasse-arf-evidence/reproduce.md) recomputes the closure, verifies original and adapted hashes, copies notices and paired English Markdown, applies the exact patch, reconstructs the private adapter, and prints the required `lean_check` requests. It never runs Lean from the shell.

The restoration check used the workspace based on Library `13a081dfafb3be77f947b586115e69bcabd924c8`. A later bounded scan of current Library `3e255196ad168b37f73124db5bdb4d6a5168a4da` and the pinned Mathlib found only the existing host proposition and its conjunction reference for `HasseArf|hasseArf|Hasse.Arf`. The three host interface files have identical bytes in both the checked workspace and that current Library. [The scan and file hashes are retained](anthropic-hasse-arf-evidence/library.md). This spelling-based search does not establish that no differently named reusable result exists.

## Exact source and host statements

The source theorem has independent universe parameters for `R : Type uR` and `G : Type uG`. Its hypotheses are `CommRing R`, `IsDomain R`, `IsDiscreteValuationRing R`, `Group G`, `Finite G`, `MulSemiringAction G R`, `FaithfulSMul G R`, `IsMulCommutative G`, the maximal ideal of `R` lying over that of `FixedPoints.subring R G`, separability of the corresponding residue-field extension, and `PerfectField (IsLocalRing.ResidueField R)`. Its conclusion is:

```lean
RamificationChain.HasseArfChain (IsLocalRing.lowerRamificationGroup R G)
```

The source's `Definitions/Def_RamificationChain_Wild.lean:16` defines the proposition exactly as:

```lean
def HasseArfChain (Gs : ℕ → Subgroup G) : Prop :=
  ∀ i : ℕ, Gs i ≠ Gs (i + 1) →
    Nat.card ↥(Gs 0) ∣ ∑ j ∈ Finset.Icc 1 i, Nat.card ↥(Gs j)
```

The [complete source theorem text and elaborated universe-explicit checks](anthropic-hasse-arf-evidence/bridge.md) are retained, together with `#print axioms` output in [check 08](anthropic-hasse-arf-evidence/check-08.md). The original source root failed to compile in the host environment before the compatibility edits, so no successful inspection of the unadapted root in that environment is claimed.

The host target is [ArithmeticStatement.lean](../../Langlands/LocalFactor/Ramification/Herbrand/ArithmeticStatement.lean), declaration `Langlands.Ramification.Padic.HasseArfIntegrality` (line 72 at the audited commits). With `p : ℕ`, `[Fact p.Prime]`, `K : PadicField.{uK} p`, `L : PadicField.{uL} p`, `[Algebra K.Carrier L.Carrier]`, `[IsScalarTower (Padic p) K.Carrier L.Carrier]`, `[IsGalois K.Carrier L.Carrier]`, and supplied `T : L.TopologicalData`, it is:

```lean
IsMulCommutative Gal(L.Carrier/K.Carrier) →
  ∀ i : ℕ, lowerRamificationGroup T K.Carrier i ≠
      lowerRamificationGroup T K.Carrier (i + 1) →
    ∃ n : ℤ, herbrandPhi T K.Carrier i = n
```

The compiled private `HasseArfAudit.integrality` has precisely this named proposition as its displayed conclusion, with the parameters above. Its inspection has level parameters `uK`, `uL`; no relationship between those universes was introduced. This development elaboration is distinct from a formal exact-target acceptance receipt: `proof_accepted` is false, no `statement_declaration` was supplied for receipt validation, and inspection's `target_matches: false` / `statement_returns_prop: false` are not a claim of statement mismatch or a non-propositional theorem. The raw encoded expression files were removed with the service scratch directory; the terminal records retain their exact hashes and byte lengths, while the readable full `#check @` types are retained. That limitation is explicit rather than replaced with a fabricated raw-expression artifact.

## The actual-ring adapter

All declarations in this section are private experiment names, proposed ingredients for later reviewed work. They are not importable Library declarations.

| Obligation | Implemented comparison and evidence |
|---|---|
| Actual ring and group | Set `R := T.Integers`, `G := Gal(L.Carrier/K.Carrier)` and install the existing `Langlands.Ramification.Padic.integerAction T K.Carrier` locally. Install `T.topology`, `T.valuativeRel`, and `T.localField` to obtain the DVR and residue finiteness instances. |
| Finiteness | `Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier L.Carrier` supplies finite dimension over `K.Carrier`; the full automorphism group is finite. No replacement quotient is substituted. |
| Faithfulness | `HasseArfAudit.action_faithful` proves agreement on the integer ring implies agreement on its fraction field, by `IsFractionRing.ringHom_ext`, then `AlgEquiv.ext`. This adapts the private `integerAction_faithful` in [Galois.lean](../../Langlands/LocalFactor/Ramification/Galois.lean), lines 107–119; its private name cannot be reused as an exported API. |
| Groups at all indices | `HasseArfAudit.groups_eq (i : ℕ)` is proved by subgroup extensionality and `rfl`. Both memberships require every integer `x` to satisfy `σ(x) - x ∈ maximalIdeal(T.Integers) ^ (i+1)`. The source `Ideal.inertia` action and host `lowerGroup` therefore give the identical subgroup, including `i = 0`. |
| Fixed-ring locality and lies-over | The source fixed ring has its local-ring instance. `FixedPoints.maximalIdeal_subring_eq_comap` gives the exact comap equality and hence the required `Ideal.LiesOver`. Identification of that fixed ring with the integers of `K` is unnecessary for this source theorem. |
| Residue perfectness and separability | The actual residue field of `T` is finite. The fixed-ring residue field embeds into it via the lies-over algebra map. Explicit local `Ideal.Quotient.field` instances for the raw quotient types allow `algebraMap.injective` and `Finite.of_injective`; finite-field instances then give perfectness and separability. These are proved/synthesized facts about these rings, not new premises. |
| Break condition | `groups_eq` rewrites both `i` and `i+1` in the host break inequality, exactly matching the source hypothesis. There is no shift of break conventions. |
| Cardinality | Source `HasseArfChain` and host `lowerGroupOrder` both use `Nat.card` of the subgroup. Equality of groups suffices. No `Nat.card`/`Fintype.card` adapter or arbitrary enumerator is needed at this boundary; the source internals use their own finite-card conversions. |

`HasseArfAudit.source_chain` applies the adapted source root after these instances are supplied. The experiment does not select canonical topological data, assume local class field theory, or use any host Herbrand tower or quotient-family theorem. The generic source proof does prove its own rational quotient compatibility internally; the distinction matters when planning its port.

## The numerical bridge

Write `a(j) := lowerGroupOrder T K.Carrier j`. The existing [Finite.lean](../../Langlands/LocalFactor/Ramification/Herbrand/Finite.lean) defines `a(j)` by `Nat.card`, proves `lowerGroupOrder_pos`, and proves `herbrandPhi_floor`. For every natural `i`, that floor identity specializes to

```text
herbrandPhi T K.Carrier (i : ℝ) = (∑ j ∈ Icc 1 i, a(j) : ℕ) / a(0),
```

where the numerator and denominator on the right are cast to `ℝ`. `HasseArfAudit.phi_nat` proves this: `Nat.floor_natCast` identifies the floor, `sub_self` makes the fractional term zero, an induction converts `Icc 1 i` to the shifted `range i`, and `Nat.cast_sum` moves the cast through the finite sum. The zero case has an empty sum, so the same formula covers `i = 0` without an extra premise.

At a lower break, source divisibility gives `∑ a(j) = a(0) * n` for `n : ℕ`. The positivity theorem gives a nonzero real denominator. Rewriting casts and cancelling produces the host witness `(n : ℤ)`; `Int.cast_natCast` identifies its real coercion. This avoids comparing the entire rational source phi function with the real host phi function: only the source divisibility conclusion and the host's already proved floor formula are needed. The complete implementation is in the [bridge evidence](anthropic-hasse-arf-evidence/bridge.md).

## Reading the complete proof closure

Every file in inventory order 1–53 was read in full, including both theorem wrappers and `P2M/Sol` implementations. [Detailed reading notes](anthropic-hasse-arf-evidence/reading.md) explain the implemented routes. The main dependency blocks are:

| Inventory positions | Content and audit finding |
|---|---|
| 1–14 | Ideal-inertia lower filtration; rational phi/psi; fixed-ring locality; divisibility statement; subgroup restriction; depth as the infimum of displacement valuations; faithful fixed-ring Galois group; monogenic generators controlling depth. |
| 15–20 | The orbit-product polynomial gives the monogenic coset-depth sum. Counting lower memberships, choosing maximal-depth representatives, and valuation scaling turn it into lower quotient compatibility at `ceil(phi)`. The early abstract quotient premise is later proved. |
| 21–32 | Different-formula statement, compatibility shim, inertia order/ramification index, finite fixed-ring extension, valuation scaling, separable DVR extensions being monogenic, and fixed-ring DVR. The monogenic proof uses primitive residue lifts, a uniformizer perturbation and Nakayama; the fixed-ring DVR proof chooses a least positive valuation using an orbit product. |
| 33–34 | A finite abelian character separates an element outside the next group; its kernel gives a cyclic quotient. Upper compatibility transfers a selected last quotient break to divisibility in the original group. |
| 35–43 | Powers raise positive depth; eventual triviality yields wild inertia a p-group. Uniformizer cocycles give the tame character, cyclic prime-to-characteristic tame quotient, and tame-index divisibility of positive breaks under commutativity. Perfect residue is used explicitly. |
| 44–49 | The long wild congruence proof uses Frobenius lifts, approximate invariant digits, trace and valuation estimates by strong induction. Cyclic counting by element order and Abel summation combine wild congruences with tame divisibility. Characteristic zero and positive characteristic are treated separately. |
| 50–53 | Quotient faithfulness follows by fraction-field invariants and fixed-field correspondence; double-fixed rings and residue maps supply the quotient hypotheses. The abelian root invokes the cyclic theorem with these proved inputs. |

The closure's two compatibility changes are fully retained in [the patch](anthropic-hasse-arf-evidence/compatibility.md): reuse the pinned Mathlib `AddSubgroup.inertia_mono` with its explicit group argument, and change the compatibility shim's `Finsupp.mapDomain_apply` use to `Finsupp.mapDomain_apply_of_injective hg`. All other source Lean bytes are unchanged. All retained source module and declaration names stay the same; the removed duplicate `AddSubgroup.inertia_mono` is resolved to the same-named Mathlib declaration. The six `HasseArfAudit.*` declarations are new experimental adapters. No P2M wrapper, tactic implementation, global attribute reset, theorem type or source proof route was removed. No unrestricted heartbeat option was added. Future extraction of unnecessary compatibility blocks or global attribute changes needs its own recorded edits and review.

## Checks and their limits

The evidence index links exact terminal reports, requests, patch and failed bridge snapshots. These are project Lean-service development records, not theorem acceptance receipts.

| Check | Outcome |
|---|---|
| 01 original closure | Failed with five errors: duplicate/changed `AddSubgroup.inertia_mono` and the changed `Finsupp.mapDomain_apply` API. |
| 02 first adapted attempt | Transport timeout, reconciled to a cancelled service job. It supplies no mathematical result; both records are retained. |
| 03 adapted leaves | Passed, zero errors. |
| 04 adapted source root | Passed, zero errors, 143 warnings; inspected both universes and only the three allowed axioms. |
| 05–07 evolving bridge | Failed on quotient aliases, field-instance/algebra-map elaboration and the final `lowerGroupOrder` unfolding. Exact unsuccessful source snapshots and reports are retained. |
| 08 complete bridge | Passed, zero errors, 19 style warnings; full source/bridge `#check @` output and five axiom checks retained. |
| 09 restoration | Recompiled `HasseArfAudit`; passed, zero errors and zero newly reported warnings, with the same bridge type fingerprint and allowed axioms. |

The successful source type fingerprint is `3d5937bee55aa11cdc0caeba3e4fcf1b7be78f9b359bcf863000158b7bb49fc4` (213,866 encoded bytes); the bridge fingerprint is `5bb489391670f9b123db2fda14c812652b59bcf2f8b08dd52fc46747a6c26c31` (22,301 encoded bytes). These identify inspected types, not publication status. Textual scans for holes or unsafe constructs, successful compilation and complete source reading provide different evidence; none substitutes for independent semantic acceptance.

## Notices and current errata

`LICENSE`, `NOTICE`, the applicable `ATTRIBUTION.md` entries and its limitations were read and preserved in both private source trees. The repository is copyright 2026 Anthropic, PBC, under Apache-2.0. Within this closure, the attribution table specifically names `Definitions/Def_Compat_Mathlib430.lean`; it reproduces or adapts blocks from eight Mathlib files. Their notices credit Antoine Labelle; Yunzhou Xie, Edison Xie and Kim Morrison; Johannes Hölzl, Callum Sutton and Yury Kudryashov; Chris Hughes; David Ang; David Kurniadi Angdinata; and Yongle Hu and Jiedong Jiang, with precise per-file lists retained in [provenance evidence](anthropic-hasse-arf-evidence/provenance.md). Absence of another closure path from the attribution table is not a claim that its ideas or every short passage are novel: upstream explicitly limits that tracing. Adapted files carry an added Worker 25 modification notice, preserving the original header and the full repository notices. The host faithful-action proof is separately credited to Worker 40.

The bounded current-source check on 25 October 2026 inspected the GitHub repository root, `main` head, all eleven issue/PR bodies then returned by the API, and comments for items 2, 6, 8, 10 and 11. Main still matched the pinned commit. No root errata file or Hasse–Arf-specific issue was found. Reports [8](https://github.com/anthropics/fermats-last-theorem/issues/8) and [10](https://github.com/anthropics/fermats-last-theorem/issues/10) concerned build failures reported resolved after increasing the memory-map limit. [Pull request 11](https://github.com/anthropics/fermats-last-theorem/pull/11) proposed a stale-work-directory fix in a verification wrapper; it was closed and did not claim a proof defect. Our service checks did not use that wrapper. These findings do not establish absence of other defects.

The retained source for that check is `anthropic-flt-hasse-arf-upstream-status-2026-10-25`, content SHA256 `71052bc0f831f9858a82ffe8be1b45f46f8856aa3ac9753965b6a5cc31fdee1d`, directory `literature/Anthropic FLT Hasse-Arf audit - upstream status and issue snapshot 2026-10-25`; locators and per-file hashes are in the provenance evidence.

## Proposed focused work and remaining obligations

This is a dependency-ordered proposal, not authorization to port the 53-file tree. Coordinate with Worker 0 and Worker 60 before creating mathematical tasks. Worker 60's arithmetic parent `aee98e7b-dc34-4549-afd4-ca288f42ea07` retains its scope; this audit does not replace norm or full Herbrand-family work. Existing construction and statement work are `d6f24eff-2379-41f8-8038-e2c826c77b58` and `62f87a9a-95a0-4e66-a143-b101054829c4`. The bounded task/owner consultation found no dedicated Hasse–Arf proof owner at audit time.

1. **Source foundations.** First review the required filtration/depth, fixed-ring and rational-index definitions and the `HasseArfChain` Prop target. Prefer the existing host `lowerGroup` and current Mathlib facts where their exact statements agree. Record the declaration partition and all attribution; the import inventory alone is not that partition.
2. **Source statements before proofs.** Publish focused Prop targets for the monogenic coset-depth and quotient route, tame/wild cyclic route, and abelian reduction, over the reviewed definitions. Then prove them in dependency order: fixed-ring DVR/finiteness and monogenic comparison; lower/upper quotient compatibility; tame character/divisibility and wild depth congruence; cyclic counting and cyclic Hasse–Arf; quotient hypotheses and abelian root. The 878-line wild congruence and 474-line cyclic counting implementations deserve separate proof units, not a bulk candidate.
3. **Actual-ring adapter.** Once the source root is published, group the short faithfulness, all-index subgroup equality and residue-instance comparisons corresponding to `HasseArfAudit.action_faithful`, `groups_eq`, and `source_chain`. These small lemmas form one reviewable adapter unit. A reviewed exported faithfulness lemma would avoid duplicating the currently private proof. Preserve every supplied `T` and both universes.
4. **Exact host proof.** Group the elementary `sum_Icc_eq_range` and `phi_nat` lemmas with the final proof corresponding to `HasseArfAudit.integrality`. Its proof task must name the existing `Langlands.Ramification.Padic.HasseArfIntegrality` statement. Freeze that target and its imports, submit the final theorem for Lake build and exact-target validation, and obtain independent semantic review and publication.

The experiment leaves no demonstrated logical gap in this particular adapter, but all public source decomposition, naming, attribution, mathematical review and exact-target receipts above remain obligations. Removing P2M machinery or compatibility baggage is optional refactoring with additional validation, not part of the two-edit feasibility result. Host tower laws, normal quotient comparisons for arbitrary supplied fixed-field presentations, and other clauses of `FiniteHerbrandArithmetic` remain outside this audit's claimed coverage.
