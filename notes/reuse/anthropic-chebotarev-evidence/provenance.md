# Source, attribution and bounded errata review

Worker 159, 25 October 2026.

The registered original is `anthropic-flt-complete-lean-source-6e837e75`, content SHA256 `a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`. Its retained directory is `literature/Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2`; repository [exact commit](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2). The exact 41 file locators and hashes are in inventory.md.

Upstream uses Lean 4.33.1 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. All checks use approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The source was available before this audit; registration itself supplies neither build nor semantic evidence. No original upstream-pin build or whole-repository build is claimed.

## Notices

`LICENSE` and `NOTICE` were read completely. The applicable `ATTRIBUTION.md` path search and the table's stated limits were checked. All three files are retained byte for byte in every experimental source tree and copied by reproduce.md.

| File | Bytes | SHA256 |
|---|---:|---|
| LICENSE | 11345 | `746bc52848eabf8765635fe532e0680756a10b18e7b3fb26e7433ab4edf34034` |
| NOTICE | 7128 | `42b1821f19a6aaa25e6811d22ab8f2fdc6433d4a37bc810b1cfafa5b6dd6b0b6` |
| ATTRIBUTION.md | 50635 | `698fb76c8d80b2ed78ebd48b271f2ee5815b3654fb8ec5c699b21b16ce0d9698` |

The repository is copyright 2026 Anthropic, PBC, under Apache-2.0, with Mathlib and other third-party acknowledgments in NOTICE. None of the 41 selected paths occurs as a specific row in ATTRIBUTION.md, and no selected Lean file has an explicit Copyright/Authors header. This is not evidence that all its ideas or code are original: section 5 of the attribution document limits the coverage of its tracing. Preserve the complete notices rather than inventing per-file authors. Modified files have Worker 159's explicit compatibility, universe or cleanup notice; existing source text and names are preserved except for the recorded patches. Private adapter files are newly authored by Worker 159; the prime/discriminant/residue-cardinality route is credited to Worker 35, and the secondary endpoint qualification to Worker 65. No peer has independently approved this audit by offering those suggestions.

## Current-source snapshot

The retained snapshot is registered as `anthropic-flt-chebotarev-upstream-status-2026-10-25`, content SHA256 `b6d0824afb6eb67a0f70c7c1e3fd888329273f685079146d340ae17887b1dc87`. Its directory is `literature/Anthropic FLT Chebotarev audit - upstream head and complete issue snapshot 2026-10-25`. `retrieved.txt` records `2026-10-25T16:34:00.735694+00:00`. `head.json` gives main commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. `issues.json` contains all eleven issue/PR bodies then returned by the GitHub API, and `comments-1.json`, `comments-7.json`, `comments-8.json`, `comments-10.json`, `comments-11.json` contain every nonempty comment thread according to that response. All those bodies/comments were read in full.

No Chebotarev-specific proof defect was identified in this bounded snapshot. [Issue 10](https://github.com/anthropics/fermats-last-theorem/issues/10) and [issue 8](https://github.com/anthropics/fermats-last-theorem/issues/8) describe build failures; their discussion attributes the failures to memory-map limits and reports successful builds after increasing the limit. The issues remained open in this snapshot. Issue 6 concerns packaging/heavy imports. Issue 2's title alleges a bug but its body supplies no mathematical counterexample. [PR 11](https://github.com/anthropics/fermats-last-theorem/pull/11), closed in the snapshot, identifies a stale comparator WORK directory that can reuse artifacts from another checkout and proposes rejecting that conflict. It does not establish an error in a mathematical proof. Our checks use the project's Lean service, not that comparator; they make no assertion about the comparator's whole-repository result.

The source-specific local errata file `notes/errata/anthropic-flt-complete-lean-source-6e837e75.md` was not present in the supplied Library/project note locations. The bounded issue review is not a guarantee that no other defect or erratum exists.
