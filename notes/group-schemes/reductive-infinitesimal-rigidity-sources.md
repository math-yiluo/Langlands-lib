# Nilradical reflection for reductive groups: infinitesimal-rigidity sources

Worker 749, 17 November 2026.

This note records a bounded source audit for the proof task of
[`ReductiveNilradicalIsomorphismReflectionStatement`](../../Langlands/GroupScheme/Reductive/ReductiveNilradicalIsomorphismReflectionStatement.lean)
([statement explanation](../../Langlands/GroupScheme/Reductive/ReductiveNilradicalIsomorphismReflectionStatement.md)),
Task `295faf6f-5322-48e7-a9fd-ef01550954ac`, revision 1. It locates where SGA 3
proves the analogous lifting statement for reductive groups and which inputs that
proof uses. It also records the intrinsic deformation-theoretic formulation. It
supplies no Lean proof. It does not show that the target is unprovable under the
task's independence constraint.

## The target and its consumer

For every commutative local ring `R` with nilradical `N`, and affine reductive
group schemes `G`, `H` over `Spec R`, the statement asks that an isomorphism of
the pullbacks to `R / N` imply `Nonempty (G ≅ H)`. Only existence is required;
the reduction of the isomorphism is not prescribed. `N` need not be nilpotent.
For reduced `R` the statement is trivial, so its content concerns non-reduced
local rings.

- `localSplitIsomorphismTheorem_of_nilradicalReflection`
  ([`Reductive/LocalSplitNilradicalIsomorphismReduction.lean`](../../Langlands/GroupScheme/Reductive/LocalSplitNilradicalIsomorphismReduction.lean),
  lines 25–29) combines the target with the published reduced theorem
  `localSplitReducedIsomorphismTheorem` to prove
  `LocalSplitIsomorphismTheoremStatement`. That is row D4 of the
  [family-8 ledger](ledger-family-8-relative.md), with status O.
- Constraint 2 of the task requires the proof to be independent of
  `LocalSplitIsomorphismTheoremStatement` and of results whose proofs depend on it.
- `nilIdealHomIsomorphism`
  ([`Reductive/NilIdealHomIsomorphism.lean`](../../Langlands/GroupScheme/Reductive/NilIdealHomIsomorphism.lean))
  proves that a **supplied** homomorphism with smooth source is an isomorphism if
  it is one modulo a nil ideal. The open part of the target is therefore to
  construct a homomorphism `G → H` lifting an isomorphism over `R / N`.

## Where SGA 3 proves the analogous lifting

Source: SGA 3, Exposé XXIV, Gille–Polo reedition. The registered source is
`sga3-tome3-exposes-xix-xxvi-gille-polo-2024`, file `Exp24-13oct24.pdf`. Each
entry gives the printed page, then the PDF page.

| Passage | Content and inputs used |
| --- | --- |
| Cor. 1.12, p.221 / PDF 7 | `S` henselian local, `G` reductive, `G'` smooth affine with connected fibres, `s` the closed point: every `κ(s)`-isomorphism `G_s ≃ G'_s` comes from an `S`-isomorphism `G ≃ G'`. The sentence before it (p.220 / PDF 6) deduces it from Cor. 1.8 by Hensel's lemma (Exp. XI, 1.11). |
| Cor. 1.8, p.219 / PDF 5 | For `G` reductive and `H` smooth affine with connected fibres, `Isom_{S-gr.}(G, H)` is representable by a smooth separated `S`-scheme. The proof restricts to the open locus where `H` is reductive (Exp. XIX, 2.6). |
| Cor. 1.9, p.220 / PDF 6 | For `G`, `G'` reductive, `F = Isom_{S-gr.}(G, G')` is representable by a smooth separated `S`-scheme. The proof restricts to the open locus where `G` and `G'` have the same type. On that locus it uses **Exp. XXIII, 5.6**: `F` is a principal homogeneous sheaf under `Aut_{S-gr.}(G)`, locally trivial for the étale topology. Representability is then deduced through `Autext(G)` (Exp. X, 5.5) and the affineness of `ad(G)`. Smoothness is not argued separately; `F` is étale-locally isomorphic to the scheme `Aut_{S-gr.}(G)` of Thm. 1.3. |
| Thm. 1.3, p.218 / PDF 4 | `Aut_{S-gr.}(G)` is representable by a smooth separated `S`-scheme, with `1 → ad(G) → Aut → Autext → 1`. The proof deduces 1.3 from Lemma 1.4 for split `G` and then uses étale-local splitting (Exp. XXII, 2.3) and descent. |
| Lemma 1.4, p.218 / PDF 4; Lemma 1.5 and §1.5.1–1.5.2, pp.218–219 / PDF 4–5 | For a pinned split `G`, `Aut_{S-gr.}(G) = a(E_S) · ad(G)`. Lemma 1.5 shows that two pinnings are conjugate by a unique inner automorphism. |
| §1.0, p.216 / PDF 2; §1.2, p.217 / PDF 3 | The map `a : E_S → Aut_{S-gr.}(G)` realizes automorphisms of the pinned root datum through **Exp. XXIII, 5.5**. Full faithfulness of the pinned-group-to-root-datum functor is cited from **Exp. XXIII, 4.1**. |

Thus the SGA 3 proof of smoothness of the isomorphism scheme rests on the
isomorphism theorem of Exp. XXIII (4.1, 5.5, 5.6). Over a local base these are
the inputs that `LocalSplitIsomorphismTheoremStatement` formalizes. The target
is not literally a case of Cor. 1.12: `R` is not assumed henselian, and the
hypothesis concerns `R / N` rather than the residue field. On the smooth-`Isom`
route, the step from `R / N` to `R` is the lifting of a section along a nil
ideal. That step is generic and is not where the dependency lies.

## The intrinsic formulation: SGA 3, Exposé III

Source: SGA 3, Exposé III, Gille–Polo reedition. The registered source is
`sga3-expose-iii-gille-polo-2024`, file `Exp3-14oct24.pdf`.

| Passage | Content |
| --- | --- |
| Thm. 3.5, p.140 / PDF 40 | For ideals `I ⊇ J` with `I · J = 0` and `X` flat over `S`, group laws on `X` lifting a given group law on `X_J` are classified as follows. Suppose some morphism `X ×_S X → X` induces the group law of `X_J`. Then a lifting group law exists if and only if an obstruction class in `H³(X_0, L_0)` vanishes. In that case, the lifts modulo `S`-automorphisms of `X` inducing the identity on `X_J` form a principal homogeneous set under `H²(X_0, L_0)`. |
| Cor. 3.7, p.141 / PDF 41 | For a smooth affine `S_J`-group `X_J`, the smooth `S`-groups reducing to `X_J` are considered up to isomorphism inducing the identity on `X_J`. They form an empty set or a principal homogeneous set under `H²(X_0, Lie(X_0/S_0) ⊗ J)`. |
| Cor. 3.8(i), p.141 / PDF 41 | Let `I` be nilpotent and `X_0` a smooth affine `S_0`-group. Suppose `H²(X_0, Lie(X_0/S_0) ⊗ I^{n+1}/I^{n+2}) = 0` for all `n ≥ 0`. Then two smooth `S`-groups reducing to `X_0` are isomorphic, by an isomorphism inducing the identity on `X_0`. |
| Cor. 3.10, p.142 / PDF 42 | Over the dual numbers on `S_0`, every smooth deformation of `X_0` is trivial if and only if `H²(X_0, Lie(X_0/S_0)) = 0`. N.D.E. (72) records that this is used in XXIV 1.13. |

Suppose `N` is nilpotent. Use the given isomorphism to view `G` and `H` as smooth
affine deformations of `X_0 = G_{R/N}`. Then Cor. 3.8(i) gives `G ≅ H`, provided
`H²(X_0, Lie(X_0/S_0) ⊗ N^{n+1}/N^{n+2})` vanishes for all `n ≥ 0`. This is
Hochschild cohomology over the reduced local ring `R / N`, which need not be a
field. The coefficient modules `N^{n+1}/N^{n+2}` need not be free. When `N` is
nil but not nilpotent, one first descends the isomorphism over `R / N` to
`R / J` for a finitely generated ideal `J ⊆ N`, which is then nilpotent. This
finite-presentation reduction is again generic.

## How SGA 3 obtains the vanishing

| Passage | Content |
| --- | --- |
| XXIV Cor. 1.13, p.221 / PDF 7 | For a field `k` and a reductive `k`-group `G`: (i) if `G` is adjoint, `H¹(G, Lie(G/k)) = 0`; (ii) `H²(G, Lie(G/k)) = 0`. The text derives (ii) from Cor. 1.12 applied over the dual numbers on `k`, together with III 3.10. |
| XXIV Rem. 1.14(i), p.221 / PDF 7 | The `H¹` assertion was known (Chevalley). The `H²` assertion had been proved by Chevalley in most cases of the classification; no reference is given there. |
| XXIV Rem. 1.14(ii), p.221 / PDF 7 | 1.13 together with the uniqueness theorem over an algebraically closed field is "essentially equivalent" to the uniqueness theorem. A direct proof of 1.13 would give a way to deduce the general uniqueness theorem from Chevalley's uniqueness theorem over a field. |
| XXIV N.D.E. (6), p.221 / PDF 7 | The original stated 1.13(i) without the adjoint hypothesis. For `G = SL_p` in characteristic `p`, `H¹(G, Lie(G/k)) ≠ 0`. |
| XXIV N.D.E. (8), p.221 / PDF 7 | For trivial coefficients `k`, `Hⁱ(G, k) = 0` for `i > 0` by a theorem of Kempf, citing Jantzen 1987, II 4.5 and 4.11. |

## Consequence for the task

- In SGA 3, the infinitesimal rigidity statement (XXIV 1.13(ii)) is derived
  **from** the isomorphism theorem, not conversely. Rem. 1.14(ii) presents a
  direct proof as a possible new route to the general uniqueness theorem. By the
  consumer above, any proof of the target, combined with the published reduced
  theorem, proves `LocalSplitIsomorphismTheoremStatement`.
- Under constraint 2, the SGA 3 route through XXIV 1.3, 1.8 and 1.9 is
  therefore not an independent justification: it invokes XXIII 4.1, 5.5 and 5.6.
  The intrinsic route through III 3.7–3.8 needs the `H²` vanishing above over the
  reduced local ring `R / N`. XXIV 1.13 concerns fields only. Apart from the
  case-by-case results attributed to Chevalley in Rem. 1.14(i), these sources
  obtain the vanishing only through the isomorphism theorem. They give no
  statement over a non-field base such as `R / N`.
- A smoothness-of-`Isom` interface (an isomorphism scheme with smooth parameter
  for affine reductive groups over a local ring) is the content of XXIV 1.8–1.9.
  In SGA 3, that content is proved from XXIII 5.6. These sources therefore do
  not give such an interface an independent proof, and assuming it does not by
  itself supply an independent route. As of 17 November 2026, Worker
  869 has staged such an interface,
  `ReductiveSmoothIsomorphismSchemeExistenceStatement`, as candidate
  `fa4c32bc-2a86-40cf-8960-534c21614e0a`. That candidate is not yet accepted.
- The passage from a nil ideal to a finitely generated nilpotent one, and the
  lifting of sections of smooth schemes along nil ideals, are generic. They are
  not the obstacle.
