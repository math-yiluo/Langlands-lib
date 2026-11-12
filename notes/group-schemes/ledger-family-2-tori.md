# Group-scheme ledger, family 2: tori and groups of multiplicative type

Author: Worker 3483, 10 November 2026, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). This note is the source-to-declaration
ledger for family 2 of that program's contract. Family 2 covers:

- finite-rank split tori, their character and cocharacter lattices and the perfect pairing;
- diagonalizable groups and groups of multiplicative type, including finite non-smooth ones;
- tori in smooth groups: images, centralizers, normalizers, extensions;
- field tori and the Galois action on their lattices;
- finite separable Weil restriction of `𝔾_m`, with the real Deligne torus `Res_{ℂ/ℝ} 𝔾_m`;
- norm-one tori, and the central-torus results that the program needs.

It describes Library commit `e449cde988d4e97ab280b8d4d11262887ccc26e0` and environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. All Lean names are in `Langlands.GroupScheme`
unless a namespace is shown. Module paths are relative to `Langlands/GroupScheme/` in that
commit, except paths beginning `Shimura/`, which are relative to `Langlands/`. "Field
group" means a group scheme over `Spec k` for a field `k : Type u`.

General results on maximal tori (existence, base change, conjugacy, finite-field and
Henselian versions) belong to families 4 and 8 of the program and are not listed here. The
only maximal-torus rows here are the central-torus results F6–F7 and the reflection result
F8.

## Status codes and evidence

Each row gives the source assertion with its locator, the exact Lean statement and its
hypotheses, a status, the evidence, and the owner task.

- **D (definition or internal result).** A published construction, or a published
  theorem that is not a proposition declaration, with the hypotheses listed in the row.
  The evidence is its module path. No owner task is needed.
- **P (published proof).** The Library at the commit above contains a theorem whose type is
  exactly the statement. For a statement with parameters, the row lists the hypotheses
  under which the theorem proves it. The evidence is that theorem and its module path. The
  author also type-checked `example : S := proof` for every P row in a private module.
  That check passed with no errors or warnings, but it is not public evidence. No further
  proof work or owner task is needed.
- **C (composite, not published).** No published theorem has the statement as its type.
  However, a term built only from published theorems has that type: the author type-checked
  it in the same private module, and its axioms are `propext`, `Classical.choice` and
  `Quot.sound`. The composite is not an accepted artifact. The row names the owner task,
  or says that there is none. A projection out of a published conjunction is also listed
  as C: what is missing is then a named wrapper theorem, not mathematics.
- **O (open).** No published proof and no composite from published results is known.
- **G (gap).** No Lean declaration of the source assertion was found.

The labels "accepted" and "published" are used only for artifacts that passed independent
review.

Source locators use these registered sources, cited by source id:
- `milne-2017-algebraic-groups`: J. S. Milne, *Algebraic Groups* (2017). PDF page = printed
  page + 16.
- `milne-2022-algebraic-groups`: the 2022 corrected reprint. PDF page = printed page + 11.
- `conrad-2014-reductive-group-schemes`: B. Conrad, *Reductive group schemes* (2014).
  Printed page = PDF page.
- `conrad-gabber-prasad-2015-pseudo-reductive`: Conrad, Gabber and Prasad,
  *Pseudo-reductive groups*, 2nd edition (2015). PDF page = printed page + 26.
- `kaletha-prasad-2023-bruhat-tits-new-approach`: Kaletha and Prasad, *Bruhat–Tits theory:
  a new approach* (2023). PDF page = printed page + 31.
- `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: the Clay Mathematics
  Proceedings volume 4 (2005) containing Milne's *Introduction to Shimura varieties*. PDF
  page = printed page + 12.
- `borel-tits-1965-groupes-reductifs`: Borel and Tits, *Groupes réductifs*, Publ. Math.
  IHÉS 27 (1965). Journal page numbers are given.

The author re-read every locator below in the original source for this note, on 10 November
2026, and checked that the cited item is on the cited page.

## A. Split tori, lattices and the pairing

**A1. Split tori.** Source: Milne 2017, Definition 12.14, printed p.236 (PDF 252);
Conrad, Appendix B.1, p.280, and Definition 3.1.1, p.81.
- Lean (`Torus/Split`): `splitTorus S I`, for a scheme `S` and a type `I` with `[Finite I]`,
  is the finite product of copies of `𝔾_m` over `S`. `IsSplitTorus G` means
  `∃ (I : Type u) (_ : Finite I), Nonempty (G ≅ splitTorus S I)`.
- Finite rank is part of the definition: it is not inferred from freeness of a lattice.
  The base `S` is arbitrary.
- Status D.

**A2. Characters, cocharacters and the pairing.** Source: Milne 2017, §12.a, printed p.230
(PDF 246); Theorem 12.9, printed p.233 (PDF 249); Example 12.15, printed p.236 (PDF 252).
- Lean (`Torus/Lattice`): `characterLattice T := T ⟶ Gm S` and
  `cocharacterLattice T := Gm S ⟶ T` for a commutative group scheme `T` over any `S`.
  Over `Spec k` with `k` an integral domain, `gmEndEquiv k : (Gm ⟶ Gm) ≃+ ℤ`, and
  `latticePairing T χ ν = gmEndEquiv k (ν ≫ χ)`.
- For the standard split torus `splitTorus (Spec k) I`, with `k` an integral domain and `I`
  finite, `splitTorus.characterLatticeEquiv k I` and `splitTorus.cocharacterLatticeEquiv k I`
  identify both lattices with `I → ℤ`. A split torus given only by `IsSplitTorus` gets
  these identifications after transport along its chosen isomorphism; no packaged
  equivalence for that case is named here.
- Status D.

**A3. Endomorphisms of `𝔾_m`.** Source: Milne 2017, 2.22, printed p.46 (PDF 62), over a
field.
- Lean: `Gm.EndomorphismsStatement` (`Torus/GmEndomorphismsStatement`). Hypotheses: a
  commutative ring `R` with `IsDomain R`. Conclusion: `n ↦ multiplication (Gm (Spec R)) n`
  (the `n`-th power map) is a bijection from `ℤ` onto the endomorphisms of `𝔾_m`.
- Scope: integral domains instead of fields.
- Status P: `Gm.endomorphismsStatement` (`Torus/GmEndomorphismsProof`).

**A4. The pairing of a split torus is perfect.** Source: as A2.
- Lean: instance `splitTorus.isPerfPair_latticePairing` (`Torus/Lattice`), for `k` an
  integral domain and `I` finite.
- The finite separable Weil restrictions have their own perfectness theorems (E2).
- Status D (a published instance).

**A5. Homomorphisms into a split torus are determined by characters.** Source: Milne 2017,
Theorem 12.9(a), printed p.233 (PDF 249).
- Lean (`Torus/CharacterMapHom`), over `Spec k` with `k` an integral domain, `T` any
  commutative group scheme and `T'` a split torus:
  `IsSplitTorus.existsUnique_hom_of_characterMap` says that every additive map
  `characterLattice T' →+ characterLattice T` is the character pullback of exactly one
  homomorphism `T ⟶ T'`. `IsSplitTorus.hom_ext_of_characters` (`Torus/CharacterIsomorphism`,
  any base) says that characters separate homomorphisms into a split torus.
- Scope: this is full faithfulness for split targets only. No functor or equivalence of
  categories is packaged.
- Status D.

**A6. Split tori are split solvable.** Source: Milne 2017, Definition 12.14 and the
following paragraph, printed p.236 (PDF 252); CGP, Section B.1, printed p.561 (PDF 587).
- Lean: `SplitTorusSplitSolvableStatement` (`Torus/SplitSolvableStatement`). Hypotheses: a
  field group `T` with `IsSplitTorus T`. Conclusion: `IsSplitSolvableGroupScheme T`.
- Status P: `splitTorusSplitSolvable` (`Torus/SplitSolvableProof`).

**A7. Split tori are reductive.** Source: Milne 2017, Definition 12.14, printed p.236 (PDF
252), and Corollary 19.18, printed p.401 (PDF 417); Conrad, Definition 3.1.1, p.81.
- Lean: `IsSplitTorus.ReductiveStatement` (`Torus/SplitReductiveStatement`), the
  conjunction of:
  - `IsSplitTorus.IsConnectedReductiveStatement`: a split field group is connected
    reductive;
  - `IsSplitTorus.IsReductiveStatement`: over every scheme `S`, a split torus is reductive
    (Conrad 3.1.1).
- Status P: `IsSplitTorus.reductiveStatement` (`Torus/SplitReductiveProof`).

**A8. Weyl images of split tori are finite.** Source: Milne 2017, Theorem 12.36 and
Corollary 12.40, printed pp.243–244 (PDF 259–260).
- Lean: `SplitTorusWeylImageFiniteStatement` (`Torus/WeylImageFiniteStatement`).
  Hypotheses: a field group `G` with `IsAffineHom` and `LocallyOfFiniteType` structure
  map, a split torus `T` and a closed subgroup `i : T ⟶ G`. Conclusion:
  `Finite (weylImage i)`.
- Status P: `splitTorusWeylImageFinite` (`Torus/WeylImageFinite`).

## B. Tori, diagonalizable groups and multiplicative type over fields

**B1. Tori.** Source: Milne 2017, Definition 12.14, printed p.236 (PDF 252).
- Lean: `IsTorus T` (`Torus/Lattice`): `T` becomes a split torus after base change to some
  field extension `K/k`. The extension need not be finite, algebraic or separable;
  `torusFiniteGaloisSplitting` (D1) shows that a finite Galois one exists.
- Proved properties, for every field: `IsTorus.smooth`, `IsTorus.connectedSpace`
  (`Torus/Geometry`), `IsTorus.isConnectedReductive_of_fieldSplitting`
  (`Torus/ConnectedReductive`) and `IsSplitTorus.isTorus` (`Torus/Lattice`).
- Status D.

**B2. Diagonalizable groups `D(Λ)`, including finite non-smooth ones.** Source: Conrad,
Appendix B.1, p.280; Milne 2022, Definition 12.7 and Theorem 12.9, printed pp.233–234 (PDF
244–245).
- Lean (`Torus/Diagonalizable`): `Diagonalizable.groupScheme R Λ = Spec R[Λ]` for any
  commutative ring `R` and any abelian group `Λ`; no finiteness or freeness of `Λ` is
  assumed. `Diagonalizable.splitIso` identifies it with `splitTorus (Spec R) I` when
  `Λ ≃ ℤ^I`.
- Finite parts (`Torus/DiagonalizableDecomposition`): for `Λ ≃ ℤ^I × A`,
  `Diagonalizable.splitFiniteIso` gives `D(Λ) ≅ 𝔾_m^I × D(A)`; the instance
  `Diagonalizable.isFinite` makes `D(A)` finite over `Spec R` for finite `A`. No
  smoothness of `D(A)` is claimed: for `A = ℤ/p` in characteristic `p`, `D(A) = μ_p` is
  not smooth. The group `mu S n` (`Multiplicative`) is the `n`-torsion of `𝔾_m`.
- Kernels (`Torus/KernelDiagonalizable`, `Torus/HomKernelDiagonalizable`): over an
  integral domain, the scheme-theoretic kernel of a character `a` of a split torus is
  `Diagonalizable.kernelDiagonalizableIso : ker a ≅ D(X^*(T)/ℤa)`, and the kernel of a
  homomorphism of split tori is `D` of the cokernel of character pullback. Torsion,
  including `p`-torsion, is kept.
- Status D.

**B3. Groups of multiplicative type.** Source: Milne 2017, Definition 12.17, printed p.236
(PDF 252).
- Lean: `IsMultiplicativeType G` (`Torus/MultiplicativeType`): for some field extension
  `K/k` and some finitely generated `Λ`, `G_K ≅ D(Λ)`. No smoothness, reducedness or
  connectedness is assumed.
- Proved properties:
  - `IsTorus.isMultiplicativeType` (`Torus/MultiplicativeType`);
  - `IsMultiplicativeType.geometry` (`Torus/MultiplicativeTypeGeometry`): `G` is affine,
    locally of finite type and commutative;
  - `IsMultiplicativeType.of_isClosedSubgroup` (`Torus/MultiplicativeTypeSubgroups`):
    closed subgroups are of multiplicative type;
  - `IsMultiplicativeType.of_fppfHom` (`Torus/MultiplicativeTypeQuotients`): the target
    of a flat, surjective, locally finitely presented homomorphism is of multiplicative
    type;
  - `IsMultiplicativeType.exists_torus_finiteQuotient` (`Torus/MultiplicativeTypeStructure`):
    `G` has a closed torus `T` with a finite fppf quotient `G/T`.
- Status D.

**B4. Closed subgroups of diagonalizable groups are diagonalizable.** Source: Milne 2022,
Definition 12.7 and Theorems 12.8 and 12.9(a),(c), printed pp.233–234 (PDF 244–245).
- Lean: `Diagonalizable.ClosedSubgroupPresentationStatement`
  (`Torus/ClosedSubgroupPresentationStatement`). Hypotheses: a field `k`, a finitely
  generated abelian group `Λ`, and a closed subgroup `i : H ⟶ D(Λ)`. Conclusion: `H ≅ D(Λ')`
  for some finitely generated `Λ'`.
- Status P: `Diagonalizable.closedSubgroupPresentation` (`Torus/ClosedSubgroupPresentationProof`).

**B5. Fixed points of a diagonalizable action on a smooth group are smooth.** Source: CGP,
Proposition A.8.10(2), printed pp.547–548 (PDF 573–574), for an acting group with linearly
reductive geometric fibres, such as `D(Λ)` with `Λ` finitely generated. The Lean statement is
the case of a field and an action by group automorphisms.
- Lean: `Diagonalizable.FixedSubgroupSmoothStatement` (`Torus/DiagonalizableFixedSmoothStatement`).
  Hypotheses: a field `k`, a finitely generated `Λ`, a field group `G` that is **smooth**
  and has affine structure map, an action `a` of `D(Λ)` on `G`, and a closed subgroup
  `j : C ⟶ G` representing the fixed subgroup functor of `a`. Conclusion: `C` is smooth.
- The smoothness of `G` is essential: the trivial action on `α_p` in characteristic `p` has
  fixed subgroup `α_p`. Representability is an input, not a conclusion.
- Status P: `Diagonalizable.FixedSmooth.fixedSubgroupSmooth`
  (`Torus/DiagonalizableFixedSmoothProof`).

**B6. Smooth action relations on diagonalizable cocycle models.** Source: CGP, proof of
Proposition A.8.12, printed p.554 (PDF 580), using A.8.10(2). The Lean statement is a
derived specialization.
- Lean: `Diagonalizable.CocycleModelActionRelationSmoothStatement`
  (`Torus/CocycleModelActionRelationSmoothStatement`). Hypotheses: a field `k`, a finitely
  generated `Λ`, a smooth field group `G` with affine structure map, an action `a` of
  `D(Λ)` on `G`, and a cocycle model `M` of `a` whose scheme is affine and locally of
  finite type over `k`. Conclusion: the action relation `G × M → M × M`,
  `(g, x) ↦ (g • x, x)`, is smooth.
- Status P: `Diagonalizable.cocycleModelActionRelationSmooth`
  (`Torus/CocycleModelActionRelationSmoothProof`).

**B7. Connectedness of torus-stable subgroups containing the fixed points.** Source: CGP,
Proposition 2.1.12(2),(3), printed pp.59–60 (PDF 85–86), as used in the proof of part (b) of
Proposition 3.3.10. That proposition is stated on printed pp.112–113 (PDF 138–139), and the
proof of (b) is on printed p.114 (PDF 140). The Lean statement is derived.
- Lean: `Torus.SolvableFixedContainmentConnectedStatement`
  (`Torus/SolvableFixedContainmentConnectedStatement`). Hypotheses:
  - a field group `H` that is smooth, affine, connected and solvable on all tests
    (`RelativeRoot.IsSolvableScheme H`);
  - a split torus `S` with an action `c` on `H`;
  - a subgroup functor `F` of `H`, stable under `c`, containing the fixed subgroup of `c`;
  - a closed subgroup `q : C ⟶ H` representing `F`, with `C` smooth.

  Conclusion: `C` is connected.
- Status P: `Torus.solvableFixedContainmentConnected`
  (`Torus/SolvableFixedContainmentConnectedProof`). The algebraically closed case,
  `Torus.SolvableFixedContainmentConnectedAlgClosedStatement`, is a special case. Its proof
  is the published `Torus.connectedSpace_of_isAlgClosed`
  (`Torus/SolvableFixedAlgClosedCore`).

**B8. Endomorphisms of a torus over an algebraically closed field.** Source: Milne 2017,
proof of Theorem 17.48, printed p.367 (PDF 383), with Theorem 12.9(a)–(c), printed
pp.233–234 (PDF 249–250).
- Lean: `TorusEndomorphismDichotomyStatement` (`Torus/EndomorphismDichotomyStatement`).
  Hypotheses: `k` algebraically closed, a torus `T` and an endomorphism `f`. Conclusion:
  `f` is surjective, or there is a cocharacter `ν` that is a closed subgroup with
  `ν ≫ f = 0`.
- Status P: `torusEndomorphismDichotomy` (`Torus/EndomorphismDichotomy`).

**B9. Homomorphisms between tori and unipotent groups.** Source: Milne 2017, Corollary
14.18(b), printed p.284 (PDF 300).
- Lean (`Unipotent/TorusHom`): `IsTorus.hom_eq_zero_of_isUnipotent`. Hypotheses: field
  groups `S`, `U` with `U` affine, `IsTorus S` and `IsUnipotent U`. Conclusion: every
  homomorphism `S ⟶ U` is zero. `Torus/UnipotentHom` proves the reverse direction for split
  targets: `IsUnipotent.hom_eq_zero_of_isSplitTorus`.
- Status D (published theorems with these hypotheses).

## C. Tori inside smooth groups

**C1. The image of a torus is a closed torus.** Source: Milne 2017, Theorem 5.39, printed
p.108 (PDF 124), and §12.e after Definition 12.14, printed p.236 (PDF 252). The statement
is derived.
- Lean: `TorusImageClosedTorusStatement` (`Torus/ImageStatement`). Hypotheses: a field group
  `H` that is smooth with affine structure map, a torus `E` and a homomorphism
  `e : E ⟶ H`. Conclusion: a torus `Z`, a closed subgroup `j : Z ⟶ H` and `f : E ⟶ Z`
  with `f ≫ j = e`.
- Status P: `torusImageClosedTorusStatement` (`Torus/ImageProof`).

**C2. Centralizers of tori are smooth.** Source: Milne 2017, Corollary 13.10, printed p.257
(PDF 273), stated for group varieties (smooth groups).
- Lean: `TorusCentralizerSmoothStatement` (`Torus/CentralizerSmoothStatement`). Hypotheses:
  a field group `G` that is **smooth** with affine structure map, a torus `T`, a closed
  subgroup `i : T ⟶ G`, and a closed subgroup `j : C ⟶ G` representing the centralizer
  functor of `i`. Conclusion: `C` is smooth.
- Without smoothness of `G` this fails: in `𝔾_m × α_p` in characteristic `p`, the central
  `𝔾_m` has the whole non-smooth group as centralizer.
- Status P: `torusCentralizerSmooth` (`Torus/CentralizerSmoothProof`).

**C3. Normalizers of tori are smooth and closed.** Source: Milne 2017, Corollary 13.10,
printed p.257 (PDF 273), and Proposition 1.83, printed p.31 (PDF 47).
- Lean: `TorusNormalizerSmoothClosedStatement` (`Torus/NormalizerSmoothStatement`).
  Hypotheses: a **smooth** field group `G` with affine structure map, a torus `T` and a
  closed subgroup `i : T ⟶ G`. Conclusion: the normalizer functor of `i` has a smooth
  closed representative (`HasSmoothClosedRepresentative`). Here representability is part of
  the conclusion.
- Status P: `torusNormalizerSmoothClosed` (`Torus/NormalizerSmoothProof`).

**C4. Extensions of a torus by a central torus.** Source: Milne 2017, Corollaries 12.41 and
12.42, printed p.244 (PDF 260), and Corollary 12.22, printed p.239 (PDF 255). Milne's 12.42
assumes the extension connected; here centrality replaces this.
- Lean: `CentralTorusExtensionStatement` (`Torus/CentralExtensionStatement`). Hypotheses: a
  field group `E`, a torus `Z` with a closed central subgroup `z : Z ⟶ E`, a torus `T`, and
  a homomorphism `p : E ⟶ T` with affine underlying morphism that is an fppf quotient of
  `E` by the range of `z`. Conclusion: `IsTorus E`.
- Status P: `centralTorusExtensionStatement` (`Torus/CentralExtensionProof`).

## D. Field tori and Galois actions on lattices

**D1. Every torus splits over a finite Galois extension.** Source: Milne 2017, Definition
12.14, Theorem 12.18 and Corollary 12.19, printed pp.236–238 (PDF 252–254).
- Lean: `TorusFiniteGaloisSplittingStatement` (`Torus/FiniteGaloisSplittingStatement`).
  Hypotheses: a field group `T` with `IsTorus T`. Conclusion: a field `K` with
  `FiniteDimensional k K`, `IsGalois k K` and `T_K` split.
- Status P: `torusFiniteGaloisSplitting` (`Torus/FiniteGaloisSplittingProof`). The published
  note [Field tori and rational centers](field-tori-central-progress.md) records its
  acceptance.

**D2. The Galois action on the lattices.** Source: Milne 2017, §12.a, printed p.230 (PDF
246), and §12.g, printed p.239 (PDF 255).
- Lean (`Torus/LatticeGalois`): `characterLattice.galoisRepresentation k K T` and
  `cocharacterLattice.galoisRepresentation k K T`, for commutative rings `k → K` and a
  commutative group scheme `T` over `Spec k`, are `Representation ℤ (K ≃ₐ[k] K)` on
  `X^*(T_K)` and `X_*(T_K)`, by transport along `Spec σ`.
- Status D.

**D3. Continuity of the Galois action.** Source: Milne 2022, §12.g, printed p.239 (PDF 250).
- Lean: `TorusLatticeGaloisContinuityStatement` (`Torus/LatticeGaloisContinuityStatement`).
  Hypotheses: an algebraic extension `E/k` and a commutative group scheme `T` over `Spec k`
  with `T_E` split. Conclusion: some finite-dimensional intermediate field `L` has the
  property that every `σ` fixing `L` acts trivially on `X^*(T_E)` and `X_*(T_E)`.
- Status P: `torusLatticeGaloisContinuity` (`Torus/LatticeGaloisContinuityProof`), published
  from candidate `faea411e-8f86-46be-ba5a-8be80ea8ce78` of Task 5263
  (`bfb511f7-800a-4ce4-afc4-cf2e243e9ff6`). Its proof is a new argument (a finite field of
  definition of the splitting isomorphism), not a composite.
- Continuity for the Weil restrictions of E2 and the norm-one tori of F1 is proved
  separately; see those rows.

**D4. Classification of multiplicative-type groups by Galois modules.** Source: Milne 2017,
Theorem 12.23, printed p.240 (PDF 256).
- Status G. No Lean statement of the anti-equivalence between groups of multiplicative
  type over `k` and finitely generated continuous `Gal(k_s/k)`-modules was found. A5 gives
  full faithfulness for split targets only. No owner task was found.

**D5. Smoothness of diagonalizable groups.** Source: Milne 2017, §12.b, opening paragraph,
printed p.230 (PDF 246), which fixes a **finitely generated** commutative group `M`, and
Remark 12.5, printed p.232 (PDF 248). For a field `k` with characteristic exponent `p` and a
finitely generated `M`: `D(M)` is smooth if and only if `M` has no `p`-torsion, connected
if and only if the only torsion in `M` is `p`-torsion, and smooth and connected if and only
if `M` is free (of finite rank, since `M` is finitely generated).
- Finite generation is essential. `Diagonalizable.groupScheme k Λ` of B2 is defined for
  every abelian group `Λ`; for `Λ` free of countably infinite rank it is not locally of
  finite presentation over `k`, so it is not smooth, although `Λ` is free.
- Status G. No Lean declaration of these criteria was found. B2 keeps non-smooth finite
  factors but does not characterize smoothness or connectedness. No owner task was found.

## E. Finite separable Weil restriction and the Deligne torus

**E1. Weil restriction of `𝔾_m`.** Source: Milne 2017, §2.i, 2.55, printed p.57 (PDF 73).
- Lean: `WeilGm.groupScheme A B` (`Torus/WeilRestriction`), for a commutative ring `A` and a
  commutative `A`-algebra `B` with `[Module.Finite A B] [Module.Projective A B]`. Its points
  on a test scheme `T` are the units of `B ⊗_A Γ(T)`.
- Proved properties, under the same hypotheses:
  - `WeilGm.smooth` (`Torus/WeilRestriction`);
  - `WeilGm.baseChangeIso` (`Torus/WeilRestrictionBaseChange`): base change along
    `A → A'` is the Weil restriction of `A' ⊗_A B`;
  - `WeilGm.splitIso` (`Torus/WeilRestrictionSplit`): for `B = A^I`, `I` finite, it is
    `splitTorus (Spec A) I`;
  - `WeilGm.decompositionIso` (`Torus/WeilRestrictionDecomposition`): a supplied algebra
    equivalence `A' ⊗_A B ≃ A'^I` splits the base change;
  - `WeilGm.decomposition_latticePairing_isPerfPair`: in that situation over a field, the
    pairing is perfect.
- `WeilGm.commGroupScheme` (`Torus/WeilRestrictionCommutative`) is the commutative version.
- Status D.

**E2. Finite separable field extensions: torus, permutation lattices, pairing.** Source:
Milne 2017, 2.61, printed p.59 (PDF 75) (motivating; the results are internal).
- Data: fields `k`, `K`, `Ω` with `[FiniteDimensional k K] [Algebra.IsSeparable k K]`, and
  `hsplit`: every `minpoly k x`, `x : K`, splits in `Ω`.
- Lean (`Torus/WeilRestrictionSeparable`):
  - `WeilGm.isTorus_of_finite_separable`: `Res_{K/k} 𝔾_m` is a torus (no `Ω` needed);
  - `WeilGm.separableEmbeddingIso`: its base change to `Ω` is
    `splitTorus (Spec Ω) (K →ₐ[k] Ω)`, and `WeilGm.separableEmbedding_card` says there are
    `[K : k]` embeddings;
  - `WeilGm.separableEmbeddingCharacterEquiv_galoisRepresentation` and its cocharacter
    analogue: the lattices are `(K →ₐ[k] Ω) → ℤ`, and `σ` acts by permuting embeddings;
  - `WeilGm.separableEmbeddingCharacterContinuousAction` and its cocharacter analogue:
    for a chosen discrete topology on the lattice, the action is continuous.
- `WeilGm.embedding_latticePairing_isPerfPair` (`Torus/WeilRestrictionEmbeddingLattices`):
  the pairing is perfect, given a finite set of embeddings and bijectivity of the canonical
  evaluation `Ω ⊗_k K → Ω^{K →ₐ[k] Ω}`.
- Scope: finite separable only. Purely inseparable restriction is not treated.
- Status D.

**E3. Induced tori are Weil restrictions.** Source: Kaletha–Prasad, §2.5(a), Definition
2.5.1 and the following paragraph, printed p.86 (PDF 117).
- Lean: `IsInducedTorus T` (`Torus/Induced`) asks for a finite Galois `E/k` splitting `T` and
  a `ℤ`-basis of `X^*(T_E)` permuted by the Galois group.
  `InducedTorusWeilDecompositionStatement` (`Torus/InducedWeilDecompositionStatement`).
  Hypotheses: `L/k` finite Galois, `T` commutative with `T_L` split, and
  `IsInducedTorus T`. Conclusion: for some intermediate fields `E_1, …, E_n` of `L/k`,
  `T ≅ Res_{(∏ E_i)/k} 𝔾_m`.
- Status P: `inducedTorusWeilDecomposition` (`Torus/InducedWeilDecompositionProof`).

**E4. The real Deligne torus `𝕊 = Res_{ℂ/ℝ} 𝔾_m` (milestone).** Source: Milne,
*Introduction to Shimura varieties*, in the Clay Proceedings volume 4 (2005), §2,
paragraph "Hodge structures as representations of S", printed p.282 (PDF 294); Milne 2017,
Definition 12.14, printed p.236 (PDF 252).
- Lean (namespace `Langlands.Shimura.DeligneTorus`; modules under `Shimura/Unitary/`):
  - `NonSplitTorusStatement` (`DeligneNonSplitStatement`): `groupScheme` is smooth, its base
    change to `ℂ` is a split torus, and `groupScheme` is not a split torus over `ℝ`.
    Status P: `nonSplitTorusStatement` (`DeligneNonSplitProof`). Non-splitting is the
    proved theorem `not_isSplitTorus_groupScheme`, not an input.
  - `ReductiveStatement` (`DeligneReductiveStatement`): `groupScheme` is connected
    reductive and reductive. Status P: `reductiveStatement` (`DeligneReductiveProof`).
  - `weilRestrictionIso : WeilGm.groupScheme ℝ ℂ ≅ groupScheme` (`DeligneWeilRestriction`).
  - `characterEquiv`, `cocharacterEquiv` (`DeligneLattices`): `X^*(𝕊_ℂ) ≅ ℤ × ℤ` and
    `X_*(𝕊_ℂ) ≅ ℤ × ℤ`. `characterEquiv_galoisRepresentation_conj` and
    `cocharacterEquiv_galoisRepresentation_conj`: complex conjugation acts by the swap.
    `characterLattice_galoisRepresentation_conj_ne_one`: the action is nontrivial.
- The construction lives in universe `0` (over `ℝ : Type`).

## F. Norm-one tori and central tori

**F1. Norms and norm-one tori.** Source: internal constructions.
- Lean: `WeilGm.norm A B` (`Torus/WeilRestrictionNorm`, `B` finite free over `A`), the
  determinant norm `Res_{B/A} 𝔾_m → 𝔾_m`. `WeilGm.normOne A B` (`Torus/WeilRestrictionNormOne`)
  is its scheme-theoretic kernel. For `K/k` finite separable,
  `WeilGm.normOne_isTorus_of_finite_separable` says it is a torus.
- `WeilGm.normOneSeparableEmbeddingCharacterContinuousAction` and its cocharacter analogue
  (`Torus/WeilRestrictionNormOneContinuity`): continuity of the Galois action on its
  lattices, under the data of E2 and a chosen discrete topology.
- Status D.

**F2. Lattices and anisotropy of norm-one tori.** Source: internal derivations; the
anisotropy convention is Borel–Tits (1965), Definition 4.23, printed p.93, compared with
Milne 2017, Definition 25.3, printed p.545 (PDF 561). The published note
[Norm-one tori: rational lattices and split rank zero](norm-one-rational-progress.md)
records the acceptance of the first two theorems.

Throughout, `k`, `K` are fields with `[FiniteDimensional k K]` and `N` is the norm-one torus
of `K/k`.
- `WeilGm.normOneRationalLatticesStatement k K` (`Torus/WeilRestrictionNormOneRationalStatements`):
  if `K/k` is separable, every character and every cocharacter of `N` over `k` is zero.
  Status P: `WeilGm.normOneRationalLattices` (`Torus/WeilRestrictionNormOneRationalProof`).
- `WeilGm.normOneAnisotropyStatement k K` (`Torus/WeilRestrictionNormOneAnisotropyStatement`):
  if `K/k` is separable, `IsAnisotropic N` (split rank zero). Status P:
  `WeilGm.normOneAnisotropy` (`Torus/WeilRestrictionNormOneAnisotropyProof`).
- `WeilGm.normOneGaloisFixedLatticesStatement k K Ω` (`Torus/WeilRestrictionNormOneFixedStatements`),
  for a further field `Ω`: if `K/k` is separable, `Ω/k` is normal and every `minpoly k x`
  splits in `Ω`, then five assertions hold: the Galois action on embeddings is transitive;
  the fixed vectors of the sum-zero and quotient embedding lattices are zero; and the fixed
  cocharacters and characters of `N_Ω` are zero. Status P:
  `WeilGm.normOneGaloisFixedLattices` (`Torus/WeilRestrictionNormOneFixedProof`).
- Components. The component statements carry no separability, normality or splitting
  hypothesis of their own. This note makes no claim about them beyond the hypotheses stated
  here.
  - `embeddingActionTransitiveStatement k K Ω`: Status P whenever `Normal k Ω`, by the
    published theorem `WeilGm.embeddingActionTransitive`
    (`Torus/WeilRestrictionNormOneFixedProof`), whose only hypothesis beyond the fields and
    algebra structures is `[Normal k Ω]`.
  - `normOneRationalCharacterVanishingStatement k K` and
    `normOneRationalCocharacterVanishingStatement k K` are C when `K/k` is separable: the
    projections `.1` and `.2` of `normOneRationalLattices k K hsep`.
  - The four components `embeddingSumZeroFixedStatement`, `embeddingQuotientFixedStatement`,
    `normOneCocharacterFixedStatement` and `normOneCharacterFixedStatement` (for `k K Ω`)
    are C under the three hypotheses of `normOneGaloisFixedLatticesStatement`, as
    projections of `normOneGaloisFixedLattices k K Ω hsep hnormal hsplit`.

  The author type-checked `WeilGm.embeddingActionTransitive` against its statement and all
  six projections in the private module. The four fixed-lattice components also follow from
  published component theorems in `Torus/WeilRestrictionNormOneFixedProof`, with their own
  hypotheses:
  - `WeilGm.embeddingSumZeroFixed` and `WeilGm.embeddingQuotientFixed`, assuming a nonempty
    set of embeddings and transitivity;
  - `WeilGm.normOneCocharacterFixed`, assuming separability, the splitting condition and the
    sum-zero result; `WeilGm.normOneCharacterFixed`, assuming the same with the quotient
    result instead.

  For the six C components, what is missing is only a named theorem under these
  hypotheses, not mathematics. No owner task exists or is needed.

**F3. Smoothness of the Galois norm.** Source: Kaletha–Prasad, proof of Lemma 2.5.12,
printed pp.89–90 (PDF 120–121).
- Lean: `GaloisNormSmoothnessStatement` (`Torus/GaloisNormSmoothness`). Hypotheses:
  `L/k` finite Galois, a commutative group scheme `T` over `k` with `T` and `T_L` affine,
  `T_L` locally of finite type, and `T_L` split. Conclusion: the algebraic norm
  `GaloisNorm.norm k L T` (`Torus/GaloisNorm`) is a smooth morphism.
- Status P: `GaloisNormSmoothnessProof.galoisNormSmoothness` (`Torus/GaloisNormSmoothnessProof`).

**F4. A smooth connected group without tori is unipotent.** Source: Milne 2017, Proposition
17.81, printed p.378 (PDF 394).
- Lean: `NoTorusUnipotentStatement` (`Torus/NoTorusUnipotentStatement`). Hypotheses: a
  field group `Q` that is smooth, affine and connected, such that every homomorphism from a
  torus to `Q` has trivial range. Conclusion: `IsUnipotent Q`.
- This is not Milne 14.18(b); that corollary is B9.
- Status P: `noTorusUnipotent` (`Torus/NoTorusUnipotent`).

**F5. Absence of tori is invariant under field extension.** Source: Milne 2017, Theorem
17.82, printed p.379 (PDF 395), with Proposition 17.81 and Corollaries 14.9 and 14.18(b),
printed pp.282–284 (PDF 298–300). The statement is derived.
- Lean: `NoTorusBaseChangeStatement` (`Torus/NoTorusBaseChangeStatement`). Hypotheses:
  fields `k`, `K` with `Algebra k K`, and a smooth field group `Q` with affine structure map
  such that every homomorphism from a torus over `k` to `Q` has trivial range. Conclusion:
  the same holds for tori over `K` mapping to `Q_K`.
- Status P: `noTorusBaseChange` (`Torus/NoTorusBaseChangeProof`), published from candidate
  `fed3b6b1-222c-4310-88ec-87c3aa172edb` of Task 5243
  (`054c9e79-c59d-4325-a96b-8c82a40df80b`). Its proof is the composite
  `noTorusBaseChangeReduction noTorusUnipotent` (`Torus/NoTorusBaseChangeReduction`,
  `Torus/NoTorusUnipotent`).

**F6. The quotient by a central maximal torus has no tori.** Source: Milne 2017, Theorem
17.82, printed p.379 (PDF 395), and Lemma 16.43, printed p.340 (PDF 356).
- Lean: `CentralMaximalTorusQuotientStatement` (`Torus/CentralMaximalQuotientStatement`).
  Hypotheses: a smooth field group `H` with affine structure map, a central maximal torus
  `j : Z ⟶ H`, and an fppf quotient `q : H ⟶ Q` by the range of `j`. Conclusion: every
  homomorphism from a torus to `Q` has trivial range.
- Status P: `centralMaximalTorusQuotientStatement` (`Torus/CentralMaximalQuotientProof`).

**F7. A central maximal torus stays maximal after field extension.** Source: Milne 2017,
Theorem 17.82, printed p.379 (PDF 395) (the central case of its proof).
- Lean: `CentralMaximalTorusBaseChangeStatement` (`Torus/CentralMaximalBaseChangeStatement`).
  Hypotheses: fields `k`, `K`, a smooth field group `H` with affine structure map, and a
  central maximal torus `j : Z ⟶ H`. Conclusion: `j_K` is a maximal torus of `H_K`.
- Status P: `centralMaximalTorusBaseChange` (`Torus/CentralMaximalBaseChangeProof`),
  published from candidate `16548b25-b004-4fd4-a202-fa6891fa2328` of Task 5243. Its proof is
  the composite `centralMaximalTorusBaseChangeReduction normalSubgroupQuotient
  centralMaximalTorusQuotientStatement` applied to the F5 composite
  (`Torus/CentralMaximalBaseChangeReduction`, `NormalSubgroupQuotientProof`,
  `Torus/CentralMaximalQuotientProof`).

**F8. Maximal tori are reflected along finite homomorphisms.** Source: Milne 2017,
Proposition 17.20, printed pp.357–358 (PDF 373–374), Theorem 17.82, printed p.379 (PDF 395),
and Definition 19.20, printed pp.401–402 (PDF 417–418). The statement is derived.
- Lean: `FiniteHomMaximalTorusReflectionStatement` (`Torus/FiniteHomMaximalityStatement`).
  Hypotheses:
  - connected reductive field groups `G`, `H` and `π : G ⟶ H` with finite underlying
    morphism;
  - a torus `T` with a closed subgroup `j : T ⟶ G`;
  - a maximal torus `i : S ⟶ H` and a homomorphism `f : T ⟶ S` whose underlying morphism
    is surjective, with `j ≫ π = f ≫ i`.

  Conclusion: `j` is a maximal torus.
- Status C: `finiteHomMaximalTorusReflection_of_torusImage torusImageClosedTorusStatement`
  (`Torus/FiniteHomMaximalityReduction`, `Torus/ImageProof`). No owner task was found; a
  TaskHub search for the statement name on 10 November 2026 returned no task. A
  variant, `FiniteHomMaximalTorusReflectionSmoothStatement`, is proved in
  `Torus/FiniteHomMaximalitySmooth`.

**F9. Centres of reductive groups are of multiplicative type.** Source: Milne 2017, §19.b,
paragraph "Reductive algebraic groups", printed p.400 (PDF 416), with Definition 12.17,
printed p.236 (PDF 252).
- Lean: `CenterMultiplicativeTypeStatement` (`Reductive/CenterMultiplicativeTypeStatement`).
  Hypotheses: a connected reductive field group `G` and `z : Z ⟶ G` with
  `IsSchemeTheoreticCenter z` (a closed subgroup whose subgroup functor is the centre of `G`
  on every test scheme). Conclusion: `IsMultiplicativeType Z`. The centre need not be smooth
  or connected.
- Status P: `centerMultiplicativeType` (`Reductive/CenterMultiplicativeTypeProof`), published
  from candidate `574605df-e99d-400a-a0eb-52e7a1114693` of Task 5242
  (`043f2527-205c-4cfc-b9b2-553de1010d9d`). Its proof is the composite
  `centerMultiplicativeTypeCentralizerReduction (algClosedMaximalTorusCentralizerReduction
  dynamicCentralizerReductive noTorusUnipotent solvableTorusQuotient)`
  (`Reductive/CenterMultiplicativeTypeReduction`,
  `Absolute/AlgClosedMaximalTorusCentralizerAssembly`, `Dynamic/CentralizerReductiveProof`,
  `Torus/NoTorusUnipotent`, `Absolute/SolvableTorusQuotientProof`).

## Conventions and scope

- `IsTorus` and `IsMultiplicativeType` allow any splitting extension. D1 then gives a finite
  Galois one for tori.
- Groups of multiplicative type are of finite type (Milne's convention); finite generation
  of `Λ` is explicit. Finite non-smooth factors such as `μ_p` are kept (B2, B3).
- Smoothness hypotheses on the ambient group are part of B5–B7, C1–C3 and F4–F7. For B5
  and C2–C3 they are necessary, by the examples given in those rows. For the other rows this
  note makes no claim that they are necessary.
- Weil restriction is treated for finite projective algebras in general and for finite
  separable field extensions in detail (E1, E2). Purely inseparable restriction is not
  used to replace finite separability.

## Remaining targets in family 2

- Gaps G: the Galois-module classification of multiplicative-type groups (D4) and the
  smoothness and connectedness criteria for `D(M)`, `M` finitely generated (D5). No owner
  tasks were found.
- Publication of the composite F8 (no owner task).
- Named theorems for the six C norm-one components of F2, if a consumer needs them.
