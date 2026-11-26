# Group-scheme ledger, family 6: Galois and central structure

This note, dated 10 November 2026, is the source-to-declaration
ledger for family 6 of the algebraic and reductive group-scheme program. Family 6 covers:

- the Galois action on the lattices of a torus;
- the star action on the absolute based root datum, and its relation to the Galois action;
- quasi-split groups and inner forms;
- centres and adjoint groups;
- derived groups and cocentres;
- central isogenies;
- simply connected covers and their root-data comparisons.

The original rows describe Library commit `e748734106ab2ee9de1cab1eb18a60e59593aac0`.
That version updated
A6, D9 and F3 from commit `e449cde988d4e97ab280b8d4d11262887ccc26e0`.
Row A9 records results checked on 18 November 2026. A10 was checked
at Library commit `1704ae21875deeabd17a51ced41447cc741572dd`.
Rows A11, B4 and B5 use the declarations at Library commit
`66a181ec9cda271c1ff0dcf555f386b52dc687c7`.

All Lean names are in `Langlands.GroupScheme` unless a namespace is shown. Module paths
are relative to `Langlands/GroupScheme/` in that commit. "Field group" means a group
scheme over `Spec k` for a field `k : Type u`.

## Status codes and evidence

Each row gives the source assertion with its locator, the exact Lean statement and its
hypotheses, a status and the evidence.

- **D (definition or internal result).** A published construction, or a published
  internal theorem that is not a proposition declaration, with the hypotheses listed in the
  row. The evidence is its module path.
- **P (published proof).** The cited Library commit contains a theorem whose type is
  exactly the statement. The evidence is that theorem and its module path. Every P row was also
  type-checked as `example : S := proof`, with no errors or warnings. No further proof work is
  needed.
- **C (composite, not published).** No published theorem has the statement as its type.
  However, a term built only from published theorems has that type: it was type-checked
  in the same way, and its axioms are `propext`, `Classical.choice` and
  `Quot.sound`. The composite is not itself in the Library.
- **O (open).** No published proof and no composite from published
  results is known. A proof outside the Library does not change the status.

The label "published" means: in the Library.

Source locators use these registered sources, cited by source id:
- `milne-2017-algebraic-groups`: J. S. Milne, *Algebraic Groups* (2017). PDF page = printed
  page + 16.
- `milne-2022-algebraic-groups`: the 2022 corrected reprint. PDF page = printed page + 11.
- `conrad-2014-reductive-group-schemes`: B. Conrad, *Reductive group schemes* (2014).
  Printed page = PDF page.
- `conrad-gabber-prasad-2015-pseudo-reductive`: Conrad, Gabber and Prasad,
  *Pseudo-reductive groups*, 2nd edition (2015). PDF page = printed page + 26.
- `kaletha-prasad-2023-bruhat-tits-new-approach`: Kaletha and Prasad, *Bruhat–Tits theory:
  a new approach* (2023).
- `borel-tits-1965-groupes-reductifs`: Borel and Tits, *Groupes réductifs* (1965).
- `borel-tits-1972-complements-groupes-reductifs`: Borel and Tits, *Compléments à l'article
  « Groupes réductifs »* (1972).

Locators marked (†) were re-read in the original for this note. Every other
locator is copied from the published Markdown of a module named in the row.

## A. Galois actions and the star action

**A1. Galois action on character and cocharacter lattices.** Source: Milne 2017, §12.a,
printed p.230, and §12.g, printed p.239.
- Lean: `characterLattice.galoisRepresentation` and `cocharacterLattice.galoisRepresentation`
  (`Torus/LatticeGalois`). They take fields `k`, `K` with `Algebra k K` and a commutative
  group scheme `T` over `Spec k`, and give `Representation ℤ (K ≃ₐ[k] K)` on `X^*(T_K)` and
  `X_*(T_K)` by transport along `Spec σ`.
- Status D.

**A2. Continuity of the Galois action on torus lattices.** Source: Milne 2022, §12.g,
printed p.239 (PDF 250) (†).
- Lean: `TorusLatticeGaloisContinuityStatement` (`Torus/LatticeGaloisContinuityStatement`).
  Hypotheses: an algebraic extension `E/k` and a commutative group scheme `T` over `Spec k`
  with `T_E` split. Conclusion: some finite-dimensional intermediate field `L` has the
  property that every `σ` fixing `L` acts trivially on `X^*(T_E)` and `X_*(T_E)`.
- Status P: `torusLatticeGaloisContinuity` (`Torus/LatticeGaloisContinuityProof`). Its proof is a new argument, not a composite:
  finite fields of definition of the splitting isomorphism
  (`Descent.FiniteStage.homModel`), then invariance of characters and, by the lattice
  pairing, of cocharacters.

**A3. Galois pinning data, the Galois action on the root datum, and the star action.**
Source: Milne 2022, §25.c, printed p.555 (PDF 566) (†), defines the `*`-action
`σ*α = w_σ(σα)`. Milne 2022, 23.75, printed p.513 (PDF 524), gives
`Aut(R) = W ⋊ Aut(R, base)`.
- Lean (`Reductive/StarAction`):
  - `GaloisPinningData k E G`, for `G` affine over `Spec k`, is the following data:
    - a `k`-torus `T` with a map `T ⟶ G`;
    - `G_E` connected reductive, with `T_E` a split maximal torus;
    - a reduced root datum of `(G_E, T_E)`;
    - a base and simple-root Lie trivializations.
  - `GaloisPinningData.galoisAction : (E ≃ₐ[k] E) →* Aut(root datum)` is the action through
    the lattices of `T` (A1).
  - `GaloisPinningData.starAction` is `galoisAction` followed by the based projection
    `SplitPinning.basedRootDatumProjection` (`Reductive/BasedRootDatumProjection`).
    `starAction_mul_galoisAction_inv_mem` proves that the two differ by a Weyl element.
- `Reductive/AbsoluteStarAction`: `GaloisPinningData.ofSeparableClosure` and
  `absoluteStarAction` give the star action of `Gal(k_s/k)` for a connected reductive `G`
  locally of finite type over `k`.
- Status D. These are the equivariant based root data exported for dual and L-groups.

**A4. Independence of the star action from the pinning data.** Source: Milne 2022, §25.c,
printed p.555 (PDF 566).
- Lean: `StarActionIndependenceStatement` (`Reductive/StarActionStatement`). Hypotheses:
  `G` affine and locally of finite type over a field `k`, an extension `E`, and two Galois
  pinning data `d`, `d'`. Conclusion: there are an `E`-point `g` and `φ : T_E ≅ T'_E` such
  that `g` conjugates the torus of `d` onto that of `d'` through `φ`. There is also an
  isomorphism `e` of root data with weight map `characterLattice.congr φ`. It preserves the
  bases and intertwines `d.starAction σ` with `d'.starAction σ` for every `σ`.
- Status P: `StarActionIndependence.starActionIndependence`
  (`Reductive/StarActionIndependenceProof`).
  Its proof is a new argument using published theorems: conjugacy of the two split maximal
  tori over `E`, comparison of root data, a Weyl correction to match the bases, and Galois
  descent of the conjugating point.

**A5. Continuity of the star action.** Source: as A4.
- Lean: `StarActionContinuityStatement` (`Reductive/StarActionStatement`). Hypotheses: `E/k`
  algebraic, `G` affine and locally of finite type, and Galois pinning data `d`.
  Conclusion: some finite-dimensional intermediate field `L` has the property that every
  `σ` fixing `L` has `d.galoisAction σ = 1` and `d.starAction σ = 1`.
- Status P: `starActionContinuity` (`Reductive/StarActionContinuityProof`). Its proof is a short new
  argument from the A2 theorem.

**A6. In the quasi-split case the star action is the Galois action.** Source: Milne 2022,
Proposition 25.28(a), direction "quasi-split ⇒ natural action", with §25.c, printed p.555
(PDF 566).
- Lean: `StarActionQuasiSplitStatement` (`Reductive/StarActionQuasiSplitStatement`).
  Hypotheses: `G` affine and locally of finite type over `k`, with `IsQuasiSplit G`.
  Conclusion: some `d : GaloisPinningData k (SeparableClosure k) G` has
  `(d.starAction σ).val = d.galoisAction σ` for every `σ`.
- Status O. Published partial inputs:
  - `IsRootDatumOf.galoisRootIndexEquiv_mem_support_iff` (`Reductive/RootDatumGaloisSimpleRoots`)
    shows that the Galois root-index action preserves a base. It applies when the positive
    roots of that base are exactly the roots of a `k`-defined torus map into a `k`-subgroup.
  - `GaloisPinningData.starAction_eq_galoisAction` then applies.

  No published theorem states that the roots of a `k`-Borel subgroup containing the torus
  form the positive system of a base. This is why the row is not C.
- A route outside the Library at this commit adds two new
  lemmas: the roots statement above, for a Borel subgroup that represents the dynamic
  parabolic of a regular cocharacter, and the fact that a geometric Borel subgroup stays
  Borel over `SeparableClosure k`. The Library now proves A6; see the
  [Galois and derived coverage note](galois-derived-coverage-2026-11-13.md).

**A7. Finite Galois descent from a supplied pinned action.** Internal constructions with
no single source statement. They implement the twisting step in the proof of Conrad,
Proposition 7.2.11, p.258 (†), where a split group is twisted by a cocycle valued in the
pinned automorphisms `Aut(R, Δ)`.
- Common data: fields `k`, `K` with `Algebra k K`; an affine group scheme `G` over `Spec K`
  (`[IsAffineHom G.X.hom]`); a complete split pinning `p : SplitPinning G`; and a supplied
  homomorphism `ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut`. Nothing here extracts `ρ` from a
  ground-field group; A3 does that.
- `Reductive/PinnedGaloisDatum`: `SplitPinning.galoisSemilinearIso p ρ σ : G^σ ≅ G` is the
  semilinear pinned lift of `σ` with based automorphism `ρ σ`, and
  `galoisSemilinearIso_mul` is its tower law. Neither needs `K/k` finite or Galois. With
  `[FiniteDimensional k K] [IsGalois k K]`, `SplitPinning.galoisDatum p ρ` is the resulting
  descent datum for `G` along `Spec K → Spec k`.
- `Reductive/PinnedGaloisBorel`, under the same finite Galois hypotheses:
  `galoisBorelDatum p ρ` is the compatible descent datum for the negative Borel subgroup of
  `p`. `galoisQuasiSplitSolution p ρ` is an effective descent of the pair, and the theorem
  `isQuasiSplit_galoisQuasiSplitSolution` says that the descended `k`-group is quasi-split.
- Status D: published constructions and published theorems about them, with the
  hypotheses listed above. There is no separate proposition declaration.

**A8. The pinned Galois twist is an inner twist (conditional).** Internal supporting result
(`Rational/PinnedGaloisInnerTwist`; its Markdown calls it a step toward the
inner-discrepancy part of B1). Source: Conrad, Proposition 7.2.11, p.258 (†), whose
proof shows that the twisted group is an inner form of `G`.
- Lean: `SplitPinning.hasInnerDiscrepancy_solution`. Data and hypotheses:
  - fields `k`, `K` with `K/k` finite Galois, a group scheme `H` over `Spec k` with `H_K`
    affine, a split pinning `p` of `H_K` with `p.inclusion` a monomorphism, and `ρ` as in A7;
  - torus comparisons `τ σ : (p.torus)^σ ≅ p.torus` for every `σ`, with `hτ σ`: pulling
    `p.inclusion` back along `Spec σ` and then applying the canonical identification
    `(H_K)^σ ≅ H_K` equals `τ σ` followed by `p.inclusion`;
  - full root-datum automorphisms `δ σ` with `hδ σ`: the weight map of `δ σ` sends `χ` to
    `(τ σ).inv ≫` (the pullback of `χ` along `Spec σ`), that is, `δ` is the actual Galois
    action on characters;
  - Weyl agreement `hw σ`: `(ρ σ).val * (δ σ)⁻¹` lies in the Weyl group of `p.rootDatum`;
  - an adjoint quotient `hq'` of `H_K`, a descent solution `s` of `p.galoisDatum ρ`, and
    an adjoint quotient `hq : IsAdjointQuotient q` of the descended group `s.obj` over `k`.

  Conclusion: the local group isomorphism induced by `s.iso : (s.obj)_K ≅ H_K` has
  all-test inner discrepancy for `hq.innerAction`. This is the Library's form of the
  statement that `s.obj` is an inner form of `H`.
- The same module also proves the steps `pullIso_solution_iso`,
  `inclusion_comp_galoisTwistIso`, `characterAut_galoisTwistTorus_mem_weylImage` and
  `exists_adjointPoint_galoisTwistIso`, under the corresponding subsets of these
  hypotheses.
- Status D (published internal theorem with the hypotheses above). It does not construct
  `τ`, `δ`, the pinning or the solution. The unconditional existence of quasi-split inner
  forms is B1.

**A9. Short exactness for absolute-Galois characters of groups of multiplicative type.**
Source is Milne 2017, §12.g and Theorem 12.23, printed pp.239–240 (PDF 255–256).

- Status P. `multiplicativeTypeAbsoluteExactness` proves
  `MultiplicativeTypeAbsoluteExactnessStatement.{u}` over every field
  `k : Type u`. For composable maps of actual groups of multiplicative type,
  closed subgroup inclusions and their represented fppf quotients correspond
  to short exact sequences under the contravariant character functor. Its maps
  are integral linear and equivariant for `Gal(k_s/k)`, with torsion allowed.
  This applies to a central subgroup sequence when all three groups are of
  multiplicative type.
- The proof first appeared in the Library at `bb9e086196d00484fd52204977452d922bf3c660`. D4 in the family 2 ledger
  records the categorical equivalence for the same functor.
  [Modules, statements and proofs](multiplicative-type-absolute-galois-progress.md)

**A10. Fixed lattices and rational morphisms.** Milne 2017, §12.g, printed
p.239 (PDF 255), gives the fixed-character formula over the separable
closure. The character half of `GaloisInvariantLatticesStatement.{u}`
specializes to that formula for commutative affine algebraic groups.
- For an affine commutative `k`-group scheme `T` and any Galois extension
  `K/k`, scalar extension identifies the actual `k`-homomorphisms
  `T ⟶ 𝔾_m` and `𝔾_m ⟶ T` with the fixed homomorphisms of the respective
  types over `K`. The two comparisons are bijections to the integral
  invariant submodules for A1, with the canonical `𝔾_m` base-change
  isomorphism. This covers `K = SeparableClosure k`.
- Status P. `galoisInvariantLattices` in
  `Torus/GaloisInvariantLatticesProof` proves both comparisons. The proof first appeared in the Library at
  `2d12bd934a2a0da7808014bfe52c6d67fde3eb62`; it was checked for Lake build and the exact target. [Statement](../../Langlands/GroupScheme/Torus/GaloisInvariantLatticesStatement.md),
  [proof](../../Langlands/GroupScheme/Torus/GaloisInvariantLatticesProof.md),
  [family 2, D6](ledger-family-2-tori.md#d-field-tori-and-galois-actions-on-lattices)

**A11. The actual Tits index of a semisimple group.** J. Tits, *Classification
of algebraic semisimple groups* (1966), §§2.1–2.3 and 2.5.1, printed
pp.38–40 (PDF pp.43–45). Registered source `tits-1966-classification-algebraic-semisimple`,
SHA-256 `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.

- `titsIndexExistence` and `titsIndexIndependence` prove the two components
  of `TitsIndexChoiceStatement`. For a semisimple group over an arbitrary
  field, with affine and locally finite type structure map, they give
  compatible actual maximal and maximal split tori, based root data over the
  separable closure, and comparison of any two resulting indices. The
  comparison preserves the Cartan pairings, the zero-restriction simple
  vertices, and the star action of each Galois element.
  [Statement](../../Langlands/GroupScheme/Reductive/TitsIndexChoiceStatement.md),
  [existence proof](../../Langlands/GroupScheme/Reductive/TitsIndexExistenceProof.md),
  [independence proof](../../Langlands/GroupScheme/Reductive/TitsIndexIndependenceProof.md)
- Status P for `TitsIndexRelativeStructureStatement` by
  `titsIndexRelativeStructure`. For each such index, the star action
  preserves the zero-restriction vertices. Restriction sends the orbits
  of the complementary vertices bijectively to the actual simple relative
  roots. Their number equals the split rank as defined by dimensions of
  closed split subtori.
  [Statement](../../Langlands/GroupScheme/Reductive/TitsIndexRelativeStatement.md),
  [proof](../../Langlands/GroupScheme/Reductive/TitsIndexSplitRankProof.md)
- `titsAnisotropicKernel` and `titsAnisotropicKernelIndex` prove the two
  components of `TitsAnisotropicKernelStructureStatement`. For every
  represented centralizer of the chosen maximal split torus and every
  derived subgroup of that representative, they give semisimplicity,
  anisotropy and the identification of its index with the subdiagram on
  the zero-restriction vertices. This uses restriction and pushforward
  along an actual torus map for the roots and coroots, and the identified
  simple vertices carry the same star action.
  [Statement](../../Langlands/GroupScheme/Reductive/TitsIndexAnisotropicKernelStatement.md),
  [anisotropy proof](../../Langlands/GroupScheme/Reductive/TitsIndexAnisotropicKernelProof.md),
  [index proof](../../Langlands/GroupScheme/Reductive/TitsIndexAnisotropicKernelIndexProof.md)

## B. Quasi-split groups and inner forms

`IsQuasiSplit G` (`Reductive/QuasiSplit`) means: `G` is connected reductive and has a
geometric Borel subgroup defined over `k`. Source: Milne 2017, 17.66–17.67, printed p.375.

**B1. Quasi-split inner forms exist.** Source: Conrad, Proposition 7.2.11, p.258 (†), with
§7.2, pp.250–252.
- Lean: `QuasiSplitInnerFormExistenceStatement` (`Rational/QuasiSplitInnerFormExistenceStatement`).
  Hypotheses: a connected reductive field group `G`. Conclusion:
  `Nonempty (QuasiSplitInnerForm G)`.
- Status P: `quasiSplitInnerFormExistence` (`Rational/QuasiSplitInnerFormExistenceProof`). It
  applies `quasiSplitInnerFormExistence_of_rootDatum_adjoint`
  (`Rational/QuasiSplitInnerFormExistenceReduction`) to `rootDatumExistence` and
  `adjointQuotientExistence`.

**B2. Adjoint quotients of quasi-split groups are quasi-split.** Source: Milne 2017,
Proposition 17.20, printed p.357, and 17.69, printed p.376.
- Lean: `AdjointQuotientQuasiSplitStatement` (`Adjoint/QuasiSplitStatement`). Hypotheses: an
  adjoint quotient `q : G ⟶ A` (`IsAdjointQuotient q`) with `IsQuasiSplit G`. Conclusion:
  `IsQuasiSplit A`.
- Status P: `adjointQuotientQuasiSplitStatement` (`Adjoint/QuasiSplitProof`).

**B3. Quasi-splitness lifts along central isogenies.** Source: Milne 2017, 17.67, printed
p.375; Proposition 17.54(a), printed pp.369–370; 17.84, printed p.379; Definition 18.1,
printed p.387.
- Lean: `CentralIsogenyQuasiSplitLiftStatement` (`CentralIsogeny/QuasiSplitLiftStatement`).
  Hypotheses: a central isogeny `π : G ⟶ A` of field groups, `G` connected reductive, and
  `IsQuasiSplit A`. Conclusion: `IsQuasiSplit G`.
- Status P: `centralIsogenyQuasiSplitLift` (`CentralIsogeny/QuasiSplitLift`).

**B4. The star action detects inner forms.** Conrad, *Reductive group schemes*
(2014), Proposition 7.2.2, p.252, and the identification of the outer class
by the star action on p.256. Registered source `conrad-2014-reductive-group-schemes`,
SHA-256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

- Status P. `innerFormStarAction` proves `InnerFormStarActionStatement`.
  Take two affine, locally finite type groups over an arbitrary field,
  an adjoint quotient of the first, and Galois pinning data of both over
  the separable closure. An inner discrepancy for an actual local group
  isomorphism over a finite Galois extension exists exactly when there is
  a based root-datum isomorphism intertwining the two full star actions.
  The discrepancy acts through the first group's adjoint quotient on
  every test scheme.
  [Statement](../../Langlands/GroupScheme/Reductive/InnerFormStarActionStatement.md),
  [proof](../../Langlands/GroupScheme/Reductive/InnerFormStarActionProof.md)

**B5. Uniqueness of the quasi-split inner form over a field.** Conrad,
Proposition 7.2.12 and its proof, pp.258–259, from the same registered source
as B4. The proposition applies over semilocal affine bases.

- Status P for `ReductiveSemilocalQuasiSplitInnerFormStatement` by
  `reductiveSemilocalQuasiSplitInnerForm`. It takes a reductive group over a
  semilocal ring with a represented fppf quotient by its full centre and the
  adjoint action of that quotient. It gives existence of a relative
  quasi-split inner form and an isomorphism over the base between any two
  such forms. For this theorem the inner-form data comprise an étale
  surjective cover with an all-test inner discrepancy.
  [Statement](../../Langlands/GroupScheme/Reductive/SemilocalQuasiSplitInnerFormStatement.md),
  [proof](../../Langlands/GroupScheme/Reductive/SemilocalQuasiSplitInnerFormProof.md)
- For a connected reductive `G` over an arbitrary field `k` and
  `d d' : QuasiSplitInnerForm G`, this gives `Nonempty (d.model ≅ d'.model)`.
  Obtain the adjoint quotient of `G` by `adjointQuotientExistence` and use
  `IsAdjointQuotient.isFppfQuotient` and `IsAdjointQuotient.innerAction_restrict`.
  Apply `IsConnectedReductive.isReductive` and
  `IsGeometricBorelSubgroup.isRelativeBorelSubgroup` to obtain relative
  quasi-splitness of the two models. For each model the finite Galois
  extension in its data gives an étale surjective cover. Its cocycle
  naturality gives the required discrepancy on every refinement, and
  `IsAdjointQuotient.hasInnerDiscrepancy_symm` inverts the local family to
  use the adjoint action of `G`. The uniqueness clause of the semilocal
  theorem then applies over `k`.
  [Field inner-form data](../../Langlands/GroupScheme/Rational/QuasiSplitInnerForm.md),
  [relative Borel comparison](../../Langlands/GroupScheme/RelativeLevi/HenselianBorelReduction.md),
  [discrepancy symmetry](../../Langlands/GroupScheme/Rational/InnerDiscrepancySymmetry.md)

## C. Centres and adjoint groups

**C1. The scheme-theoretic centre exists.** Source: CGP, Definitions A.1.8–A.1.10, printed
pp.468–469; Milne 2017, the paragraph before Proposition 19.10, printed p.400.
- Lean: `SchemeTheoreticCenterExistenceStatement` (`Reductive/CenterStructureStatement`).
  Hypotheses: a connected reductive field group `G`. Conclusion: some `z : Z ⟶ G` has
  `IsSchemeTheoreticCenter z`.
- Status P: `schemeTheoreticCenterExistence` (`Reductive/CenterExistenceProof`).

**C2. The centre commutes with field extension.** Same source.
- Lean: `SchemeTheoreticCenterBaseChangeStatement` (`Reductive/CenterStructureStatement`).
  Hypotheses: fields `k`, `K` with `Algebra k K`, a connected reductive `G` over `k`, and
  `IsSchemeTheoreticCenter z`. Conclusion: the base change of `z` along `Spec K → Spec k` is
  the centre.
- Scope: field extension only, not arbitrary base change.
- Status P: `schemeTheoreticCenterBaseChangeStatement` (`Reductive/CenterBaseChangeProof`).

**C3. The centre of a connected reductive group is of multiplicative type.** Source: Milne
2017, §19.b "Reductive algebraic groups", printed p.400; Definition 12.17, printed p.236.
The centre need not be smooth.
- Lean: `CenterMultiplicativeTypeStatement` (`Reductive/CenterMultiplicativeTypeStatement`).
  Hypotheses: a connected reductive `G` and its centre `z : Z ⟶ G`. Conclusion:
  `IsMultiplicativeType Z`.
- Status P: `centerMultiplicativeType` (`Reductive/CenterMultiplicativeTypeProof`). Its proof is the composite
  `centerMultiplicativeTypeCentralizerReduction` applied to
  `algClosedMaximalTorusCentralizerReduction dynamicCentralizerReductive noTorusUnipotent
  solvableTorusQuotient` (`Reductive/CenterMultiplicativeTypeReduction`,
  `Absolute/AlgClosedMaximalTorusCentralizerAssembly`, `Dynamic/CentralizerReductiveProof`,
  `Torus/NoTorusUnipotent`, `Absolute/SolvableTorusQuotientProof`).

**C4. The adjoint quotient exists.** Source: Milne 2017, Corollary 17.62(e), printed
pp.372–373; Remark 17.63, printed p.373; Theorem 5.14, printed p.102.
- Lean: `AdjointQuotientExistenceStatement` (`Adjoint/ExistenceStatement`). Hypotheses: a
  connected reductive field group `G`. Conclusion: some `q : G ⟶ A` with
  `IsAdjointQuotient q`. That predicate contains the following:
  - `G` connected reductive and `A` adjoint;
  - `q` flat, surjective and locally of finite presentation;
  - the kernel of `q` is the scheme-theoretic centre.
- Status P: `adjointQuotientExistence` (`Adjoint/ExistenceProof`).

**C5. The quotient by the centre is reductive with trivial centre.** Source: Milne 2017,
Corollary 17.62(e) with its proof, printed pp.372–373; Remark 17.63, printed p.373.
- Lean: `CenterQuotientReductiveStatement` and `CenterQuotientCenterTrivialStatement`
  (`Adjoint/CenterQuotientStatement`). Hypotheses: a connected reductive `G` and an affine,
  locally finite type `Q` with `q : G ⟶ Q` an fppf quotient by `center G`. Conclusions:
  `IsConnectedReductive Q`, and `center Q = ⊥`.
- Status P: `centerQuotientReductive` (`Adjoint/CenterQuotientReductiveProof`) and
  `centerQuotientCenterTrivial` (`Adjoint/CenterQuotientCenterProof`).

**C6. Adjoint quotients commute with field extension.** Source: CGP, Definitions
A.1.9–A.1.11 and Example A.1.12, printed pp.468–470.
- Lean: `AdjointQuotientBaseChangeStatement` (`Adjoint/BaseChangeStatement`). Hypotheses:
  fields `k`, `K` with `Algebra k K` and an adjoint quotient `q`. Conclusion: the base
  change of `q` to `K` is an adjoint quotient.
- Scope: field extension of a supplied adjoint quotient.
- Status P: `adjointQuotientBaseChangeStatement` (`Adjoint/BaseChangeProof`).

**C7. Images of maximal split tori in the adjoint group.** Source: Milne 2017, Definition
12.14, printed p.236; Remark 17.63, printed p.373; Definition 5.5, printed p.99; Theorem
5.39, printed p.108.
- Lean: `AdjointSplitTorusImageExistenceStatement` (`Adjoint/SplitTorusImageStatement`).
  Hypotheses: an adjoint quotient `q : G ⟶ A` and a maximal split torus `i : T ⟶ G`.
  Conclusion: a torus `T_ad` with `j : T_ad ⟶ A` and `p : T ⟶ T_ad` satisfying
  `IsAdjointSplitTorusImage q i j p`.
- Status P: `adjointSplitTorusImageExistenceStatement` (`Adjoint/SplitTorusImageProof`).

**C8. Real cocharacter spaces of the adjoint torus.** Source: Kaletha–Prasad, printed
pp.209–210; Milne 2017, Proposition 21.7, printed p.427, and 25.13, printed p.548.
- Lean: `AdjointRealCocharacterComparisonStatement` (`Adjoint/RealCocharacterStatement`).
  Hypotheses: data `(q, i, j, p)` with `IsAdjointSplitTorusImage q i j p`. Conclusion: the
  real cocharacter map of `p` has three properties:
  - it is surjective;
  - its kernel is the space of relative central directions;
  - it induces an isomorphism from the translation space of `i` onto `V(T_ad)`.
- Status P: `adjointRealCocharacterComparison` (`Adjoint/RealCocharacterProof`).

## D. Derived groups and cocentres

`IsDerivedSubgroup d` (`Derived/Basic`) means that `d : D ⟶ G` is a closed subgroup whose
range is the full scheme-theoretic derived subgroup on every test scheme.

**D1. Representability, smoothness, connectedness and field extension of the derived
subgroup.** Source: Milne 2017, Definition 6.16, Propositions 6.17–6.18 and Corollary
6.19(a)–(b), printed p.129 (PDF 145).
- Lean (`Derived/StructureStatement`), each with `G` affine and locally of finite type over
  a field:
  - `DerivedSubgroupRepresentabilityStatement`: some `d : D ⟶ G` with `D` affine and locally
    of finite type has `IsDerivedSubgroup d`.
  - `DerivedSubgroupSmoothnessStatement`: if `IsDerivedSubgroup d` and `G` is smooth, then
    `D` is smooth.
  - `DerivedSubgroupConnectednessStatement`: if `IsDerivedSubgroup d` and `G` is connected,
    then `D` is connected. No smoothness is needed.
  - `DerivedSubgroupFieldBaseChangeStatement`: for a field extension `K/k`, the base change
    of `d` is again a derived-subgroup inclusion. Moreover the base change of
    `derivedSubgroup G` equals `derivedSubgroup G_K`.
- Status P: `derivedSubgroupRepresentability` (`Derived/RepresentabilityProof`),
  `derivedSubgroupSmoothness` (`Derived/SmoothnessProof`), `derivedSubgroupConnectedness`
  (`Derived/ConnectednessProof`), `derivedSubgroupFieldBaseChange`
  (`Derived/FieldBaseChangeAssembly`).
- The conjunction `DerivedSubgroupStructureStatement` of these four is C, as the 4-tuple
  of the proofs.

**D2. The derived subgroup of a connected reductive group is semisimple.** Source: Milne
2017, Proposition 19.21(c), printed p.402 (PDF 418) (†).
- Lean: `DerivedSubgroupSemisimpleStatement` (`Derived/SemisimpleStatement`). Hypotheses:
  `G` connected reductive and `IsDerivedSubgroup d`. Conclusion: `IsSemisimple D`.
- Status P: `derivedSubgroupSemisimple` (`Derived/SemisimpleProof`).

**D3. `G` is the product of a central torus and its derived subgroup.** Source: Milne
2017, 6.46, printed p.135; Proposition 21.61, printed p.443; proof of 21.60(b)–(c), printed
p.442.
- Lean: `ReductiveCentralDerivedProductStatement` (`Reductive/CentralDerivedProductStatement`).
  Hypotheses: a connected reductive `G`. Conclusion: an affine, locally finite type torus
  `Z` with a closed central `i : Z ⟶ G`, and `d` with `IsDerivedSubgroup d`, such that the
  product map `Z × D → G` is an epimorphism.
- Status P: `reductiveCentralDerivedProduct` (`Reductive/CentralDerivedProductProof`).

**D4. Semisimple groups are perfect.** Source: Milne 2017, Corollary 21.50, printed p.440.
- Lean: `SemisimplePerfectStatement` (`Derived/SemisimplePerfectStatement`). Hypotheses:
  `IsSemisimple G`. Conclusion: `derivedSubgroup G = ⊤`.
- Status P: `semisimplePerfect` (`Derived/SemisimplePerfectProof`).

**D5. `Z(G) ∩ D(G)` is finite.** Source: Milne 2017, Proposition 19.21(b), printed p.402
(PDF 418) (†). Milne's Proposition 6.18, printed p.129, enters only to compare the definitions
of the derived subgroup.
- Lean: `DerivedCentralIntersectionFinitenessStatement` (`Derived/CentralIntersectionStatement`).
  Hypotheses: `G` connected reductive and `IsDerivedSubgroup d`. Conclusion: a closed
  subgroup `c : C ⟶ D` whose range is `(center G).comap d`, with `C → Spec k` finite.
- Status P: `derivedCentralIntersectionFiniteness` (`Derived/CentralIntersectionProof`).

**D6. Maximal tori meet the derived group in a torus.** Source: Kaletha–Prasad, §2.6(a),
printed p.93.
- Lean: `DerivedMaximalTorusIntersectionStatement` (`Derived/MaximalTorusIntersectionStatement`).
  Hypotheses: `G` connected reductive, `IsDerivedSubgroup d`, and a maximal torus `t`.
  Conclusion: the scheme-theoretic intersection of `t` and `d` is a torus.
- Status P: `derivedMaximalTorusIntersection` (`Derived/MaximalTorusIntersectionProof`).

**D7. Maximal split tori of the derived group.** Source: CGP, Theorem C.2.15, printed p.603
(PDF 629) (†), for quasi-reductive `G`: `S' := (S ∩ D(G))⁰_red` is a maximal `k`-split torus
of `D(G)`; proof Step 1, printed p.604 (PDF 630) (†). Background only: the opening of
Appendix C, printed p.581 (PDF 607), and Definition C.2.11 with the setup C.2.13, printed
pp.599–600 (PDF 625–626).
- Lean: `DerivedMaximalSplitTorusStatement` (`Derived/MaximalSplitTorusStatement`).
  Hypotheses: `G` connected reductive, `IsDerivedSubgroup d`, and a maximal split torus
  `i : S ⟶ G`. Conclusion: a maximal split torus `j : S_D ⟶ D` and a closed
  `e : S_D ⟶ S` with `j ≫ d = e ≫ i`.
- Scope: this is the existential part of C.2.15, specialized from quasi-reductive to
  connected reductive `G`. The Lean statement does not identify the witness `S_D` with the
  reduced identity component of `S ∩ D(G)`.
- Status P: `derivedMaximalSplitTorus` (`Derived/MaximalSplitTorusProof`).

**D8. The cocentre `G/D(G)` exists as a torus.** Source: Kaletha–Prasad, §2.6(a), printed
p.93, and the proof of Lemma 2.6.27, printed p.105.
- Lean: `CocenterQuotientExistenceStatement` (`Derived/CocenterQuotientStatement`).
  Hypotheses: a connected reductive `M` and `IsDerivedSubgroup d`. Conclusion: an affine
  torus `D'` with an fppf quotient `q : M ⟶ D'` by the range of `d`. Further, for every
  maximal torus `T` of `M` and every field `E` splitting `T`, `D'_E` is split and
  cocharacters of `T_E` surject onto those of `D'_E`.
- Status P: `cocenterQuotientExistence` (`Derived/CocenterQuotientProof`).

**D9. Homomorphisms to commutative groups kill the derived subgroup.** Source: Milne 2017,
Corollary 6.19(d), printed p.129; Remark 6.23, printed p.131.
- Lean: `DerivedCommutativeAnnihilationStatement`, `DerivedCharacterAnnihilationStatement`
  and their conjunction `DerivedAnnihilationStatement` (`Derived/AnnihilationStatement`).
  The data and conclusions are as follows:
  - `G` affine and locally of finite type over `k`, with `IsDerivedSubgroup d`;
  - after any scalar extension `R/k`, every homomorphism from `G_R` to a commutative affine
    finite-type group restricts trivially along `d_R`;
  - every rational character of `G_R` restricts to zero.
- Status C. Fix `R` and set `b = Spec.map (CommRingCat.ofHom (algebraMap k R))`. Then
  `hd.baseChange_of_eq _ (derivedSubgroup_baseChange_eq_of_field _ G)` shows that `d_R` is
  again a derived-subgroup inclusion. Here `IsDerivedSubgroup.baseChange_of_eq` is in
  `Derived/BaseChangeElementary` and `derivedSubgroup_baseChange_eq_of_field` in
  `Derived/FieldBaseChangeAssembly`. Then `IsDerivedSubgroup.comp_eq_one` and
  `IsDerivedSubgroup.characterRestrict_eq_zero` (`Derived/KernelAnnihilation`) give the two
  statements. The first needs the instance `IsAffineHom` for the base change `H_R`, which
  holds because `pullback.snd H.X.hom b` is affine. The conjunction is the pair of the two
  composites.
- The Library now proves the three statements; see the
  [Galois and derived coverage note](galois-derived-coverage-2026-11-13.md).

## E. Central isogenies

`IsCentralIsogeny` (`CentralIsogeny/Basic`) follows Conrad, Definition 3.3.9, p.103, and
Milne 2017, Definition 18.1, printed p.387. It does not require a smooth kernel.

**E1. Base change.** Source: Conrad, Definition 3.3.9, p.103.
- Lean: `CentralIsogenyBaseChangeStatement` (`CentralIsogeny/BaseChangeStatement`).
  Hypotheses: arbitrary schemes `S`, `S'` with `b : S' ⟶ S`, and a central isogeny `f` of
  `S`-groups. Conclusion: the base change of `f` along `b` is a central isogeny.
- Status P: `centralIsogenyBaseChange` (`CentralIsogeny/BaseChange`).

**E2. Images of maximal tori.** Source: Milne 2017, Proposition 17.20, printed pp.357–358,
and Theorem 17.82, printed p.379.
- Lean: `CentralIsogenyMaximalTorusImageStatement` (`CentralIsogeny/MaximalTorusImageStatement`).
  Hypotheses:
  - connected reductive `G`, `H` and a central isogeny `π : G ⟶ H`;
  - a maximal torus `i : T ⟶ G`;
  - a torus `S` with a closed `j : S ⟶ H`;
  - a surjective `f : T ⟶ S` with `i ≫ π = f ≫ j`.

  Conclusion: `j` is a maximal torus.
- Status P: `centralIsogenyMaximalTorusImage` (`CentralIsogeny/MaximalTorusImageProof`).

**E3. Central isogenies induce morphisms of root data.** Source: Milne 2017, Proposition
23.5, printed p.485 (PDF 501) (†), with its proof, printed pp.485–486: an isogeny of split
reductive groups induces an isogeny of root data, and the isogeny is central, respectively
an isomorphism, under the stated conditions on the root data. Supporting conventions:
Definitions 23.1–23.2, printed pp.483–484 (PDF 499–500), and the paragraph before
Proposition 23.5, printed p.485, which defines an isogeny of split reductive pairs.
- Lean: `CentralIsogenyRootDatumHomStatement` (`CentralIsogeny/SplitRootDatumStatement`).
  Hypotheses:
  - connected reductive `G`, `G'` with split maximal tori `i`, `i'`;
  - a central isogeny `φ` and `t : T ⟶ T'` with `i ≫ φ = t ≫ i'`;
  - root data `P` of `i` and `P'` of `i'`.

  Conclusion: a morphism of root pairings `f : P' ⟶ P` with `f χ = t ≫ χ` and
  `f ν = ν ≫ t`, both maps injective. Moreover `φ` is an isomorphism iff the weight map is
  bijective.
- Status P: `centralIsogenyRootDatumHom` (`CentralIsogeny/SplitRootDatumProof`).

**E4. Lifting split maximal tori.** Source: Borel–Tits (1972), Théorème 2.20(ii), printed
p.260; Milne 2017, Proposition 17.20, printed pp.357–358.
- Lean: `CentralIsogenySplitMaximalTorusLiftStatement` (`CentralIsogeny/SplitTorusLiftStatement`).
  Hypotheses: connected reductive `G`, `H`, a central isogeny `π : G ⟶ H`, and a split
  maximal torus `i : S ⟶ H`. Conclusion: a split maximal torus `j : T ⟶ G` and
  `f : T ⟶ S` with `j ≫ π = f ≫ i`.
- Status P: `centralIsogenySplitMaximalTorusLift` (`CentralIsogeny/SplitMaximalTorusLiftProof`).

**E5. Central isogenies killing central semisimple tangent vectors.** Internal deduction
with no single source statement (statement Markdown).
- Lean: `CentralSemisimpleKernelStatement` (`CentralIsogeny/SemisimpleKernel`) and
  `GeometricCentralSemisimpleKernelStatement` (`CentralIsogeny/GeometricSemisimpleKernel`).
  Hypotheses: exponential characteristic `p > 1`, and `G` smooth, affine and connected.
  Conclusion: a smooth connected affine `Q` and a central isogeny `q : G ⟶ Q`, with the
  following properties:
  - on every coefficient algebra, the kernel of the differential of `q` is the Lie algebra
    of the full centre;
  - a semisimple tangent vector is killed iff its Lie centralizer is everything. The
    geometric form asserts this over every field extension.
- Status P: `centralSemisimpleKernel` and `geometricCentralSemisimpleKernel` (same modules).

## F. Simply connected covers

`IsSimplyConnected` and `IsSimplyConnectedCover` (`SimplyConnected/Basic`) are defined as
follows. A simply connected cover `π : C ⟶ G` consists of:
- `G` semisimple and `C` simply connected;
- `π` a central isogeny;
- the universal property: every central isogeny onto `G` from a semisimple group receives a
  unique factorization of `π`.

**F1. Split simply connected central isogenies.** Source: Milne 2017, Remark 23.60, printed
p.502 (PDF 518) (†).
- Lean: `SplitSimplyConnectedCoverExistenceStatement` (`SimplyConnected/SplitCoverExistenceStatement`).
  Hypotheses: `G` semisimple with a split maximal torus. Conclusion: a central isogeny
  `π : C ⟶ G` with `C` simply connected.
- Scope difference: the universal factorization of F5 is not part of the conclusion.
- Status P: `splitSimplyConnectedCoverExistence` (`SimplyConnected/SplitCoverExistenceProof`).

**F2. Coroot criterion and its converse.** Source: Milne 2017, Proposition 23.29, printed
p.493 (PDF 509) (†), and Proposition 23.59, printed p.502 (PDF 518) (†).
- Lean:
  - `SplitCorootSpanSimplyConnectedStatement` (`SimplyConnected/SplitCriterionStatement`):
    `G` semisimple, a split maximal torus `i` with a root datum `P`, and coroots spanning
    `X_*(T)`. Conclusion: `IsSimplyConnected G`.
  - `SplitSimplyConnectedCorootSpanStatement` (`SimplyConnected/SplitNecessityStatement`):
    `G` simply connected, a split maximal torus, and a finite reduced root datum `P`.
    Conclusion: the coroots span `X_*(T)`.
- Status P: `splitCorootSpanSimplyConnected` (`SimplyConnected/SplitCriterion`) and
  `splitSimplyConnectedCorootSpan` (`SimplyConnected/SplitNecessity`).

**F3. Field extension.** Source of the field-extension compatibility: CGP, Corollary
A.4.11(1), printed pp.500–501 (PDF 526–527) (†). It gives the simply connected central cover,
unique up to unique isomorphism, and says that "its formation commutes with any extension
of the base field".
- Supporting locators, which are not sources of that compatibility:
  - the definition of a simply connected semisimple group in the paragraph just before
    Corollary A.4.11, CGP printed p.500 (PDF 526) (†);
  - Milne 2017, Propositions 19.10 and 19.13, printed p.400 (PDF 416): a reductive group is
    semisimple if and only if its centre is finite (19.10), and reductivity is invariant
    under extension of the base field (19.13);
  - Milne 2017, Proposition 19.15, printed pp.400–401 (PDF 416–417): the central-isogeny
    criterion behind `IsSimplyConnected`;
  - Milne 2017, Proposition 18.8, printed p.389 (PDF 405): the universal property.
- Lean (`SimplyConnected/FieldExtensionStatement`), each for an arbitrary field extension
  `K/k`:
  - `IsSemisimpleFieldExtensionStatement`: semisimplicity of `G` is preserved.
  - `IsSimplyConnectedFieldExtensionStatement`: simple connectedness of `G` is preserved.
  - `IsSimplyConnectedCoverFieldExtensionStatement`: a supplied simply connected cover
    remains one, universal property included.
  - `SimplyConnectedFieldExtensionStatement`: the conjunction of the three.
- Status:
  - P for the first two: `isSemisimpleFieldExtension`
    (`SimplyConnected/SemisimpleFieldExtensionProof`) and `isSimplyConnectedFieldExtension`
    (`SimplyConnected/SimplyConnectedFieldExtensionProof`).
  - P for the cover statement: `isSimplyConnectedCover_fieldExtension`
    (`SimplyConnected/FieldExtensionProof`).
  - P for the conjunction: `simplyConnected_fieldExtension`
    (`SimplyConnected/FieldExtensionPackageProof`).
  - These two first appeared in the Library after commit `e449cde`.

**F4. Simply connected covers exist over every field.** Source: CGP, Corollary A.4.11(1),
printed pp.500–501 (PDF 526–527) (†); Milne 2017, Definition 18.5, printed p.388.
- Lean: `SimplyConnectedCoverExistenceStatement` (`SimplyConnected/CoverExistenceStatement`).
  Hypotheses: `IsSemisimple G` over a field. Conclusion: some `π : C ⟶ G` with
  `IsSimplyConnectedCover π`.
- Status P: `simplyConnectedCoverExistence` (`SimplyConnected/CoverExistenceProof`).

**F5. Simply connected covers of derived subgroups.** Source: Milne 2017, Proposition
19.21(c), printed p.402, with CGP Corollary A.4.11(1). The composite assertion is not
stated verbatim in the sources.
- Lean: `SimplyConnectedDerivedCoverExistenceStatement` (`SimplyConnected/DerivedCoverStatement`).
  Hypotheses: a connected reductive field group `G`. Conclusion: `d : D ⟶ G` and
  `π : C ⟶ D` with `IsSimplyConnectedDerivedCover d π`, that is, `IsDerivedSubgroup d` and
  `IsSimplyConnectedCover π`.
- Status P: `simplyConnectedDerivedCoverExistence` (`SimplyConnected/DerivedCoverProof`). It
  applies `derivedSubgroupRepresentability`, then `derivedSubgroupSemisimple`, then
  `simplyConnectedCoverExistence`.

**F6. Tori through covers.**
- `SimplyConnectedCoverSplitTorusStatement` (`SimplyConnected/SplitTorusStatement`). Source:
  Borel–Tits (1972), Théorème 2.20(ii), printed p.260. Hypotheses: `IsSimplyConnectedCover
  π` and a maximal split torus `i` of `G`. Conclusion: a maximal split torus `i_C` of `C`
  and `f` with `i_C ≫ π = f ≫ i`, `f` a central isogeny. Status P:
  `simplyConnectedCoverSplitTorus` (`SimplyConnected/SplitTorusProof`).
- `DerivedCoverMaximalTorusPreimageStatement` (`SimplyConnected/DerivedCoverMaximalTorusPreimageStatement`).
  Internal provenance. Hypotheses: `IsSimplyConnectedDerivedCover d π` and a maximal torus
  `i` of `H`. Conclusion: the full scheme-theoretic intersection of `π ≫ d` and `i` is a
  torus. Status P: `derivedCoverMaximalTorusPreimage`
  (`SimplyConnected/DerivedCoverMaximalTorusPreimageProof`).
- `SimplyConnectedDerivedCoverSplitTorusStatement` (`SimplyConnected/DerivedCoverSplitTorusStatement`).
  Source: Borel–Tits (1965), §0.6, printed p.59, Proposition 2.2 and §2.3, pp.63–64, and
  Proposition 4.27, printed p.94; CGP, Definition C.2.11, printed p.599. Hypotheses:
  `IsSimplyConnectedDerivedCover d π` and a maximal split torus `i` of `G`. Conclusion:
  - compatible maximal split tori of `D` and `C`;
  - a closed `e` and a central isogeny `f`;
  - `f ≫ e` is injective on rational and real cocharacters, with the same image as `e`.

  Status P: `simplyConnectedDerivedCoverSplitTorus` (`SimplyConnected/DerivedCoverSplitTorusProof`).
- `SplitTorusCentralizerDerivedCorootComparisonStatement`
  (`SimplyConnected/SplitTorusCentralizerDerivedCorootComparisonStatement`). This is a
  derived geometric formulation; no source states it verbatim. Sources (†), all in Conrad:
  - Theorem 5.3.1 and its proof, pp.160 and 163: the derived group of a reductive group,
    its maximal tori and root system;
  - Proposition 5.3.4, p.164: maximal tori of `G` correspond to maximal tori of `D(G)`;
  - Proposition 5.4.5 and its proof, pp.177–178: a parabolic subgroup has a unique Levi
    subgroup containing a given maximal torus; the proof writes `P = P_G(λ)` with Levi
    subgroup `Z_G(λ)`;
  - Exercise 6.5.2(iv), p.236, which Remark 5.4.7, p.178, applies to a simply connected
    semisimple group: the choice of a chamber for which the relevant roots are spanned by a
    subset of the simple roots.

  Exercise 6.5.2 starts from a simply connected semisimple ambient group. The Lean
  statement assumes only a connected reductive `G` and asserts a comparison of coroot spans
  for the supplied centralizer and its derived subgroup. Hypotheses:
  - `k` algebraically closed and `G` connected reductive;
  - a split subtorus `a`, with its centralizer `M` represented by `j`;
  - a semisimple derived subgroup `d : D ⟶ M`.

  Conclusion: split maximal tori of `G` and `D` with reduced root data and a base `b`.
  The coroot span of `D` maps onto the span of the coroots of a subset of `b`. Status P:
  `splitTorusCentralizerDerivedCorootComparison` (same module path with `Proof`).

## Conventions and scope

- Centres, derived subgroups and isogeny kernels are scheme-theoretic. They may be
  non-smooth or disconnected. No row above adds a smoothness hypothesis on them.
- Base-change rows C2, C6, D1 and F3 concern field extensions only. E1 is the only
  arbitrary-base row.
- The star action (A3) is defined from Galois pinning data over any extension `E/k`.
  `absoluteStarAction` specializes it to the separable closure. The descent constructions
  of A7 and the conditional result A8 instead start from a supplied pinned action.
- Local Kneser–Tits results for simply connected groups are tracked in the published note
  [Local Kneser–Tits: published reductions and open inputs](local-kneser-tits-route.md).

## Remaining open targets in family 6

At the snapshot commit these were open: A6, the quasi-split star action (the missing
input was that the roots of a `k`-Borel subgroup containing the torus form the
positive system of a base), and named theorems for the C rows, the D1 conjunction and the
three D9 statements. All of them are now proved in the Library; see the
[Galois and derived coverage note](galois-derived-coverage-2026-11-13.md).
