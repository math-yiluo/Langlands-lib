# Group-scheme ledger, family 1: group-scheme and affine foundations

Author: Worker 3483, 10 November 2026, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). This note is the source-to-declaration
ledger for family 1 of that program's contract. Family 1 covers:

- group schemes over a general base, their homomorphisms, closed subgroups, normality,
  kernels and base change;
- affine group schemes and Hopf algebras;
- the identity tangent space (Lie algebra) and its functoriality;
- images, monomorphisms and flatness of homomorphisms;
- quotients and the representability results that later quotient constructions use.

It describes Library commit `f2c5495316f5a5631bc8c11875b7509d93271fe5` and environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. Lean names are in `Langlands.GroupScheme` unless a
namespace is shown. Module paths are relative to `Langlands/GroupScheme/` unless they start
with `Langlands/`.

The rows list the principal source assertions of this family, together with the internal
lemmas that later families use directly; an internal lemma is marked "Source: internal" and
claims no source theorem. Other auxiliary declarations are not listed, and leaving one out
says nothing about its status.

## Status codes and evidence

Each row gives the source assertion with its locator, the exact Lean statement and its
hypotheses, a status, the evidence, and the owner task.

- **D (definition or internal result).** A published construction, or a published theorem
  that is not a proposition declaration. The evidence is its module path. No owner task is
  needed.
- **P (published proof).** The Library at the commit above contains a theorem whose type is
  exactly the statement. The evidence is that theorem and its module path. The author also
  type-checked `example : S := proof` for every P row in a private module. That check
  passed with no errors or warnings, and `#print axioms` reported only `propext`,
  `Classical.choice` and `Quot.sound`; it is not public evidence. No further proof work or
  owner task is needed.
- **C (composite, not published).** No published theorem has the statement as its type, but
  a term built only from published theorems has it: a projection out of a published
  conjunction, a tuple of published proofs, or the short term shown. The author
  type-checked it in the same private module, with axioms `propext`, `Classical.choice` and
  `Quot.sound`. What is missing is a named wrapper theorem, not mathematics. The row names
  the owner task, or says that there is none.
- **O (open).** A Lean statement exists, but no published proof and no composite from
  published results is known.

The labels "accepted" and "published" are used only for artifacts that passed independent
review.

Source locators use these registered sources, cited by source id:

- `milne-2017-algebraic-groups`: J. S. Milne, *Algebraic Groups* (2017). PDF page = printed
  page + 16. With it, the official errata snapshot
  `milne-2017-algebraic-groups-errata-2026-11-02`.
- `conrad-2014-reductive-group-schemes`: B. Conrad, *Reductive group schemes* (2014).
  Printed page = PDF page.
- `conrad-gabber-prasad-2015-pseudo-reductive`: B. Conrad, O. Gabber and G. Prasad,
  *Pseudo-reductive groups*, 2nd edition (2015). PDF page = printed page + 26.
- `milne-abelian-varieties-1986-author-2022`: J. S. Milne, *Abelian Varieties* (1986 article,
  author revision 2022). Printed page = PDF page.
- Stacks Project snapshots retained in the project literature: "Tag 047L group schemes over
  a field are separated (HTML snapshot 2026-10-22)" and "Roots of unity and the Kummer
  finite etale calculation (2026-10-23)", file `03PL.html`.

The author re-read every locator below in the original source for this note, on 10 November
2026, and checked that the cited item is on the cited page.

## A. Group schemes, subgroups, kernels and base change

All rows are D. Except for the last row, these constructions work over an arbitrary base
scheme `S`; field hypotheses appear only in the statements of later rows. The last row,
`MatrixRepresentation`, is defined only over affine bases `Spec R`.

- `Langlands.GroupScheme S := Grp (Over S)` and its base change functor
  `Langlands.GroupScheme.baseChange (f : T ⟶ S)` (`Langlands/AbelianScheme/GroupScheme`).
  Homomorphisms are morphisms of group objects. Over a field this is Milne's notion of a
  group scheme; Milne 2017, Definition 1.1, printed p.6 (PDF 22), adds finite type.
- `kernel f`, `kernelι f` and `kernelPointsEquiv f T` (`Langlands/AbelianScheme/Kernel`): the
  kernel is the pullback of `f` along the unit section of the target, and its `T`-points are
  the kernel of `G(T) → H(T)` for every `T`. No smoothness is imposed, so non-smooth kernels
  such as `μ_p` in characteristic `p` are kept.
- `IsClosedSubgroup i` (`Reductive/Basic`): the underlying morphism of `i` is a closed
  immersion.
- `SubgroupFunctor G`, `SubgroupFunctor.range f`, `SubgroupFunctor.IsNormal`,
  `SubgroupFunctor.baseChange` and `SubgroupFunctor.IsRepresentedBy` (`SubgroupFunctor`):
  subgroup functors of `G` on all test schemes over `S`, including nonreduced ones; the image
  functor of a homomorphism; normality tested on every test scheme; base change; and
  representation by a monomorphism.
- `RelativeRoot.IsFppfQuotient N q` (`Rational/RootSubgroupStructureStatement`): `q` is flat,
  surjective and locally of finite presentation, and `range (kernelι q) = N`. This is a
  quotient of fppf sheaves. It does not say that `G(T) → Q(T)` is surjective for each test
  `T`. Over a field, Milne 2017, Definition 5.5, printed p.99 (PDF 115), calls a faithfully
  flat homomorphism a quotient map.
- `MatrixRepresentation G n` (`MatrixRepresentation`): for a commutative ring `R`
  (`R : CommRingCat`), a group scheme `G` over `Spec R` and a finite coordinate index type
  `n` (with `[Fintype n]` and `[DecidableEq n]`), the homomorphisms
  `G ⟶ GeneralLinear.groupScheme n R`. The base is affine; the test schemes over `Spec R`
  are arbitrary.

## B. Affine group schemes and basic structure

**B1. Affine groups and Hopf algebras.** Source: Milne 2017, §3.c, printed p.66 (PDF 82),
and Corollary 3.7, printed p.67 (PDF 83).
- D: `AffineCoordinates.hopfAlgebra G` and `AffineCoordinates.hopfSpecIso G`
  (`AffineHopfCoordinates`): for an affine group scheme `G` over `Spec R`, `R` any
  commutative ring, the coordinate Hopf algebra and the isomorphism of Mathlib's
  `hopfSpec` of it with `G`.

**B2. Affine algebraic groups are linear.** Source: Milne 2017, Corollary 4.10, printed p.87
(PDF 103).
- Lean: `AffineLinearEmbeddingStatement` (`AffineLinearEmbeddingStatement`). Hypotheses: a
  field; `G` with affine structure map, locally of finite type. Conclusion: a matrix
  representation `G ⟶ GL_N` that is a closed subgroup.
- Status P: `affineLinearEmbeddingStatement` (`AffineLinearEmbeddingProof`).

**B3. Cartier's theorem.** Source: Milne 2017, Theorem 3.23, printed p.71 (PDF 87).
- Lean: `AffineCartierSmoothStatement` (`AffineCartierSmoothStatement`). Hypotheses:
  `[CharZero k]`; `G` with affine structure map, locally of finite type. Conclusion: `G` is
  smooth.
- Status P: `affineCartierSmooth` (`AffineCartierSmoothProof`).

**B4. Group schemes over a field are separated.** Source: Stacks Project, Lemma 39.7.3
(Tag 047L), snapshot cited above.
- Lean: `FieldSeparatedStatement` (`FieldSeparatedStatement`). Hypotheses: any field and any
  group scheme `G` over it. Conclusion: `G → Spec k` is separated.
- Status P: `fieldSeparated` (`FieldSeparatedProof`).

**B5. `μ_n` is finite étale when `n` is invertible.** Source: Stacks Project, the proof of
Lemma 59.28.1 (Tag 03PL), snapshot cited above; the Lean conclusion is derived from that
proof, not from the lemma's exactness statement.
- Lean: `MuFiniteEtaleStatement` (`MuFiniteEtaleStatement`). Hypotheses: any scheme `S`;
  `0 < n` with `n` a unit in `Γ(S, 𝒪_S)`. Conclusion: `μ_n → S` is finite and étale.
- Status P: `muFiniteEtale` (`MuFiniteEtaleProof`).

**B6. `GL_n` is smooth.** Source: no numbered source item is cited; the first milestone of
the contract requires it.
- Lean: `GeneralLinear.SmoothStatement` (`GeneralLinearSmoothStatement`): for every finite
  type `n` and every commutative ring `R`, `GL_n` over `Spec R` is smooth.
- Status P: `GeneralLinear.smoothStatement` (`GeneralLinearSmoothProof`).

## C. The identity tangent space

**C1. Definitions.** Source: Milne 2017, 10.6, printed p.188 (PDF 204):
`Lie(G) = Ker(G(k[ε]) → G(k))`. All D.
- `lieKernel G A` (`Lie/DualNumberKernel`): the kernel of `G(A[ε]) → G(A)` for a group `G`
  over `Spec R` and an `R`-algebra `A`, `R` any commutative ring; its `A`-module structure
  for affine `G` is in `Lie/AffineModule`.
- `Lie.targetMap f A` and `Lie.targetMapLinear f A` (`Lie/KernelTargetMaps`): the
  differential of a homomorphism.
- `Lie.kernelBaseChangeLinearEquiv` (`Lie/BaseChange`): compatibility with base change.
- `SubgroupFunctor.lie` and `SubgroupFunctor.lie_eq_range` (`Lie/SubgroupTangent`): the
  tangent space of a subgroup functor, and its agreement with the image for a represented
  subgroup.

**C2. A subgroup with the full Lie algebra is everything.** Source: Milne 2017, Proposition
10.15, printed pp.190–191 (PDF 206–207).
- Lean: `LieSubgroupEqualityStatement` (`Lie/SubgroupEqualityStatement`). Hypotheses: a field;
  `H` smooth, with affine structure map and connected; `K` smooth; a closed subgroup
  `j : K ⟶ H` such that every element of `Lie(H)(k)` comes from `Lie(K)(k)`. Conclusion:
  `range j = ⊤`.
- Status P: `lieSubgroupEquality` (`Lie/SubgroupEqualityProof`).

**C3. Surjective differential.** Source: internal.
- Lean: `Lie.SmoothSurjectiveOfSurjectiveDifferentialStatement` (`Lie/SurjectiveDifferentialStatement`).
  Hypotheses: a field; **both** `H` and `G` smooth with affine structure maps; `G` connected;
  `f : H ⟶ G` whose differential `Lie(H)(k) → Lie(G)(k)` is surjective. Conclusion: `f` is
  smooth and surjective.
- Scope: smoothness of the source is needed; without it the projection `α_p × 𝔾_a → 𝔾_a` in
  characteristic `p` has surjective differential but is not smooth.
- Status P: `Lie.smoothSurjectiveOfSurjectiveDifferential` (`Lie/SurjectiveDifferentialProof`).

**C4. Zero tangent space.** Source: internal.
- Lean: `ZeroTangentTrivialityStatement` (`Lie/ZeroTangentTrivialityStatement`). Hypotheses: a
  field; `G` with affine structure map, locally of finite type and connected, with
  `Lie(G)(k) = 0`. Conclusion: `G → Spec k` is an isomorphism and every point of `G` is `1`.
- Status P: `zeroTangentTriviality` (`Lie/ZeroTangentTriviality`).

## D. Images, monomorphisms and flatness

**D1. Homomorphism theorem for affine groups.** Source: Milne 2017, Theorem 3.34, printed
p.75 (PDF 91), and Theorem 5.39, printed p.108 (PDF 124).
- Lean: `AffineHomImageStatement` (`AffineHomImageStatement`). Hypotheses: a field; `G`, `H`
  with affine structure maps, locally of finite type; `f : G ⟶ H`. Conclusion:
  `f = q ≫ i` with `I` affine and locally of finite type, `i : I ⟶ H` a closed subgroup and
  `q` an fppf quotient by `range (kernelι f)`.
- Status P: `affineHomImage` (`AffineHomImageProof`).

**D2. Images of smooth connected groups.** Source: Milne 2017, Theorem 5.39, printed p.108
(PDF 124), and Proposition 5.46, printed p.110 (PDF 126).
- Lean: `SmoothConnectedHomImageStatement` (`HomImage`). Hypotheses: a field; `A` smooth,
  connected, affine; `G` affine, locally of finite type; `φ : A ⟶ G`. Conclusion: a closed
  subgroup `D ⟶ G`, with `D` smooth, connected and affine, through which `φ` factors by a
  flat, surjective, quasi-compact homomorphism locally of finite presentation.
- Status P: `smoothConnectedHomImage` (`HomImage`).

**D3. Monomorphisms are closed immersions.** Source: Milne 2017, Theorem 5.34, printed p.107
(PDF 123).
- Lean: `FiniteTypeMonomorphismStatement` (`FiniteTypeMonomorphismStatement`). Hypotheses: a
  field; `G`, `H` locally of finite type, quasi-compact and separated; `f` a monomorphism.
  Conclusion: `f` is a closed immersion.
- Status O. Owner task: none found.

**D4. Flatness propagates by translation.** Source: derived from the translation argument
in Milne, *Abelian Varieties*, Proposition 8.1 and its proof, p.12; Milne treats abelian
varieties.
- Lean: `TranslationFlatStatement` (`TranslationFlatStatement`). Hypotheses: `K`
  **algebraically closed**; a group `G` over `K` **locally of finite type**; an endomorphism
  `f` that is finite and surjective and is flat over some **nonempty open `U` of the
  target** (that is, `f` restricted to `f⁻¹(U) → U` is flat). Conclusion: `f` is flat.
- Status P: `translationFlat` (`TranslationFlatProof`).

**D5. Dominant homomorphisms.** Source: internal.
- `DominantGroupHomFlatStatement` (`DominantHomFlatStatement`): `k` algebraically closed; `G`
  locally of finite type and quasi-compact; `H` locally of finite type and reduced; `f`
  dominant. Conclusion: `f` is flat, surjective and quasi-compact. Status P:
  `dominantGroupHomFlat` (`DominantHomFlatProof`).
- `DominantHomFaithfullyFlatStatement` (`DominantHomFaithfullyFlat`): any field; `G` affine
  and locally of finite type; `H` affine and smooth; `f` scheme-theoretically dominant.
  Conclusion: `f` is flat and surjective. Status P: `dominantHomFaithfullyFlat`
  (`DominantHomFaithfullyFlat`).

**D6. Targets and kernels of fppf homomorphisms.** Source: internal.
- `FppfHomSmoothTargetStatement` (`FppfQuotientTargetSmooth`): a field; `G` smooth; `q` flat,
  surjective and locally of finite presentation. Conclusion: the target is smooth. No
  hypothesis on the kernel. Status P: `fppfHomSmoothTarget` (`FppfQuotientTargetSmooth`).
- `ConnectedKernelHomGeometryStatement` (`ConnectedKernelGeometryStatement`): any base scheme;
  `q` surjective with geometrically connected kernel. Conclusion: `q` is geometrically
  connected. Status P: `connectedKernelHomGeometry` (`ConnectedKernelGeometry`).

## E. Quotients and representability

**E1. Quotient targets are affine.** Source: Milne 2017, Proposition 5.18, printed p.103
(PDF 119), with Theorem 5.13, printed p.101 (PDF 117).
- Lean: `AffineGroupSchemeQuotientStatement` (`AffineQuotientStatement`). Hypotheses: a field;
  `G` affine and locally of finite type; `Q` locally of finite type, quasi-compact and
  separated; `q` flat, surjective and quasi-compact. Conclusion: `Q` is affine.
- Status P: `affineGroupSchemeQuotient` (`AffineQuotientProof`).

**E2. Quotients by normal subgroups.** Source: Milne 2017, Theorem 5.14, printed p.102
(PDF 118), Proposition 5.18, printed p.103 (PDF 119), and Corollary 5.26, printed p.105
(PDF 121).
- `NormalSubgroupQuotientStatement` (`NormalSubgroupQuotientStatement`): a field; `G` smooth
  and affine; a closed normal subgroup `N`. Conclusion: an fppf quotient `q : G ⟶ Q` by `N`
  with `Q` smooth and affine. Status P: `normalSubgroupQuotient` (`NormalSubgroupQuotientProof`).
- `NormalSubgroupQuotientExistenceStatement` (`NormalQuotientStatement`): a field; `G` affine
  and locally of finite type (**no smoothness**); a closed normal subgroup. Conclusion: an
  fppf quotient with `Q` affine and locally of finite type. Status P:
  `normalSubgroupQuotientExistence` (`NormalQuotientExistenceProof`).
- `AffineNormalSubgroupQuotientStatement` (`AffineNormalSubgroupQuotientStatement`): the same
  content with instance hypotheses. Status P: `affineNormalSubgroupQuotient`
  (`AffineNormalSubgroupQuotientProof`). The equivalence of the two formulations,
  `AffineNormalSubgroupQuotientEquivalenceStatement` (`AffineNormalSubgroupQuotientEquivalence`),
  is P: `affineNormalSubgroupQuotientEquivalence` (same module).
- `AlgClosedNormalQuotientExistenceStatement` (`NormalQuotientExistenceReduction`): the
  algebraically closed case. Status P: `algClosedNormalQuotientExistence`
  (`AlgClosedNormalQuotientExistenceProof`).

**E3. Quotient by a kernel.** Source: internal.
- `AffineKernelQuotientStatement` (`AffineKernelQuotient`): a field; `G` smooth and affine;
  `H` affine and locally of finite type; `f : G ⟶ H`. Conclusion: an fppf quotient by
  `range (kernelι f)` with smooth affine target. Status P: `affineKernelQuotient` (same
  module).
- `NormalSubgroupAffineKernelStatement` (`AffineKernelQuotient`): every closed normal subgroup
  of a smooth affine `G` is the kernel of a homomorphism to an affine group locally of finite
  type. Status C, from the published `normalSubgroupQuotient`:

  ```lean
  example : NormalSubgroupAffineKernelStatement.{u} := by
    intro k _ G _ _ N i hi hn
    obtain ⟨Q, q, hsm, haff, hq⟩ := normalSubgroupQuotient k G N i hi hn
    have := hsm
    exact ⟨Q, q, haff, inferInstance, hq.2.2.2⟩
  ```

  Owner task: none. It was the input of an older reduction whose conclusion now has a direct
  proof.

**E4. Homogeneous quotients `G/H`.** Source: Milne 2017, Definition 5.20 and Propositions
5.24–5.25, printed pp.104–105 (PDF 120–121), Proposition 7.15, printed p.142 (PDF 158), and
Theorem 7.18, printed p.143 (PDF 159).
- Lean: `SmoothSubgroupQuotientExistenceStatement` (`HomogeneousQuotientStatement`).
  Hypotheses: a field; `G` smooth and affine; a smooth closed subgroup `H`. Conclusion: a
  scheme `Q` over `k`, separated, locally of finite type and quasi-compact, and
  `q : G → Q` smooth, surjective and quasi-compact, with `q(g) = q(h)` if and only if
  `g⁻¹h ∈ H`, on every test scheme.
- Status P: `smoothSubgroupQuotientExistence` (`HomogeneousQuotientProof`).

**E5. Quotients by parabolic subgroups are proper.** Source: derived from Milne 2017, Theorem
17.16, printed p.356 (PDF 372).
- Lean: `ParabolicSubgroupQuotientProperStatement` (`HomogeneousQuotientStatement`).
  Hypotheses: a field; `G` smooth, affine and connected; a parabolic subgroup; a **supplied**
  quotient `q : G → Q` as in E4. Conclusion: `Q` is proper.
- Status P: `parabolicSubgroupQuotientProper` (`ParabolicQuotientProperProof`).

**E6. The product `HN` with `N` normal.** Source: Milne 2017, Theorem 5.82 and its proof,
printed pp.120–121 (PDF 136–137).
- Lean: `NormalFactorFppfProductExistenceStatement` (`SubgroupFunctor/NormalFactorProductExistenceStatement`).
  Hypotheses: a field; `G` affine and locally of finite type; closed subgroups `H` and `N`
  with `N` normal. Conclusion: a homomorphism `p : P ⟶ G` whose range is the fppf product of
  `H` and `N`.
- Status P: `normalFactorFppfProductExistence` (`SubgroupFunctor/NormalFactorProductExistenceProof`).

**E7. Fixed points and centralizers are representable.** Source: Conrad–Gabber–Prasad,
Proposition A.8.10(1) and the remarks after it, printed pp.547–549 (PDF 573–575).
- `FixedSubgroupRepresentabilityStatement` (`FixedRepresentabilityStatement`): over `Spec R`,
  `R` any commutative ring; `H` with affine structure map, flat, and with coordinate module
  that becomes projective after a faithfully flat extension (`HasFpqcProjectiveCoordinateModule`);
  `G` **separated**; an action of `H` on `G` by group automorphisms. Conclusion: the fixed
  subgroup functor has a closed representative. Status P: `fixedSubgroupRepresentability`
  (`FixedSubgroupRepresentabilityProof`).
- `FieldFixedSubgroupRepresentabilityStatement` (same module): over a field, `H` with affine
  structure map (not necessarily smooth); separatedness of `G` is automatic (B4). Status P:
  `fieldFixedSubgroupRepresentability` (`FieldFixedSubgroupRepresentabilityProof`).
- `FieldCentralizerRepresentabilityStatement` (same module): over a field, for `H`
  commutative with affine structure map and `j : H ⟶ G`, the centralizer of `j` has a
  closed representative. Status P: `fieldCentralizerRepresentability`
  (`FieldCentralizerRepresentabilityProof`).

**E8. Closed orbits.** Source: Milne 2017, Propositions 1.65–1.66, printed pp.26–27
(PDF 42–43).
- Lean: `ClosedOrbitStatement` (`ClosedOrbitStatement`). Hypotheses: `k` algebraically closed;
  `G` smooth and affine; a **nonempty** `X` locally of finite type and quasi-compact with an
  action of `G`. Conclusion: a reduced closed `G`-stable subscheme `O` of `X`, locally of
  finite type and quasi-compact, with a rational point whose orbit is all rational points of
  `O`.
- Status P: `closedOrbit` (`ClosedOrbitProof`).

**E9. Normalizers of smooth subgroups with geometrically connected fibres.** Source: Conrad
2014, Proposition 2.1.6, pp.61–62, which assumes a finitely presented closed subscheme that
is smooth with nonempty geometrically connected fibres.
- Lean: `SmoothConnectedNormalizerStatement` (`SmoothConnectedNormalizerStatement`).
  Hypotheses: **any base scheme** `S`; `G` smooth with affine structure map; a **closed**
  subgroup `i : H ⟶ G` with `H` smooth and with **geometrically connected fibres**
  (`GeometricallyConnected H.X.hom`). Conclusion: a closed subgroup `j : N ⟶ G`, locally of
  finite presentation, representing the normalizer functor of `range i`.
- Status O. Owner task: Task 4817 (`4444bc4c-9692-4a32-acfc-dbae06ccea66`), which has no
  proof candidate.

## F. Geometric integrality and image generation

Source: Conrad–Gabber–Prasad, Lemma 3.3.4, printed p.108 (PDF 134), and the paragraph before
Proposition 3.3.5, printed p.109 (PDF 135), in the split-torus setting introduced on printed
p.107 (PDF 133). These rows feed the commutator and image constructions of families 3 and 5.

- `SmoothConnectedAffineGeometryStatement` (`SmoothConnectedGeometryStatement`), the
  conjunction of `SmoothConnectedAffineGroupIntegralStatement` (a smooth connected affine
  group over a field is geometrically integral) and
  `SmoothConnectedAffineProductIntegralStatement` (the product of two such groups is affine,
  locally of finite type, quasi-compact and geometrically integral). Status P:
  `smoothConnectedAffineGeometry` (`SmoothConnectedGeometryProof`). The two components are
  status C: `smoothConnectedAffineGeometry.1` and `.2`. Owner task: none.
- `PointedImageGenerationStatement` (`ImageGenerationStatement`): for `G` smooth affine and a
  pointed geometrically integral affine `V` of finite type with `f : V → G` sending the point
  to `1`, the subgroup generated by the image of `f` is smooth and connected. Status P:
  `ImageGeneration.pointedImageGeneration` (`ImageGenerationPointed`).
- `PointedImageEnvelopeStabilityStatement` (same module): the same with an equivariant split
  torus action; the closed image envelope is stable. Status P: `pointedImageEnvelopeStability`
  (`ImageEnvelopeStabilityProof`).
- `InvariantPointedImageGenerationStatement` (same module): the equivariant generated image
  with a dominant power map. Status P: `invariantPointedImageGeneration`
  (`InvariantPointedImageGenerationProof`).
- `ImageGenerationSourceStatement` (same module), the conjunction of the geometry statement
  and the two previous P rows. Status C:
  `⟨smoothConnectedAffineGeometry, ImageGeneration.pointedImageGeneration,
  pointedImageEnvelopeStability⟩`.
  Owner task: none.
- `ImageGeneration.NoetherianImageGenerationFinitenessStatement` (`ImageGenerationNoetherianStatement`),
  the conjunction of `ImageGeneration.NoetherianPrimeChainStabilizationStatement` (descending
  chains of primes in a noetherian ring stabilize) and
  `ImageGeneration.NoetherianAffineClosedEndomorphismStatement`
  (a closed immersion of a noetherian affine scheme into itself is an isomorphism). Source:
  internal. Status P: `ImageGeneration.noetherianImageGenerationFiniteness`
  (`ImageGenerationNoetherianProof`). The two components are status C: `.1` and `.2`. Owner
  task: none.

## G. The Hopf faithful-flatness input of D1

`AffineHomImageHopfAdapter.HopfSubalgebraFaithfullyFlatStatement k`
(`AffineHomImageHopfAdapter`), for a fixed field `k : Type u`. Hypotheses: a commutative
Hopf algebra `H : Type u` over `k` that is of finite type, and a subalgebra `K` such that
the comultiplication of every element of `K` lies in the `k`-span of the tensors `a ⊗ b`
with `a, b ∈ K`, and `K` is stable under the antipode. Conclusion: `H` is faithfully flat
over `K`. Source: Milne 2017, Theorem 3.31, printed p.73 (PDF 89). Milne assumes both Hopf
algebras finitely generated; the Lean statement assumes finite type only for `H`, so it is
more general than the source.

Status C. The published theorem
`HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem` (module
`Langlands.AnthropicFLT.Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem`,
outside `Langlands/GroupScheme/`) has the same hypotheses and conclusion, with independent
universes for `k` and `H`. Applying it to `K` and the two stability hypotheses proves the
statement for every field `k`. No named theorem for the statement exists. Owner task: none.

This statement is the input of D1's published proof. `affineHomImage`
(`AffineHomImageProof`) applies `affineHomImage_of_hopfSubalgebraFaithfullyFlat`
(`AffineHomImageHopfReduction`), whose hypothesis is this statement for every field, and
discharges that hypothesis with the same application of the theorem above.

## Summary and remaining obligations

Counted by the Lean statements named above, 34 have published proofs (P). Seven have a
composite and no wrapper theorem (C): the two components of
`SmoothConnectedAffineGeometryStatement`, `ImageGenerationSourceStatement`, the two
components of `ImageGeneration.NoetherianImageGenerationFinitenessStatement`,
`NormalSubgroupAffineKernelStatement`, and
`AffineHomImageHopfAdapter.HopfSubalgebraFaithfullyFlatStatement` (G). Two statements are
open (O):

1. `FiniteTypeMonomorphismStatement` (D3, Milne Theorem 5.34). Owner task: none found.
2. `SmoothConnectedNormalizerStatement` (E9, Conrad Proposition 2.1.6). Owner task: Task 4817.

The wrapper theorems for the C rows need no new mathematics; the program will collect them,
with those of the other families, in one proof task.
