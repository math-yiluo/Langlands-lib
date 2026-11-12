# Group-scheme ledger, family 5: rational structure over fields

Author: Worker 3483, 10 November 2026, for the algebraic and reductive group-scheme program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483). This note is the source-to-declaration
ledger for family 5 of that program's contract. Family 5 covers:

- maximal split tori over the ground field and their rational conjugacy;
- relative roots, the relative root system and the relative Weyl group `N(k)/Z(k)`;
- parabolic subgroups defined over the ground field, minimal parabolics and rational Levi
  subgroups, described through cocharacters defined over the ground field;
- the rational Bruhat decomposition, the relative Tits system and standard parabolics;
- split components and rational characters;
- the relation between relative and absolute roots and Weyl groups;
- the rational conjugacy theorems for smooth connected affine groups of Conrad–Gabber–Prasad,
  Appendix C.2;
- relative root subgroups;
- how non-split, non-quasi-split and anisotropic groups are retained.

It describes Library commit `f2c5495316f5a5631bc8c11875b7509d93271fe5` and environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. All Lean names are in `Langlands.GroupScheme` unless
a namespace is shown. Module paths are relative to `Langlands/GroupScheme/` in that commit.
"Field group" means a group scheme over `Spec k` for a field `k : Type u`. "Connected
reductive" means `IsConnectedReductive` (`Reductive/Basic`): smooth, affine structure map,
connected, and trivial unipotent radical after base change to an algebraic closure.

The rows list the principal source assertions of this family. The directory `Rational/`
contains about 300 further proposition declarations. Most are reductions, auxiliary
interfaces or consumer adapters used inside proofs. They are not listed one by one, and
leaving one out says nothing about its status. Absolute structure (maximal tori and Borel
subgroups, mostly over algebraically closed fields) belongs to family 4. Galois actions,
inner forms and central isogenies belong to family 6. Neither is repeated here, except
where a row of this family needs them. The comparison of relative roots and Weyl groups
with absolute ones is part of this family; it is section I.

## Status codes and evidence

Each row gives the source assertion with its locator, the exact Lean statement and its
hypotheses, a status, the evidence, and the owner task.

- **D (definition or internal result).** A published construction, or a published theorem
  that is not a proposition declaration, with the hypotheses listed in the row. The evidence
  is its module path. No owner task is needed.
- **P (published proof).** The Library at the commit above contains a theorem whose type is
  exactly the statement. The evidence is that theorem and its module path. The author also
  type-checked `example : S := proof` for every P row in a private module. That check
  passed with no errors or warnings, and `#print axioms` reported only `propext`,
  `Classical.choice` and `Quot.sound` for every proof theorem; it is not public evidence.
  No further proof work or owner task is needed.
- **C (composite, not published).** No published theorem has the statement as its type.
  However, a term built only from published theorems has that type: the author type-checked
  it in the same private module, and its axioms are `propext`, `Classical.choice` and
  `Quot.sound`. The composite is not an accepted artifact. The row names the owner task, or
  says that there is none. A conjunction of published components, or a projection out of a
  published conjunction, is also listed as C: what is missing is then a named wrapper
  theorem, not mathematics.
- **O (open).** A Lean statement exists, but no published proof and no composite from
  published results is known.
- **M (missing statement).** A source assertion of this family has no Lean statement in the
  Library. It is an obligation of the program, recorded with its owner task if one exists.

The labels "accepted" and "published" are used only for artifacts that passed independent
review. A "staged" candidate has passed machine validation only.

Source locators use these registered sources, cited by source id:

- `borel-tits-1965-groupes-reductifs`: A. Borel and J. Tits, *Groupes réductifs*, Publ. Math.
  IHÉS 27 (1965). Printed page = PDF page + 53.
- `borel-tits-1972-complements-groupes-reductifs`: A. Borel and J. Tits, *Compléments à
  l'article « Groupes réductifs »*, Publ. Math. IHÉS 41 (1972). Printed page = PDF page + 251.
- `milne-2017-algebraic-groups`: J. S. Milne, *Algebraic Groups* (2017). PDF page = printed
  page + 16. With it, the official errata snapshot
  `milne-2017-algebraic-groups-errata-2026-11-02`.
- `conrad-2014-reductive-group-schemes`: B. Conrad, *Reductive group schemes* (2014).
  Printed page = PDF page.
- `conrad-gabber-prasad-2015-pseudo-reductive`: B. Conrad, O. Gabber and G. Prasad,
  *Pseudo-reductive groups*, 2nd edition (2015). PDF page = printed page + 26.
- `kaletha-prasad-2023-bruhat-tits-new-approach`: T. Kaletha and G. Prasad, *Bruhat–Tits
  Theory: A New Approach* (2023). PDF page = printed page + 31.
- `renard-2026-representations-groupes-reductifs-padiques`: D. Renard, *Représentations des
  groupes réductifs p-adiques*, French version dated 9 July 2026. PDF page = printed page + 6.

The author re-read every locator below in the original source for this note, on 10 November
2026, and checked that the cited item is on the cited page.

## Conventions

- `IsSplitSubtorus i` (`Rational/SplitTorus`): `T` is a split torus (`T ≅ 𝔾_m^I` for a finite
  `I`) and `i : T ⟶ G` is a closed subgroup. `IsMaximalSplitTorus i`: `i` is a split subtorus
  and every factorization `f ≫ i' = i` through a split subtorus `i'` has `f` an isomorphism.
  Maximality is among split subtori **over the same field**.
- `splitRank G` (`Rational/SplitTorus`) is the supremum in `ℕ∞` of `card I` over closed
  subgroups `𝔾_m^I ⟶ G`. `IsAnisotropic G` means `splitRank G = 0`, the convention of
  Borel–Tits 4.23, printed p.93 (PDF 40).
- `IsParabolicSubgroup j` (`Absolute/Borel`): `j` is a smooth closed subgroup **defined over
  `k`** whose base change to `AlgebraicClosure k` contains a Borel subgroup. This is the
  geometric notion of Milne, Definition 17.15 and Theorem 17.16, printed p.356 (PDF 372),
  applied to subgroups defined over `k`; these are Borel–Tits's `k`-parabolic subgroups.
  `IsParabolicFunctor F` (`Rational/MinimalParabolic`) says that some such `j` has range `F`.
- `IsMinimalParabolicSubgroup j` (`Rational/MinimalParabolic`): `j` is parabolic, and every
  parabolic `j'` with `range j' ≤ range j` has the same range. Inclusion is tested on every
  test scheme, not only on rational points.
- `IsRationalLeviSubgroup l` (`Rational/LeviSubgroup`) for `l : L ⟶ P`: `P` has affine
  structure map, `l` is a closed subgroup, `L` is connected reductive, and for some
  `r : U ⟶ P` with `LeviSubgroup.IsGeometricUnipotentRadical r` (the unipotent radical of
  `P`, which stays the unipotent radical over `AlgebraicClosure k`) the multiplication
  `L × U → P` is an isomorphism of schemes over `k`. No row asserts that rational Levi
  subgroups exist for arbitrary smooth groups. Existence is asserted only for parabolic
  subgroups of connected reductive groups (row B13).
- `relativeRoots i` (`Rational/RelativeRoots`), for a split subtorus `i`, is the set of
  nonzero characters `χ` of `T` whose weight space in `Lie(G)` is nonzero. No reducedness is
  imposed, so `2α` may be a relative root together with `α`.
- `IsGenericCocharacter i ν` (`Rational/RelativeRoots`): `⟨α, ν⟩ ≠ 0` for every relative root
  `α`.
- `relativeWeylGroup i` (`Rational/RelativeRoots`) is `N(k)/Z(k)`: the rational points that
  normalize `i` (`normalizerPoints i`, `Torus/Maximal`) modulo those that centralize it
  (`centralizerPoints i`). Both are defined by the action on `T` over every test scheme.
- `Dynamic.parabolic χ`, `Dynamic.centralizer χ` and `Dynamic.unipotent χ` are the dynamic
  subgroup functors `P(χ)`, `Z(χ)` and `U(χ)` of a cocharacter `χ : 𝔾_m ⟶ G` defined over
  `k`, on all test schemes including nonreduced ones. `torusCentralizer i`
  (`Rational/TorusCentralizer`) is the all-test centralizer functor of `i`.
- `G.innerIso g` is conjugation by a rational point `g ∈ G(k)`. Conjugacy statements give
  `g` and an isomorphism `e` of sources with `i ≫ (G.innerIso g).hom = e.hom ≫ i'`.
- **Field hypotheses.** Unless a row says otherwise, a statement quantifies over every field
  `k : Type u`, of any characteristic, finite or infinite, perfect or not, with no
  valuation or topology. The rows with an extra field hypothesis are: C8 (`[Infinite k]`),
  E6 (`k` a nonarchimedean local field), H2 (`[Finite k]`), H3 (the dimension-one norm
  criterion) and the examples H5 (a quadratic extension with a nontrivial automorphism).
  `RelativeRoot.QuotientActionComparisonStatement` (row G1) is stated over an arbitrary
  base scheme.
- **Renard's scope.** Renard works over nonarchimedean local fields. Every row below that
  cites Renard has a Lean statement over every field, with no topology. Where the row also
  cites Borel–Tits, the arbitrary-field scope is that of Borel–Tits. Where it cites Renard
  alone (C11, D11, E1–E3), the arbitrary-field formulation is derived.

## A. Maximal split tori and rational conjugacy

**A1. Cocharacters factor through maximal split tori.** Source: derived. In the proof of
Proposition C.2.4, printed pp.594–595 (PDF 620–621), Conrad–Gabber–Prasad conjugate a
cocharacter "to arrange that λ takes values in S", a maximal `k`-split torus. Milne 2017,
§12.e, printed p.236 (PDF 252): a quotient of a split torus is split.
- Lean: `CocharacterMaximalSplitTorusStatement` (`Rational/MaximalSplitTorusStatement`).
  Hypotheses: a field group `G` with affine structure map, locally of finite type (no
  smoothness or connectedness); a cocharacter `χ : 𝔾_m ⟶ G`. Conclusion: a maximal split
  torus `i : T ⟶ G` and `ν ∈ X_*(T)` with `ν ≫ i = χ`.
- Status P: `cocharacterMaximalSplitTorus` (`Rational/CocharacterMaximalSplitTorusProof`).
- Also D: `exists_maximalSplitTorus_extension` (`Rational/MaximalSplitTorusExtension`): under
  the same hypotheses on `G`, every split subtorus factors through a maximal split torus.

**A2. Conjugacy of maximal split tori in smooth connected affine groups.** Source:
Conrad–Gabber–Prasad, Theorem C.2.3 (Borel–Tits), printed p.593 (PDF 619), with its proof on
pp.593–594 (PDF 619–620).
- Lean: `SmoothMaximalSplitTorusConjugacyStatement` (`Rational/MaximalSplitTorusStatement`).
  Hypotheses: `G` smooth, with affine structure map and connected; maximal split tori `i`,
  `i'`. Conclusion: `g ∈ G(k)` and `e : T ≅ T'` with `i ≫ int(g) = e ≫ i'`.
- Scope: no reductivity. The rank clause is not included; for reductive groups it is part
  of A4.
- Status P: `smoothMaximalSplitTorusConjugacy` (`Rational/SmoothMaximalSplitTorusConjugacyProof`).

**A3. The solvable branch.** Source: Conrad–Gabber–Prasad, proof of Theorem C.2.3, printed
pp.593–594 (PDF 619–620), the case of a solvable group.
- Lean: `SolvableMaximalSplitTorusConjugacyStatement` (`Rational/SolvableMaximalSplitTorusStatement`).
  Hypotheses: as A2, and `IsSolvableGroupScheme G`. Conclusion: as A2.
- Status P: `solvableMaximalSplitTorusConjugacy` (`Rational/SolvableMaximalSplitTorusConjugacyProof`).

**A4. Reductive groups: conjugacy and the rank.** Source: Borel–Tits 4.21 and 4.23, printed
p.93 (PDF 40); Milne 2017, Theorem 25.10, printed p.546 (PDF 562). The errata entry for
p.546 corrects "nontrivial" to "noncentral" in the first line of the proof of 25.10; the
statement is unchanged.
- Lean: `MaximalSplitTorusConjugacyStatement` (`Rational/ConjugacyStatement`). Hypotheses:
  `G` connected reductive. Conclusion: (1) any two maximal split tori are conjugate as in
  A2; (2) for every maximal split torus `i : T ⟶ G`, finite `I` and isomorphism
  `T ≅ 𝔾_m^I`, `card I = splitRank G`.
- Status P: `maximalSplitTorusConjugacy` (`Rational/MaximalSplitTorusConjugacyProof`).

**A5. Descent step of the conjugacy proof.** Source: derived from the proof of
Conrad–Gabber–Prasad, Theorem C.2.3, printed pp.593–594 (PDF 619–620).
- Lean: `SmoothMaximalSplitTorusDescentStatement` (`Rational/MaximalSplitTorusDescentStatement`).
  Hypotheses: as A2. Conclusion: either a smooth connected solvable closed subgroup through
  which every split subtorus factors (`SplitToriFactorThrough`), or a proper smooth connected
  closed subgroup into which every split subtorus can be conjugated by a rational point
  (`SplitToriConjugateInto`).
- Status P: `smoothMaximalSplitTorusDescent` (`Rational/MaximalSplitTorusDescentProof`).

**A6. Maximal split tori under central surjections.** Source: Borel–Tits 1972,
Théorème (2.20)(ii), printed p.260 (PDF 9): for a central surjective `k`-morphism
`f : G → G'`, the maximal `k`-split tori of `G'` are the images of those of `G`.
Definition (2.2), printed p.254 (PDF 3), defines central morphisms.
- Lean, lifting: `CentralIsogenyMaximalSplitTorusLiftStatement`
  (`Rational/CentralIsogenyMaximalSplitTorusLiftStatement`). Hypotheses: `G`, `H` connected
  reductive; `π : G ⟶ H` with `IsCentralIsogeny π`; a maximal split torus `i : S ⟶ H`.
  Conclusion: a maximal split torus `j : T ⟶ G` and `f : T ⟶ S` with `j ≫ π = f ≫ i`, `f`
  flat, surjective and locally of finite presentation.
  Status P: `centralIsogenyMaximalSplitTorusLift` (`CentralIsogeny/MaximalSplitTorusLiftProof`).
- Lean, images: `CentralSurjectionMaximalSplitTorusImageStatement`
  (`Rational/CentralSurjectionMaximalSplitTorusImageStatement`). Hypotheses: `G`, `H`
  connected reductive; `q : G ⟶ H` flat, surjective, locally of finite presentation, with
  central kernel; a maximal split torus `i` of `G`, a split subtorus `j` of `H`, and
  `p : T ⟶ T'` flat, surjective, locally of finite presentation with `p ≫ j = i ≫ q`.
  Conclusion: `j` is a maximal split torus.
  Status P: `centralSurjectionMaximalSplitTorusImage` (`Rational/CentralSurjectionMaximalSplitTorusImageProof`).
- Scope: both are derived factorization forms of (2.20)(ii); kernels need not be smooth.

## B. Rational parabolics, minimal parabolics and rational Levi subgroups

**B1. Parabolics defined over `k` are dynamic.** Source: Milne 2017, Theorem 25.1, printed
p.544 (PDF 560).
- Lean: `ParabolicDynamicStatement` (`Absolute/BorelStatement`). Hypotheses: `G` connected
  reductive; a closed subgroup `i : P ⟶ G`. Conclusion: `IsParabolicSubgroup i` if and only
  if `range i = P(χ)` for some cocharacter `χ : 𝔾_m ⟶ G` defined over `k`.
- Scope: this row relates the geometric definition of parabolic subgroups (family 4) to
  cocharacters over `k`.
- Status P: `parabolicDynamic` (`Absolute/ParabolicDynamicProof`).

**B2. Every parabolic contains a minimal one.** Source: derived; Borel–Tits use it in 4.16
and 4.18, printed pp.91–92 (PDF 38–39).
- Lean: `ParabolicContainsMinimalStatement` (`Rational/MinimalParabolicStatement`).
  Hypotheses: `G` connected reductive; a parabolic `j`. Conclusion: a minimal parabolic `j'`
  with `range j' ≤ range j`.
- Status P: `parabolicContainsMinimalStatement` (`Rational/ParabolicContainsMinimalProof`).

**B3. Minimal parabolics are rationally conjugate.** Source: Borel–Tits 4.13 b), printed
p.90 (PDF 37); Milne 2017, 25.22, printed p.550 (PDF 566).
- Lean: `MinimalParabolicConjugacyStatement` (`Rational/MinimalParabolicStatement`).
  Hypotheses: `G` connected reductive; minimal parabolics `j`, `j'`. Conclusion: `g ∈ G(k)`
  and `e : P ≅ P'` with `j ≫ int(g) = e ≫ j'`.
- Status P: `minimalParabolicConjugacy` (`Rational/MinimalParabolicConjugacyProof`).

**B4. The parabolic of a generic cocharacter is minimal.** Source: Borel–Tits 4.15 a) and
4.16, printed pp.90–91 (PDF 37–38).
- Lean: `GenericMinimalParabolicStatement` (`Rational/MinimalParabolicStatement`).
  Hypotheses: `G` connected reductive; a maximal split torus `i`; `ν` generic for `i`.
  Conclusion: `P(ν ≫ i)` is a minimal parabolic functor.
- Status P: `genericMinimalParabolic` (`Rational/GenericMinimalParabolicProof`).

**B5. Centralizer of a generic cocharacter.** Source: Borel–Tits 4.15 a), printed pp.90–91
(PDF 37–38); Milne 2017, Theorem 25.6(b), printed pp.545–546 (PDF 561–562). The errata entry
"p.545 et seq." says that the parabolic in 25.6(b) must be minimal.
- Lean: `GenericCentralizerStatement` (`Rational/Statement`). Hypotheses: as B4. Conclusion:
  `Z(ν ≫ i) = torusCentralizer i` on all test schemes.
- Status P: `genericCentralizer` (`Rational/GenericCentralizerProof`).

**B6. Maximal split tori of a minimal parabolic are conjugate inside it.** Source: derived
from Borel–Tits 3.14, printed p.80 (PDF 27), and 4.15 b), 4.16, printed pp.91–92 (PDF 38–39).
- Lean: `MinimalParabolicSplitTorusConjugacyStatement` (`Rational/ParabolicTorusStatement`).
  Hypotheses: `G` connected reductive; a minimal parabolic `j : P ⟶ G`; maximal split tori
  `i`, `i'` of `G` with factorizations `f`, `f'` through `P`. Conclusion: `p ∈ P(k)` and
  `e : T ≅ T'` with `f ≫ int_P(p) = e ≫ f'`.
- Status P: `minimalParabolicSplitTorusConjugacy` (`Rational/MinimalParabolicSplitTorusConjugacyProof`).

**B7. Parabolics are self-normalizing.** Source: Conrad 2014, Corollary 5.2.8, pp.155–156,
the scheme-theoretic form; Definition 5.2.1, p.151.
- Lean: `ParabolicSelfNormalizerStatement` (`Rational/ParabolicNormalizerStatement`).
  Hypotheses: `G` connected reductive; a parabolic `j`. Conclusion: the normalizer subgroup
  functor of `range j` equals `range j`.
- Status P: `parabolicSelfNormalizer` (`Rational/ParabolicNormalizerProof`).

**B8. Parabolics are connected.** Source: Milne 2017, Corollary 17.49, printed p.367
(PDF 383), the connectedness clause. Milne states it over an algebraically closed field;
the Lean statement applies it after base change to an algebraic closure.
- Lean: `ParabolicConnectedStatement` (`Rational/ParabolicConnectedConjugacy`). Hypotheses:
  `G` smooth, with affine structure map and connected (no reductivity); a parabolic `j`.
  Conclusion: `P` is connected.
- Status P: `parabolicConnected` (`Rational/ParabolicConnectedConjugacy`).

**B9. Two parabolics contain the centralizer of a common maximal split torus.** Source:
Borel–Tits 4.18, printed p.92 (PDF 39).
- Lean: `ParabolicIntersectionCentralizerStatement` (`Rational/ParabolicTorusStatement`).
  Hypotheses: `G` connected reductive; parabolics `j`, `j'`. Conclusion: a maximal split
  torus `i` with `torusCentralizer i ≤ range j` and `torusCentralizer i ≤ range j'`.
- Status P: `parabolicIntersectionCentralizer` (`Rational/ParabolicIntersectionCentralizerProof`).
- Weakening: `ParabolicIntersectionSplitTorusStatement` (`Rational/ParabolicIntersectionAssembly`):
  the same with "`i` factors through both parabolics". Status C:
  `parabolicIntersectionSplitTorusStatement_of_centralizer parabolicIntersectionCentralizer`.
  Owner task: none. It is a wrapper only.

**B10. Split part of a maximal torus in a minimal parabolic.** Source: derived from the
proof of Borel–Tits 4.18, printed p.92 (PDF 39), with 2.15 d), printed p.70 (PDF 17), 4.2–4.3,
printed pp.85–86 (PDF 32–33), and 4.15 b), 4.16. The printed proof of 4.18 cites "4.6" at
its Levi-to-split-torus step; the statement Markdown records this discrepancy.
- Lean: `MinimalParabolicTorusSplitPartStatement` (`Rational/MinimalParabolicTorusSplitPartStatement`).
  Hypotheses: `G` connected reductive; a minimal parabolic `j`; a maximal torus `t : T ⟶ G`
  factoring through `P`; a maximal split torus `a : A ⟶ T` of `T`. Conclusion: `a ≫ t` is a
  maximal split torus of `G`, and its centralizer is contained in `range j`.
- Status P: `minimalParabolicTorusSplitPart` (`Rational/MinimalParabolicTorusSplitPartProof`).
- The final transfer step is `TorusSplitPartTransferStatement` (`Rational/TorusSplitPartTransfer`),
  status P: `torusSplitPartTransfer` (same module).

**B11. Levi subgroups of a minimal parabolic.** Source: Borel–Tits 4.16, (i) ⇒ (iii),
printed pp.91–92 (PDF 38–39), and 4.15 b), printed p.91 (PDF 38).
- Lean: `MinimalParabolicLeviCentralizerStatement` (`Rational/MinimalParabolicLeviCentralizerStatement`).
  Hypotheses: `G` connected reductive; a minimal parabolic `j : P ⟶ G`; a rational Levi
  `l : L ⟶ P`; `r : R ⟶ P` with `IsGeometricSolvableRadical r`. Conclusion: a maximal split
  torus of `G` inside `R` whose centralizer equals `range (l ≫ j)`.
- Status P: `minimalParabolicLeviCentralizer` (`Rational/MinimalParabolicLeviCentralizerProof`).

**B12. Rational Levi subgroups of a parabolic are conjugate.** Source: Borel–Tits,
Corollary 3.14, printed p.80 (PDF 27). Borel–Tits state it for a connected `k`-subgroup of
maximal rank; the Lean statement is its specialization to parabolics of reductive groups.
- Lean: `RationalLeviConjugacyStatement` (`Rational/RationalLeviConjugacyStatement`).
  Hypotheses: `G` connected reductive; a parabolic `j : P ⟶ G`; rational Levis `l`, `l'` of
  `P`; `r : U ⟶ P` with `LeviSubgroup.IsGeometricUnipotentRadical r`. Conclusion: a
  **unique** `q ∈ U(k)` for which some `e : L ≅ L'` satisfies `l ≫ int_P(q) = e ≫ l'`.
- Status P: `rationalLeviConjugacy` (`Rational/RationalLeviConjugacyProof`).

**B13. Existence of rational Levi subgroups adapted to a maximal torus.** Source: Borel–Tits
3.14, printed p.80 (PDF 27), and the proof of 4.15 b), printed p.91 (PDF 38), where
`S' = R(P) ∩ T` has centralizer a `k`-Levi subgroup of `P` with connected centre `S'`.
- Lean: `ParabolicRadicalTorusLeviStatement` (`Rational/ParabolicRadicalTorusLeviStatement`).
  Hypotheses: `G` connected reductive; a parabolic `j : P ⟶ G`; a maximal torus
  `t : T ⟶ G` with a factorization `f` through `P`. Conclusion: a geometric solvable radical
  `r : R ⟶ P`; a torus `S` with closed `S ⟶ T` that is a maximal torus of `R` and has range
  `range f ⊓ range r`; and a rational Levi `l : L ⟶ P` such that `l ≫ j` represents the
  centralizer of `S` in `G`, `S` factors through `L`, and `S` is the largest central subtorus
  of `L`.
- Status P: `parabolicRadicalTorusLevi` (`Rational/ParabolicRadicalTorusLeviProof`).

**B14. Parabolics of a dynamic Levi.** Source: Renard V.3.8, printed p.111 (PDF 117), and
V.3.11, printed p.112 (PDF 118); Borel–Tits 4.4 c), printed pp.86–87 (PDF 33–34). Renard
works over a nonarchimedean local field; the Lean statement is over every field.
- Lean: `DynamicLeviParabolicCorrespondenceStatement` (`Rational/DynamicLeviParabolicCorrespondenceStatement`).
  Hypotheses: `G` connected reductive; a cocharacter `χ`; a closed subgroup `j : L ⟶ G`
  representing `Z(χ)`. Conclusion: an order isomorphism between parabolic functors of `L`
  and parabolic functors of `G` contained in `P(χ)`, given by `Dynamic.extendFromCentralizer`
  and its inverse by pulling back along `j`.
- Status P: `dynamicLeviParabolicCorrespondence` (`Rational/DynamicLeviParabolicCorrespondenceProof`).

## C. Relative roots and the relative Weyl group

**C1. The relative root system.** Sources: Borel–Tits 5.1–5.3, printed pp.95–96 (PDF 42–43),
and Corollary 5.8, printed p.98 (PDF 45); Milne 2017, 25.16–25.17, printed p.549 (PDF 565),
with Definition C.12, printed p.610 (PDF 626). The errata entry for p.549 says the
root-system assertion of 25.16 is correct but its classical proofs are incomplete, and
refers to Conrad–Gabber–Prasad, Theorem C.2.15, printed p.603 (PDF 629).
- Lean: `RelativeRootSystemStatement` (`Rational/Statement`). Hypotheses: `G` connected
  reductive; a maximal split torus `i`. Conclusion `HasRelativeRootSystem i`: a finite
  crystallographic root system over `ℚ` on `relativeRootSpan i` (paired with its dual by
  evaluation) whose roots are the images of the relative roots, whose Weyl group has image
  equal to the range of `relativeWeylAction i`, and with `relativeWeylAction i` injective.
- Scope: reducedness is not asserted. As Milne 25.17 says, the relative root system need
  not be reduced.
- Status P: `relativeRootSystem` (`Rational/RelativeRootSystemProof`).

**C2. Rank-one factorization in root groups.** Sources: Kaletha–Prasad, Proposition 2.11.17
and Remark 2.11.18, printed p.136 (PDF 167); Conrad–Gabber–Prasad, Proposition C.2.24 (i),
(iii), printed pp.620–622 (PDF 646–648).
- Lean: `RootRankOneFactorizationStatement` (`Rational/RootRankOneFactorizationStatement`).
  Hypotheses: `G` connected reductive; a maximal split torus `i`. Conclusion
  `RelativeRoot.HasRankOneFactorization i`: for each relative root `a` and each
  `u ≠ 1` in `U_a(k)` there is a unique pair `(p₁, p₂)` in `U_{-a}(k)` such that
  `p₁ u p₂` normalizes `i`; both factors are nontrivial and `p₁ u p₂` represents the
  reflection in `a`; when `2a` is not a root,
  `p₁ = p₂` and the square of `p₁ u p₂` lies in `T(k)`.
- Status P: `rootRankOneFactorization` (`Rational/RootRankOneFactorizationProof`).

**C3. Negation and root signs.** Sources: Kaletha–Prasad §2.6(b), printed p.93 (PDF 124),
and §2.11, Propositions 2.11.1–2.11.3, printed p.131 (PDF 162); Conrad–Gabber–Prasad,
Proposition 3.3.6, printed pp.109–110 (PDF 135–136).
- `RelativeRootNegationStatement` (`Rational/RelativeRootNegationStatement`): for `G`
  connected reductive and a maximal split torus `i`, `-α` is a relative root whenever `α` is.
  Status P: `relativeRootNegation` (`Rational/RelativeRootNegationProof`).
- `RelativeRootSignInclusionsStatement` (`Rational/RelativeRootSignInclusionsStatement`): for
  cocharacters `ζ`, `η` of `T`, `P(ζ ≫ i) ≤ P(η ≫ i)` if and only if every relative root
  nonnegative on `ζ` is nonnegative on `η`; and strict positivity transfers imply
  `U(ζ ≫ i) ≤ U(η ≫ i)`. Status P: `relativeRootSignInclusions` (`Rational/RelativeRootSignInclusionsProof`).
- `RelativeRootSignsDetermineDynamicStatement` (`Rational/RelativeRootSignsStatement`): if `ζ`
  and `η` have the same signs on all relative roots, they have the same `P`, `Z` and `U`.
  Status P: `relativeRootSignsDetermineDynamic` (`Rational/RelativeRootSignsProof`).

**C4. Reflections exist in `N(k)`.** Source: Conrad–Gabber–Prasad, Lemma C.2.14 and the
discussion after it, printed pp.601–602 (PDF 627–628), and the proof of Theorem C.2.15,
Step 2, printed pp.604–605 (PDF 630–631).
- Lean: `RelativeRootReflectionExistenceStatement` (`Rational/RootReflectionExistenceStatement`).
  Hypotheses: `G` connected reductive; a maximal split torus `i`. Conclusion: reflection data
  `RelativeRootReflectionData i` (for each relative root `α` an integral coroot `α^∨` with
  `⟨α, α^∨⟩ = 2` and `n_α ∈ N(k)` acting on `X^*(T)` by `χ ↦ χ - ⟨χ, α^∨⟩ α`) whose
  representatives lie in the centralizer of `ker α`.
- Status P: `relativeRootReflectionExistence` (`Rational/RootReflectionExistenceProof`).

**C5. Simple roots and rank identities.** Sources: Borel–Tits 4.23, printed p.93 (PDF 40),
4.27, printed p.94 (PDF 41), and Théorème 5.3 with its proof, printed pp.96–97 (PDF 43–44);
Renard V.2.5–V.2.6, printed pp.107–108 (PDF 113–114), and V.3.6–V.3.7, printed p.111
(PDF 117). The Lean formulation is derived.
- `RelativeSimpleRootBasisStatement` (`Rational/RelativeRankStatement`): for `G` connected
  reductive, a maximal split torus `i` and generic `ν`, the simple relative roots are
  finite, form a `ℚ`-basis of `relativeRootSpan i`, and their number is the relative root
  rank. Status P: `relativeSimpleRootBasis` (`Rational/RelativeSimpleRootBasisProof`).
- `RelativeRankIdentityStatement` (same module): `ℚ ⊗ X^*(T)`, the relative root span and
  `ℚ ⊗ X^*(G)_k` are finite dimensional; `splitRank G = dim T`;
  `dim T = relative root rank + rank X^*(G)_k`; and for a split component `a : A ⟶ G`,
  restriction `ℚ ⊗ X^*(G)_k → ℚ ⊗ X^*(A)` is bijective and `dim T = relative root rank + dim A`.
  Status P: `relativeRankIdentity` (`Rational/RelativeRankIdentityProof`).
- The conjunction `RelativeRankStatement` (same module). Status C:
  `⟨relativeSimpleRootBasis, relativeRankIdentity⟩`. Owner task: none.

**C6. Normalizer and centralizer of a split torus.** Sources: Milne 2017, Proposition 1.83,
printed p.31 (PDF 47), Proposition 1.92, printed p.33 (PDF 49), and Corollary 13.10, printed
p.257 (PDF 273).
- Lean: `TorusNormalizerRepresentableStatement` (`Rational/TorusNormalizerStatement`).
  Hypotheses: `G` connected reductive; a split subtorus `i`. Conclusion: the all-test
  functors `torusNormalizer i` and `torusCentralizer i` have smooth closed representatives.
- Status P: `torusNormalizerRepresentable` (`Rational/TorusNormalizerProof`).

**C7. The relative Weyl group as a constant group.** Sources: Milne 2017, 25.16(b)(c) and
25.17, printed p.549 (PDF 565); Borel–Tits, Théorème 5.3, printed p.96 (PDF 43).
- Lean: `RelativeWeylGroupRestrictStatement` (`Rational/TorusNormalizerStatement`).
  Hypotheses: `G` connected reductive; a maximal split torus `i`; a connected scheme `U`
  over `k`. Conclusion: the restriction `N(k)/Z(k) → N(U)/Z(U)` is bijective.
- Status P: `relativeWeylGroupRestrict_bijective` (`Rational/RelativeWeylGroupRestrictProof`).

**C8. Normalizer points over infinite fields.** Sources: Milne 2017, Proposition 1.84,
printed p.32 (PDF 48), and Proposition 1.93, printed p.34 (PDF 50).
- Lean: `NormalizerPointsInfiniteFieldStatement` (`Rational/TorusNormalizerStatement`).
  Hypotheses: `[Infinite k]`; `G` connected reductive; a split subtorus `i`. Conclusion:
  `normalizerPoints i` and `centralizerPoints i` equal the abstract normalizer and
  centralizer in `G(k)` of the image of `T(k)`.
- Scope: the field must be infinite, because the comparison uses density of `T(k)` in `T`.
  The statement Markdown records the counterexample `GL_2` over `𝔽_2`.
- Status P: `normalizerPointsInfiniteField` (`Rational/NormalizerPointsInfiniteFieldProof`).

**C9. The relative Weyl group is a finite Coxeter group.** Sources: Borel–Tits, Théorème 5.3,
printed p.96 (PDF 43), Corollaire 5.8, printed p.98 (PDF 45), and 5.15–5.18, printed
pp.100–101 (PDF 47–48); Renard V.3.4, printed p.110 (PDF 116), V.3.7, printed p.111
(PDF 117), and V.4.6, printed pp.120–121 (PDF 126–127). Renard works over a nonarchimedean
local field; Borel–Tits give the arbitrary-field scope of the Lean statement.
- Lean: `RelativeWeylCoxeterStatement` (`Rational/RelativeWeylCoxeterStatement`).
  Hypotheses: `G` connected reductive; a maximal split torus `i`; generic `ν`. Conclusion
  `HasRelativeWeylCoxeterSystem i ν`: `N(k)/Z(k)` and the simple roots are finite, and a
  Coxeter system on `N(k)/Z(k)` indexed by the simple roots realizes the root action
  (`IsRelativeWeylCoxeterRealization`): simple reflections act by integral reflection
  formulas, the length of `w` is the number of reduced positive roots that `w` makes
  negative, and the Coxeter parabolic subgroups are the standard relative Weyl subgroups.
- Status P: `relativeWeylCoxeter` (`Rational/RelativeWeylCoxeterProof`).

**C10. Standard Weyl subgroups.** Source: Borel–Tits, Proposition 5.17, printed p.101
(PDF 48).
- `StandardRelativeWeylGenerationStatement` (`Rational/TitsStandardParabolicStatement`): for
  `J` a set of simple roots, the subgroup generated by the reflections in `J` is
  `standardRelativeWeylGroup i ν J`. Status P: `standardRelativeWeylGeneration`
  (`Rational/StandardRelativeWeylGenerationProof`).
- `NormalizerStandardParabolicStatement` (same module): `n ∈ N(k)` lies in `P_J(k)` if and
  only if its class lies in `W_J`. Status P: `normalizerStandardParabolicStatement`
  (`Rational/NormalizerStandardParabolicProof`).

**C11. Renard's root conventions.** Source: Renard V.3.4, printed p.110 (PDF 116), and
V.3.12, printed p.112 (PDF 118).
- Lean: `RenardRootConventionStatement` (`Rational/RenardRootConventionStatement`).
  Hypotheses: `G` connected reductive; a maximal split torus `i`; generic `ν`. Conclusion:
  the nonzero weights of `T` on `U(ν ≫ i)` are the positive relative roots; their
  indivisible members are the reduced positive roots; and the simple ones among those are
  the simple relative roots.
- Status P: `renardRootConvention` (`Rational/RenardRootConventionProof`).

## D. Rational Bruhat decomposition, Tits system and standard parabolics

**D1. Rational Bruhat decomposition.** Sources: Borel–Tits, Théorème 5.15, printed p.100
(PDF 47), where `P` is the minimal standard parabolic fixed in 5.12, printed p.99 (PDF 46);
Milne 2017, 25.27, printed p.551 (PDF 567). The errata entry "p.545 et seq." says that in
25.27 the parabolic `P` must be minimal and `S` maximal split in `P`. Without minimality
the decomposition is false: for `GL_2` and `P = G` both double cosets are all of `G(k)`.
- Lean: `RationalBruhatStatement` (`Rational/Statement`). Hypotheses: `G` connected
  reductive; a maximal split torus `i`; `ν` generic for `i`. The parabolic is
  `P = P(ν ≫ i)`, which is minimal by B4. Conclusion `HasRationalBruhatDecomposition i ν`:
  every `g ∈ G(k)` is `p n q` with `p, q ∈ P(k)` and `n ∈ N(k)`, and two points `n, n'` of
  `N(k)` lie in the same double coset `P(k) n P(k)` if and only if they have the same class
  in `N(k)/Z(k)`.
- Status P: `rationalBruhat` (`Rational/RationalBruhatProof`).

**D2. The relative Tits system.** Sources: Borel–Tits 5.15–5.18, printed pp.100–101
(PDF 47–48), in particular 5.18: "5.15 et 5.16 montrent que les axiomes de [33] sont
vérifiés"; Milne 2017, 25.27, printed p.551 (PDF 567), last paragraph; Renard V.4.1,
printed p.118 (PDF 124).
- Lean: `RelativeTitsSystemStatement` (`Rational/RelativeTitsSystemStatement`). Hypotheses:
  as D1. Conclusion `HasRelativeTitsSystem i ν`: `(G(k), P_∅(k), N(k), S)` is a Tits system
  with Weyl group `N(k)/Z(k)` and `S` the reflections in the simple roots; each simple root
  has exactly one reflection, and distinct simple roots have distinct reflections.
- Status P: `relativeTitsSystem` (`Rational/RelativeTitsSystemProof`).

**D3. Standard parabolics at the endpoints.** Source: Borel–Tits 5.12, printed p.99 (PDF 46),
with 4.2, printed pp.85–86 (PDF 32–33); Renard V.3.8, printed p.111 (PDF 117).
- Lean: `StandardParabolicEndpointsStatement` (`Rational/StandardParabolicEndpointsStatement`).
  Conclusion: `P_∅ = P(ν ≫ i)`, `L_∅ = torusCentralizer i`, `P_Δ = L_Δ = G` and `U_Δ = 1`.
- Status P: `standardParabolicEndpoints` (`Rational/StandardParabolicEndpointsProof`).

**D4. Classification of parabolics by standard ones.** Source: Borel–Tits, Proposition 5.14,
printed p.99 (PDF 46); Renard V.3.9, printed p.112 (PDF 118).
- Lean: `StandardParabolicClassificationStatement` (`Rational/StandardParabolicClassificationStatement`).
  Conclusion: every `P(ζ)` containing `P(ν ≫ i)` is a standard `P_J`; and every `P(ζ)` is
  `G(k)`-conjugate to `P_J` for a unique `J` among the subsets of the simple roots.
  Parabolics over `k` are given by cocharacters through B1.
- Status P: `standardParabolicClassification` (`Rational/StandardParabolicClassificationProof`).

**D5. Order of standard parabolics.** Source: Borel–Tits 5.14, printed p.99 (PDF 46), and
5.18 (ii), printed p.101 (PDF 48).
- Lean: `StandardParabolicOrderStatement` (`Rational/StandardParabolicOrderStatement`).
  Conclusion: `J ⊆ K` if and only if `P_J ≤ P_K`; then `L_J ≤ L_K` and `U_K ≤ U_J`; and
  `J ↦ P_J` is injective.
- Status P: `standardParabolicOrder` (`Rational/StandardParabolicOrderProof`).

**D6. Rational points of standard parabolics.** Source: Borel–Tits 5.17 and 5.18 (i)–(ii),
printed p.101 (PDF 48), and 5.20, printed p.102 (PDF 49); Renard V.4.5, printed p.119
(PDF 125).
- Lean: `StandardParabolicPointsStatement` (`Rational/StandardParabolicPointsStatement`).
  Conclusion: `P_J(k) = P(k) W_J P(k)`; the subgroups of `G(k)` containing `P(k)` are
  exactly the `P_J(k)`; each `P_J(k)` is self-normalizing in `G(k)`; and
  `W_J\W/W_K ≅ P_J(k)\G(k)/P_K(k)` through representatives in `N(k)`.
- Status P: `standardParabolicPointsStatement_proof` (`Rational/StandardParabolicPointsProof`).

**D7. `B W_J B = P_J(k)`.** Source: Borel–Tits, Proposition 5.17, printed p.101 (PDF 48).
- Lean: `TitsStandardParabolicStatement` (`Rational/TitsStandardParabolicStatement`):
  `P_J(k)` equals the standard parabolic subgroup `B W_J B` of the Tits system of D2 with
  `B = P_∅(k)`.
- Status C: `titsStandardParabolicStatement_of_statements standardParabolicEndpoints
  standardParabolicPointsStatement_proof standardRelativeWeylGeneration`.
- Owner task: Task 3857 (`604afc86-19c2-42df-bc5b-bf27328630a2`). Its proof candidate
  `7eecbc87-c14a-467b-ab5c-709bf27c3039` is staged and not yet reviewed.

**D8. Finite parabolic double cosets with torus-adapted representatives.** Sources:
Borel–Tits, Corollaire 5.20, printed p.102 (PDF 49); Renard V.4.5, Corollaire, printed p.120
(PDF 126), and V.4.7, printed pp.121–122 (PDF 127–128). The torus clause is derived from
Borel–Tits 4.18.
- Lean: `RepresentedParabolicDoubleCosetStatement` (`Rational/ParabolicDoubleCosetStatement`).
  Hypotheses: `G` connected reductive; parabolics `p`, `q` with rational Levis `l`, `lQ`.
  Conclusion: `P(k)\G(k)/Q(k)` is finite, and every double coset has a representative `z`
  and a maximal split torus that factors through `l ≫ p` and through `lQ ≫ q ≫ int(z)`.
- Status C: `representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs rationalBruhat
  genericMinimalParabolic minimalParabolicConjugacy parabolicIntersectionCentralizer
  parabolicDynamic smoothMaximalSplitTorusConjugacy` (`Rational/ParabolicDoubleCosetAssembly`).
- Owner task: Task 4901 (`f78f48cb-43dd-4e38-a665-b8e068407586`), which has no candidate yet.

**D9. Standard cocharacters and standard Levi subgroups.** Sources: Borel–Tits 3.13,
printed pp.78–80 (PDF 25–27), 4.2, printed pp.85–86 (PDF 32–33), and 5.12, printed p.99
(PDF 46); Renard V.4.2, printed p.118 (PDF 124), and V.4.3, printed p.119 (PDF 125).
- `StandardCocharacterStatement` (`Rational/StandardCocharacterStatement`): for each `J`
  there is a standard cocharacter `ζ` (zero on `J`, positive on the other simple roots),
  and every such `ζ` has `P(ζ ≫ i) = P_J`, `Z(ζ ≫ i) = L_J` and `U(ζ ≫ i) = U_J`.
  Status P: `standardCocharacter` (`Rational/StandardCocharacterProof`).
- `StandardLeviConjugationStatement` (`Rational/StandardLeviConjugationStatement`): for
  `J, J' ⊆ Δ`, if the Weyl class of `n ∈ N(k)` carries the roots of `J'` onto those of
  `J`, then conjugation by `n` carries `L_{J'}` onto `L_J`: `n L_{J'} n^{-1} = L_J`,
  equivalently `L_{J'} = n^{-1} L_J n`. In Lean, `L_{J'}` equals the preimage of `L_J`
  under `int(n) : x ↦ n x n^{-1}`. Separately, for every `J ⊆ Δ` the conjugate image
  `n L_J n^{-1}` depends only on the class of `n` in `N(k)/Z(k)`.
  Status P: `standardLeviConjugation` (`Rational/StandardLeviConjugationProof`).

**D10. Moving a maximal split torus into a Levi.** Source: derived from Borel–Tits 4.18,
printed p.92 (PDF 39), and the proof of 5.15, printed p.100 (PDF 47); Renard V.4.7, printed
pp.121–122 (PDF 127–128).
- Lean: `ParabolicSplitTorusLeviConjugacyStatement` (`Rational/ParabolicDoubleCosetRepresentatives`).
  Hypotheses: `G` connected reductive; a parabolic `p : P ⟶ G` with a rational Levi `l`; a
  maximal split torus `i` factoring through `P`. Conclusion: `u ∈ P(k)` and `a : T ⟶ M`
  with `a ≫ l ≫ p = i ≫ int(u)`.
- Status P: `parabolicSplitTorusLeviConjugacy` (`Rational/ParabolicSplitTorusLeviConjugacyProof`).

**D11. Root presentations of a parabolic.** Sources: Renard V.3.9, printed p.112 (PDF 118),
and V.3.14, printed p.113 (PDF 119). The formulation over every field is derived.
- `ParabolicRootPresentationStatement` (`Rational/ParabolicRootPresentationStatement`), the
  conjunction of three parts. For `G` connected reductive, a parabolic `p`, a rational Levi
  `l` and a split component `a` of the Levi, a `ParabolicRootPresentation p l a` is a
  maximal split torus, a generic cocharacter and a set `J` of simple roots presenting `P`
  as `P_J` and `L` as `L_J`. The three parts are `ParabolicRootPresentationExistenceStatement`
  (one exists), `ParabolicRootPresentationIndependenceStatement` (any two give the same
  restricted roots and cones) and `ParabolicRootPresentationIsoStatement` (an isomorphism
  of split components carries them to each other).
- Status P for the conjunction: `parabolicRootPresentation` (`Rational/ParabolicRootPresentationProof`).
  Status P for existence: `parabolicRootPresentationExistence` (same module).
- `ParabolicRootPresentationIndependenceStatement` and `ParabolicRootPresentationIsoStatement`:
  status C, the projections `parabolicRootPresentation.2.1` and `parabolicRootPresentation.2.2`.
  Owner task: none.

## E. Split components, rational characters and the centre

**E1. The split component.** Source: Renard V.2.1, printed p.104 (PDF 110).
- Lean: `SplitComponentStatement` (`Rational/CharactersStatement`). Hypotheses: `G` connected
  reductive. Conclusion: a split component `A ⟶ G` (a maximal central split torus) exists,
  and any two are isomorphic compatibly with the inclusions.
- Status P: `splitComponentStatement` (`Rational/SplitComponentProof`).

**E2. Rational characters.** Sources: Renard V.2.2, printed p.105 (PDF 111), and V.2.6,
Lemme, printed pp.107–108 (PDF 113–114).
- `RationalCharacterLatticeStatement` (`Rational/CharactersStatement`): for `G` connected
  reductive, `X^*(G)_k` is free of finite rank over `ℤ`. Status P: `rationalCharacterLattice`
  (`Rational/CharacterLatticeProof`).
- `CharacterRestrictionStatement` (same module): restriction `X^*(G)_k → X^*(A)` to a split
  component is injective with image of finite index. Status P: `characterRestriction`
  (`Rational/CharacterRestrictionProof`).

**E3. Split components of Levi subgroups.** Sources: Renard V.3.1, printed p.110 (PDF 116),
and V.3.6, printed p.111 (PDF 117).
- Lean: `LeviSplitComponentStatement` (`Rational/CharactersStatement`). Hypotheses: `G`
  connected reductive; a maximal split torus `i`; `μ ∈ X_*(T)`; a closed subgroup
  `j : M ⟶ G` representing `Z(μ ≫ i)`. Conclusion: `M` is connected reductive, and for a
  split component `A_G` of `G` there is a split component `A_M` of `M` with
  `A_G ⊆ A_M ⊆ T` and restriction maps of characters compatible with these inclusions.
- Status P: `leviSplitComponentStatement` (`Rational/LeviSplitComponentProof`).

**E4. Central directions.** Sources: Borel–Tits 4.23 and 4.27, printed pp.93–94 (PDF 40–41),
and Théorème 5.3, printed p.96 (PDF 43); Renard V.3.6–V.3.7, printed p.111 (PDF 117). The
Lean formulation is derived.
- `RelativeCharacterRootComplementStatement` (`Rational/RelativeCentralDirectionsStatement`):
  the relative root span and the image of the rational characters are complements in
  `ℚ ⊗ X^*(T)`, and also over `ℝ`. Status P: `relativeCharacterRootComplement`
  (`Rational/RelativeCharacterRootComplementProof`).
- `RelativeSplitCentralDirectionsStatement` (same module): dimensions of the real spaces,
  `N(k)/Z(k)` fixes the central directions, and a split component embeds into `T` with
  cocharacter image the central directions and character kernel the root span. Status P:
  `relativeSplitCentralDirections` (`Rational/RelativeSplitCentralDirectionsProof`).
- The conjunction `RelativeCentralDirectionsStatement` (same module). Status C:
  `⟨relativeCharacterRootComplement, relativeSplitCentralDirections⟩`. Owner task: none.

**E5. General linear groups.** Sources: Milne 2017, Example 21.6, printed p.426 (PDF 442),
Example 21.36, printed p.435 (PDF 451), Example 21.40, printed p.436 (PDF 452), 25.13,
printed p.548 (PDF 564), and 25.16–25.17, printed p.549 (PDF 565); Conrad–Gabber–Prasad,
Example 2.1.1, printed pp.45–47 (PDF 71–73).
- `GeneralLinearRationalStatement` (`Rational/GeneralLinearStatement`): the diagonal torus of
  `GL_n` is a maximal split torus, its relative roots are `χ_i - χ_j` (`i ≠ j`), it has a
  relative root system, and generic cocharacters have centralizer the diagonal torus.
  Status P: `generalLinearRationalStatement` (`Rational/GeneralLinearProof`).
- `GeneralLinearStandardParabolicStatement` (`Rational/GeneralLinearStandardParabolicStatement`):
  for a strictly decreasing generic cocharacter, the simple roots are the adjacent
  differences, and the standard parabolic, Levi and unipotent subgroups of a subset `J`
  (and their rational points) are the block upper triangular, block diagonal and block
  unipotent matrices of the block shape of `J`. Status P: `generalLinearStandardParabolic`
  (`Rational/GeneralLinearStandardParabolicProof`).
- `GeneralLinearCharactersStatement` (`Rational/CharactersStatement`): for every `n`, every
  rational character of `GL_n` is an integer multiple of `det`, and `det` restricts to the
  scalar torus as `n` times the identity character; for `n = 0` every rational character is
  zero (`GL_0` is trivial); **for `n ≥ 1`** `det` has infinite order and the scalar torus is
  a split component (for `n = 0` the map `𝔾_m → GL_0` is not a closed immersion). For
  every block shape, the block determinants form a `ℤ`-basis of the rational characters of
  the block Levi. Status P: `generalLinearCharacters` (`Rational/CharactersProof`).

**E6. Rational points of the centre over a local field.** Sources: Milne 2017,
Proposition 1.92, printed p.33 (PDF 49), which defines the centralizer by commutation after
every extension of scalars, and Proposition 1.93, printed p.34 (PDF 50): if `H` is smooth
and `H(k')` is dense in `H`, then `C_G(H)(k)` consists of the elements of `G(k)` that
centralize `H(k')`.
- Lean: `RationalCenterComparisonStatement` (`Rational/RationalCenterComparisonStatement`).
  Hypotheses: `F` a **nonarchimedean local field** (`ValuativeRel`, `TopologicalSpace`,
  `IsNonarchimedeanLocalField`); `M` connected reductive. Conclusion: the `F`-points of the
  scheme centre of `M` equal the centre of the abstract group `M(F)`.
- Scope: the statement is not asserted over other fields. The published proof follows the
  shape of Milne 1.93, with density of `M(F)` obtained from the local field (an implicit
  function argument), not from unirationality. Milne, Theorem 17.93, printed p.382
  (PDF 398), gives density of `G(k)` for a connected reductive `G` over any infinite field;
  combined with 1.93 that would give the comparison over every infinite field, but no such
  statement or proof is in the Library.
- Status P: `rationalCenterComparison` (`Rational/RationalCenterComparisonProof`).

## F. Smooth connected affine groups (Conrad–Gabber–Prasad, Appendix C.2)

In this section `G` is smooth, with affine structure map and connected; no reductivity is
assumed. `IsPseudoParabolicSubgroup` is the pseudo-parabolic notion of Conrad–Gabber–Prasad.

**F1. Rational points of `G/P` lift.** Source: Conrad–Gabber–Prasad, Lemma C.2.1 and its
proof, printed pp.592–593 (PDF 618–619).
- Lean: `PseudoParabolicQuotientRationalLiftingStatement`
  (`PseudoParabolicQuotientRationalLiftingStatement`). Hypotheses: a pseudo-parabolic `i`;
  a **supplied** quotient `q : G ⟶ Q` with `Q` separated, locally of finite type and
  quasi-compact, `q` smooth, surjective and quasi-compact, and fibres the cosets of `P` on
  every test scheme. Conclusion: every `k`-point of `Q` lifts to `G(k)`.
- Status P: `pseudoParabolicQuotientRationalLifting` (`PseudoParabolicQuotientRationalLiftingProof`).

**F2. Split solvable subgroups and split tori move into a pseudo-parabolic.** Source:
Conrad–Gabber–Prasad, Lemma C.2.2, printed p.593 (PDF 619).
- `SplitSolvableIntoPseudoParabolicStatement` (`SplitSolvableIntoPseudoParabolicStatement`):
  a closed split solvable subgroup `H` is conjugate by a rational point into `P`. Status P:
  `splitSolvableIntoPseudoParabolic` (`SplitSolvableIntoPseudoParabolicProof`).
- `SplitTorusIntoPseudoParabolicStatement` (`SplitTorusIntoPseudoParabolicStatement`): the
  same for a split subtorus. Status P: `splitTorusIntoPseudoParabolic`
  (`Rational/SmoothMaximalSplitTorusConjugacyProof`).

**F3. Maximal split tori of pseudo-parabolics.** Source: Conrad–Gabber–Prasad,
Proposition C.2.4, printed p.594 (PDF 620).
- Lean: `PseudoParabolicMaximalSplitTorusStructureStatement`
  (`Rational/PseudoParabolicMaximalSplitTorusStructureStatement`). Conclusion: a maximal split
  torus `s` of `P` is maximal split in `G`, its centralizer lies in `P`, and `P` is minimal
  pseudo-parabolic if and only if `P` is the fppf product of that centralizer and the split
  unipotent radical of `P`.
- Status P: `pseudoParabolicMaximalSplitTorusStructure` (`Rational/PseudoParabolicMaximalSplitTorusStructureProof`).

**F4. Minimal pseudo-parabolics are conjugate.** Source: Conrad–Gabber–Prasad, Theorem C.2.5
(Borel–Tits), printed p.595 (PDF 621).
- Lean: `MinimalPseudoParabolicConjugacyStatement` (`Rational/MinimalPseudoParabolicConjugacyStatement`).
  Conclusion: two minimal pseudo-parabolics are conjugate by a rational point
  (`SubgroupConjugate`).
- Status P: `minimalPseudoParabolicConjugacy` (`Rational/MinimalPseudoParabolicConjugacyProof`).

**F5. The subgroup generated by the tori is normal.** Source: Conrad–Gabber–Prasad,
Proposition A.2.11, printed p.477 (PDF 503).
- Lean: `TorusGeneratedEnvelopeNormalityStatement` (`Rational/TorusGeneratedEnvelopeNormalityStatement`).
  Hypotheses: `G` as above, over **every** field (finite fields included); a
  `TorusGeneratedEnvelope G`. Conclusion: its range is normal.
- Status P: `torusGeneratedEnvelopeNormality` (`Rational/TorusGeneratedEnvelopeNormalityProof`).

## G. Relative root subgroups

These statements are in the namespace `Langlands.GroupScheme.RelativeRoot`; their proofs
are in the same namespace. Sources: Kaletha–Prasad §2.6.3 and §2.6.8, printed pp.94–95
(PDF 125–126), Proposition 2.11.9, printed p.133 (PDF 164), and Proposition 2.11.14,
printed p.135 (PDF 166); Conrad–Gabber–Prasad, Proposition 3.3.6 and Lemma 3.3.8, printed
pp.109–112 (PDF 135–138), Theorem 3.3.11, printed p.114 (PDF 140), and Corollary 3.3.12,
printed p.116 (PDF 142).

**G1. Root subgroups** (`Rational/RootSubgroupStructureStatement`). For `G` connected
reductive and a maximal split torus `i` unless stated otherwise:
- `CharacterFpqcStatement`: every nonzero character of a split torus is quasi-compact, flat
  and surjective onto `𝔾_m`. Status P: `characterFpqc` (`Rational/CharacterFpqcProof`).
- `KernelCentralizerStructureStatement`: for `G` smooth with affine structure map (no
  reductivity), a split torus acting through `i` and `a ≠ 0`, the centralizer of `ker a`
  has a smooth closed representative with Lie image all integral multiples of `a`.
  Connectedness is not asserted. Status P: `kernelCentralizerStructure`
  (`Rational/KernelCentralizerStructureProof`).
- `QuotientActionComparisonStatement`: over an **arbitrary base scheme**, given a closed
  representative of the kernel centralizer and a character map that is quasi-compact, flat
  and surjective, `U_a` is the image of the unipotent part of the quotient action. Status P:
  `quotientActionComparison` (`Rational/QuotientActionComparisonProof`).
- `RootSubgroupRealizationStatement`: each `U_a` for a relative root `a` has a smooth,
  connected, unipotent, split unipotent closed representative, stable under `T`, with Lie
  image the positive integral `a`-weight span. Status P: `rootSubgroupRealization`
  (`Rational/RootSubgroupRealizationProof`).
- `RootSubgroupUniquenessStatement`: a smooth connected closed `T`-stable subgroup with that
  Lie image has the same functor as `U_a`. Status P: `rootSubgroupUniqueness`
  (`Rational/RootSubgroupUniquenessProof`).
- `RootSubgroupVectorStatement`: if `2a` is not a root, `U_a` is a vector group; if it is,
  `U_{2a} ⊆ U_a` is central in `U_a` and the fppf quotient is a vector group. Status P:
  `rootSubgroupVector` (`Rational/RootSubgroupVectorProof`).
- The conjunction `RootSubgroupStructureStatement`. Status C: the six proofs above as a
  tuple. Owner task: none.

**G2. Ordered products** (`Rational/RootProductStatement`):
- `SemigroupOrderedProductStatement`: let `G` be smooth, with affine structure map,
  connected and solvable, with an action of a split torus, and let the weights of the
  action be the union of pairwise disjoint sets `Ψ_1, …, Ψ_n`, none of which meets the
  additive closure of another. Then the subgroups attached to the closures of the `Ψ_r` are
  represented by smooth connected closed subgroups, and their ordered product map is an
  isomorphism. Status P:
  `semigroupOrderedProduct` (`Rational/SemigroupOrderedProductProof`).
- `RelativeRootRayDecompositionStatement`: the indivisible positive roots are finite, their
  rays are disjoint, and they cover the positive roots. Status P:
  `relativeRootRayDecomposition` (`Rational/RootRayDecompositionProof`).
- `DynamicRootOrderedProductStatement`: for any ordering of the indivisible positive roots,
  `U(ν ≫ i)` is represented by a smooth connected split unipotent closed subgroup that is
  the ordered product of the root subgroups. Status P: `dynamicRootOrderedProduct`
  (`Rational/DynamicRootOrderedProductProof`).
- The conjunction `RootProductStatement`. Status C: the three proofs above as a tuple. Owner
  task: none.

## H. Quasi-split, anisotropic and non-split groups

None of the rows above assumes that `G` is split or quasi-split, or that its split rank is
positive. A relative root system may be empty or nonreduced.

**H1. Definitions.**
- `IsQuasiSplit G` (`Reductive/QuasiSplit`), D: `G` is connected reductive and has a closed
  subgroup defined over `k` that is a Borel subgroup after base change to an algebraic
  closure. Source: Milne 2017, 17.66–17.67, printed p.375 (PDF 391).
- `IsAnisotropic G` (`Rational/SplitTorus`), D: `splitRank G = 0`. Source: Borel–Tits 4.23,
  printed p.93 (PDF 40). The theorem `IsAnisotropic.relativeRoots_eq_empty`
  (`Rational/RelativeRoots`), D: for an anisotropic `G` with affine structure map, every split
  subtorus has no relative roots.

**H2. Reductive groups over finite fields are quasi-split.** Source: Milne 2017,
Proposition 17.99 and the sentence after its proof, printed p.384 (PDF 400).
- Lean: `FiniteFieldQuasiSplitStatement` (`Rational/FiniteFieldQuasiSplitStatement`).
  Hypotheses: `[Finite k]`; `G` connected reductive. Conclusion: `IsQuasiSplit G`.
- Status P: `finiteFieldQuasiSplit` (`Rational/FiniteFieldQuasiSplit`).

**H3. Steinberg's theorem.** Source: Kaletha–Prasad, Theorem 2.3.3(2), printed p.79
(PDF 110), with the dimension-one criterion of §2.3, printed pp.78–79 (PDF 109–110).
- Lean: `DimensionLEOneQuasiSplitStatement` (`Rational/DimensionLEOneQuasiSplitStatement`).
  Hypotheses: `Langlands.FieldTheory.HasDimensionLEOne K` (for every finite separable `E/K`
  and finite Galois `L/E` the norm `L^× → E^×` is surjective); `H` connected reductive.
  Conclusion: `IsQuasiSplit H`.
- Status O. Owner task: Task 4733 (`0367ba06-f71f-44ff-83b2-e9de61795702`), waiting, with no
  proof candidate.

**H4. Maximally split maximal tori of quasi-split groups.** Source: derived from
Kaletha–Prasad, Fact 2.6.22 and its proof, printed p.104 (PDF 135), and Remark 2.6.25(2),
printed p.105 (PDF 136), with Definition 2.6.2, printed p.93 (PDF 124).
- Lean: `QuasiSplitMaximalTorusCentralizerStatement` (`Rational/QuasiSplitMaximalTorusCentralizerStatement`).
  Hypotheses: `IsQuasiSplit G`; a maximal torus `i : T ⟶ G`, a maximal split torus
  `a : A ⟶ G` and `f : A ⟶ T` with `f ≫ i = a`. Conclusion: `i` represents
  `torusCentralizer a`.
- Status P: `quasiSplitMaximalTorusCentralizer` (`Rational/QuasiSplitMaximalTorusCentralizerProof`).

**H5. A non-split group with a nonempty relative root system: `U(1,1)`.** Source: Milne 2017,
Definition 19.20, printed p.401 (PDF 417), Definition 19.22, printed p.402 (PDF 418), and
the unitary groups of 24.40–24.44, printed pp.523–525 (PDF 539–541). These are program
examples; their formulation is derived.
- All four statements are in `Langlands.GroupScheme.QuasiSplitUnitary`. Hypotheses: fields
  `F`, `E` with `E/F` quadratic, `c : E ≃ₐ[F] E` with `c ≠ id`, and an `F`-basis `b` of
  `M_2(E)`; the group is `QuasiSplitUnitary.groupScheme b c`.
- `RankStatement` (`Examples/QuasiSplitUnitaryRankStatement`): the diagonal cocharacter is
  a closed subgroup, every closed split torus over `F` has dimension at most one, and over
  `E` there is a closed split torus of dimension two. Status P: `QuasiSplitUnitary.rankStatement`
  (`Examples/QuasiSplitUnitaryRankProof`).
- `NotSplitStatement` (`Examples/QuasiSplitUnitaryNotSplitStatement`): the group has no
  split maximal torus. Status P: `QuasiSplitUnitary.notSplit` (`Examples/QuasiSplitUnitaryNotSplitProof`).
- `LeviRepresentedStatement` and `LeviDecompositionStatement`
  (`Examples/QuasiSplitUnitaryLeviRepresentedStatement`, `Examples/QuasiSplitUnitaryLeviDecompositionStatement`):
  the centralizer of the cocharacter is represented by an explicit closed Levi subgroup,
  and `P(λ) = Z(λ) ⋉ U(λ)` with `P(λ) ∩ P(λ⁻¹) = Z(λ)` and `U(λ⁻¹) ∩ P(λ) = 1`. Status P:
  `QuasiSplitUnitary.leviRepresentedStatement`, `QuasiSplitUnitary.leviDecompositionStatement`
  (`Examples/QuasiSplitUnitaryLeviRepresentedProof`, `Examples/QuasiSplitUnitaryLeviDecompositionProof`).
- The non-split torus `Res_{ℂ/ℝ} 𝔾_m` is listed in the published family-2 ledger
  [ledger-family-2-tori.md](ledger-family-2-tori.md).

## I. Relative and absolute structure

**I1. Relative roots are the nonzero restrictions of absolute roots.** Source: Milne 2017,
25.13 with its footnote 2, printed p.548 (PDF 564), and 25.19, printed p.549 (PDF 565): for
a maximal torus `T` containing a maximal split torus `S`, the relative roots are the
nontrivial restrictions to `S` of the roots of `(G, T)_{k^s}`.
- D: `mem_roots_iff_exists_splittingField_restriction` (`Rational/AbsoluteRootRestriction`).
  Hypotheses: fields `k`, `K` with `Algebra k K`; `G` over `k` with affine structure map,
  locally of finite type; a split torus `T`; a commutative `M` whose base change to `K` is
  a split torus; `f : T ⟶ M` and `j : M ⟶ G`; a character `α` of `T`. Conclusion: `α` is a
  root of `f ≫ j` (a relative root when `f ≫ j` is a maximal split torus) if and only if
  `α ≠ 0` and some root `β` of `j_K` satisfies `f_K ≫ β = α_K`.
- D: `exists_maximalTorus_extension_of_finiteType` (`Rational/MaximalTorusFiniteType`): for
  `G` affine and locally of finite type over a field, every closed torus factors through a
  maximal torus. With a field over which that maximal torus splits (the `IsTorus` notion of
  family 2), this supplies the `M` and `K` of the previous theorem.
- Scope: this is a theorem with hypotheses, not a closed proposition; no Lean statement
  packages Milne's assertion as one proposition. Its consequence
  `relativeRootNegationStatement_of_rootDatum_fieldExtension_maximalTorus` (same module)
  derives C3's negation stability from it.

**I2. The relative Weyl group as a restriction of absolute Weyl elements.** Source:
Borel–Tits, Corollaire 5.5, printed p.97 (PDF 44): for a maximal torus `T` split over an
extension `K` and containing `S`, `N(S) = N(S, T) · Z(S)` with `N(S, T) = N(S) ∩ N(T)`, so
the relative Weyl group is the restriction to `S` of `N(S, T)/Z(T)`.
- Status M: the Library has no statement comparing `relativeWeylGroup` with the Weyl
  group of a maximal torus after a field extension. Owner task: none.

**I3. Relative root groups from absolute root groups.** Source: Milne 2017, 25.19, printed
p.549 (PDF 565): the subgroup of `G_{k^s}` generated by the root groups `U_β` with
`β|_S = α` is defined over `k`; it is the root group `U_α`.
- The relative root groups themselves are constructed and characterized over `k` (G1). A
  statement comparing them with absolute root groups after a field extension has status M.
  Owner task: none.

## Summary and remaining obligations

Counted by the Lean statements named above, 79 have published proofs (P). Nine have a
composite from published results and no published wrapper theorem (C): the conjunctions
`RelativeRankStatement`, `RelativeCentralDirectionsStatement`,
`RelativeRoot.RootSubgroupStructureStatement` and `RelativeRoot.RootProductStatement`; the
projections `ParabolicRootPresentationIndependenceStatement` and
`ParabolicRootPresentationIsoStatement`; the weakening
`ParabolicIntersectionSplitTorusStatement`; and the source theorems
`TitsStandardParabolicStatement` (D7, Task 3857) and
`RepresentedParabolicDoubleCosetStatement` (D8, Task 4901). One row is open (O):
Steinberg's theorem `DimensionLEOneQuasiSplitStatement` (H3, Task 4733). Two source
assertions have no Lean statement (M): the relative/absolute Weyl comparison (I2) and the
relative/absolute root group comparison (I3); neither has an owner task. The root
comparison I1 is available as a published theorem with hypotheses (D).

Remaining obligations of this family:

1. Accepted proofs for D7 and D8 from their owner tasks.
2. A proof of Steinberg's theorem (H3).
3. Named wrapper theorems for the C rows without an owner task. These need no new
   mathematics; the program will collect them in one proof task.
4. Statements for I2 and I3, and a closed proposition for I1.
5. The centre comparison of E6 is stated and proved only over nonarchimedean local fields.
   The Library has no statement of it over other fields; this ledger records that scope and
   claims nothing beyond it.
