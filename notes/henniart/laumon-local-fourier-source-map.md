# Laumon's local Fourier transform for E1b: source map

Written on 17 November 2026 and checked against Library commit `b369a8f280229cf081a17f96b81c7a8c1ff1f539`.

This note is a planning document. It proves nothing and states no Lean
declaration. It maps the part of Laumon's 1987 paper that the
numerical step uses (statement E1b) onto exact source locations, records what
the published edition does and does not contain, and lists the obligations that
remain. It complements item R3 of the
[Route A program plan](numerical-route-a-program.md), which locates the same
theorem at a coarser level and did not check the twist locators; section 2
below corrects one of its locators.

Sources and page rules. "La87" is Laumon, *Transformation de Fourier,
constantes d'équations fonctionnelles et conjecture de Weil*, Publ. Math. IHÉS
65 (1987), registered as `laumon-1987-fourier-weil`; printed page = PDF page
+ 129. All PDF page numbers in this note count from 1 in the central-library
file. "H88" is Henniart 1988 (`henniart-1988-numerical`); printed page = PDF page + 495.
Numbers in parentheses such as (2.4.3) are La87's own numbering. "The route
note" and "the plan note" are two planning notes
(`operator-numerical-llc-route-2026-11-16`,
`operator-external-inputs-plan-2026-11-16`).

## 1. What E1b needs, and where the sheaf theory stops

E1b is the route note's Corollary `cor:Laumon` (H88 §4.3) and item E1b of
the plan note §2.5. For `K' = F_q((t))`, `ℓ ≠ p` and `d, s ≥ 1`, it gives a
bijection between the isomorphism classes of irreducible continuous
`Q̄_ℓ`-representations of `Gal(K'^sep/K')` of dimension `d` and Swan conductor
`s` and those of dimension `d + s` and Swan conductor `s`. The bijection
commutes with twists by unramified characters. At the commit above the Library
had no E1b statement. The Library now states the route note's combined p-adic
statement (LD), which combines E1a and E1b, as `LaumonDeligneCountStatement`
(`Correspondence/HenniartLaumonDeligneStatement.lean`).

The proof splits at a named premise **S**. S is not an established result:
it is what the sheaf-theoretic part of the proof must deliver. Fix `k = F_q`, `ℓ ≠ p` and a non-trivial additive character `ψ`.
La87 (2.4.1), p. 162, allows for `T` and `T'` any two henselian traits of
equal characteristic `p` with residue field `k` and chosen uniformizers `π`,
`π'`. This note takes them complete: `T = Spec k[[π]]` (Laumon's trait at
`0`) and `T' = Spec k[[π']]` (his trait at `∞'`). Let `G` and `G'` be the
absolute Galois groups of their fraction fields `k((π))` and `k((π'))`. S is
La87 (2.4.3)(i) b) and c), restated on isomorphism classes of continuous
finite-dimensional `Q̄_ℓ`-representations:

- **S1.** A map `F` from isomorphism classes of `G`-representations to
  isomorphism classes of `G'`-representations.
- **S2.** If `V` is irreducible, then `F(V)` is irreducible,
  `dim F(V) = dim V + sw V` and `sw F(V) = sw V`.
- **S3.** `F` is injective on irreducible classes. Every irreducible `W` with
  all slopes `< 1` is `F(V)` for some irreducible `V`. (By c), `F^(0,∞')` is
  an equivalence `G → G'_[0,1[`. The subcategory `G'_[0,1[` is closed under
  subobjects, so its simple objects are the irreducible `G'`-modules with all
  slopes `< 1`, and an equivalence matches simple objects.)
- **S4.** `F(χ ⊗ V) = χ ⊗ F(V)` for every continuous character `χ` of
  `Gal(k̄/k)`, inflated to `G` and to `G'`.

The sheaf-free remainder is:

- (a) transport along the `k`-isomorphisms `k((π)) ≅ F_q((t)) ≅ k((π'))`
  sending `π` and `π'` to `t` (H88 §4.3 takes `K = K'` with matching
  uniformizers); these are the identity on `k`, so unramified characters match;
- (b) an irreducible representation has a single slope, because the slope
  decomposition La87 (2.1.2.4) is a decomposition as `G`-modules (stated after
  (2.1.2.5), p. 152); so dimension `d + s` and Swan conductor `s` force all
  slopes to equal `s/(d + s) < 1`, and S3 applies;
- (c) the assembly of E1b from S, (a) and (b). By S2, `F` sends an
  irreducible class of dimension `d` and Swan conductor `s` to an irreducible
  class of dimension `d + s` and Swan conductor `s`, and by S3 this map is
  injective. For surjectivity, let `W` be irreducible of dimension `d + s` and
  Swan conductor `s`. By (b) all its slopes are `< 1`, so S3 gives an
  irreducible `V` with `F(V) = W`. Then S2 gives `sw V = sw W = s` and
  `dim V = dim W − sw V = d`. By S4 the map commutes with unramified twists, so
  with injectivity it preserves the torsion number (the number of unramified
  characters `χ` with `χ ⊗ V ≅ V`);
- (d) the passage from orbits of `ℓ`-adic Galois classes to orbits of complex
  Weil classes under unramified twists, preserving dimension, Swan conductor
  and torsion number (H88 §§4.1–4.2, pp. 509–510). This step imports a
  general finite-image Weil/Galois dictionary (this note names it
  `Langlands.Henniart.WeilGaloisDictionaryStatement`; no proof of it is found
  by name in the Library); it is not proved twice. The dictionary leaves the
  comparison of `ℓ`-adic with complex representations to this step.

The formal hand-over point between the sheaf-theoretic and the sheaf-free
parts is a single statement, for `X = F_q((t))` (Mathlib's `LaurentSeries`)
and each `d ≥ 1`, `s ≥ 0`, of a bijection between the irreducible `ℓ`-adic
classes of dimension `d` and Swan conductor `s` and those of dimension `d + s`
and Swan conductor `s`, given by one map that commutes with every unramified
twist. S is the list of obligations behind that statement; neither S nor the
statement is an assumption that discharges Laumon's theorem.

The sheaf-theoretic part includes proving S, choosing the base library (a
decision after the reuse audit), and comparing
the complete traits with henselizations. Lemma (2.4.2.1) relates `T` and `T'`
to the global sheaves on `A` and `A'` through the `k`-morphisms `π ↦ x` and
`π' ↦ 1/x'` (and their variants), that is, through the henselizations of `A`
at `0` and of `A'` at `∞'`. So the proof of (2.4.2.1) for complete traits
needs the restriction isomorphism from the Galois group of the completion to
that of the henselization, compatible with inertia, upper numbering and Swan
conductors, together with the corresponding comparison of nearby cycles. This
is bridge (b2) of the plan note §4.1. If the sheaf-theoretic part works with
henselizations instead, the same restriction isomorphism, not a field
isomorphism, must precede (a).

## 2. Laumon's theorem and the locators Henniart cites

| H88 §4.3 (p. 510) cites | Published La87 | Finding |
|---|---|---|
| "[Lm], 2.4.2.3" | Définition (2.4.2.3), p. 163 (PDF 34) | Defines `F^(0,∞')`, `F^(∞,0')`, `F^(∞,∞')` as stalks of `R¹Φ` of `pr*V_!` (or `pr*V`) tensored with an Artin–Schreier sheaf in the two uniformizers. |
| "[Lm], Thm. 2.4.3c" | Théorème (2.4.3)(i) c), p. 163 | Equivalence `G → G'_[0,1[` with quasi-inverse `a* F^(∞',0)(−)(1)`. The page image of H88 p. 510 reads "c". Text extraction renders it as "e", and the Route A note's R3 quotes "2.4.3e"; there is no item e). |
| rank and Swan formulas | Théorème (2.4.3)(i) b), p. 163 | `r(F V) = r(V) + s(V)`, `s(F V) = s(V)`, "de sorte que" `F(G) ⊂ G'_[0,1[`. |
| "[Lm] 2.5.2 et 3.6.3" (twist compatibility) | (2.5.2), p. 165; no (3.6.3) | (2.5.2) is compatibility with base change `k → k_1 ⊂ k̄`. La87 §3.6 (pp. 200–203) contains only (3.6.1), with (3.6.1.1)–(3.6.1.3), and Théorème (3.6.2). The route note's Theorem `thm:Laumon` repeats the citation of (3.6.3). |

The twist compatibility S4 does not need a separate theorem. An unramified
character `χ` is a rank-one lisse sheaf pulled back from `Spec k`. Tensoring
with it commutes with `j_!`, with `pr*`, with the Artin–Schreier kernel and with `RΦ`
(projection formula for `Rj̄_*` with a locally constant sheaf of free rank-one
modules; `RΨ`, `RΦ` are defined in SGA 7 XIII 2.1.1). Its restriction to the
generic point of `T'` is the same character `χ`, now as a character of
`G'`. I found no numbered statement of this projection formula in SGA 7 XIII.
A proof of S4 must either derive it from the definitions or locate it
in the chosen base.

La87 uses the isomorphism-class form of (2.4.3)(i) itself, in the special
case `r = p^n`, `s = 1`: (2.6.2), p. 172, says that `F^(0,∞')` "induit une
bijection entre les ensembles des classes d'isomorphie" of these irreducible
modules. Remark (2.6.2.3), p. 173, attributes the numerical local Langlands
conjecture in equal characteristic to Henniart by this method, citing
[He 2] = Henniart, letter to Laumon, 27 March 1986.

## 3. The proof of (2.4.3)(i) b) and c), in dependency order (La87 §2.5, pp. 165–169)

1. (2.5.1), p. 165: a) (exactness) follows from (2.4.2.2); b) reduces to simple `V`.
2. (2.5.2), p. 165: base change to `k_1 ⊂ k̄`; b) reduces to `k` algebraically
   closed.
3. (2.5.3), pp. 165–167: tame case. Proposition (2.5.3.1) computes the three
   transforms of `Q̄_ℓ` and of the Kummer modules `V_χ`, with Gauss sums
   `G(χ, ψ)`. It uses (1.2.3.1), (1.4.3.2)(iii), (2.3.2.1), (2.3.3.1),
   (2.4.2.1), (1.3.1.2) and SGA 4½ Th. finitude Cor. 2.16. Lemma (2.5.3.2),
   p. 167, says `RΨ` at an isolated point is a direct summand; it uses SGA 7
   XIII (2.1.7.1).
4. (2.5.4), p. 167: `F^(∞,0')` vanishes on `G_[1,∞[`, by (2.3.2.3)(ii) and
   (2.4.2.1)(ii). `F^(∞,∞')` vanishes on `G_[0,1]`, by (2.3.1.1)(i),
   (2.3.3.1)(iii), (2.4.2.1), (2.5.3) and a dimension count. Both use the
   canonical extension (2.2.2.2).
5. (2.5.5), pp. 167–169, proves b) with the following steps.
   - Let `F` be the canonical extension of `V` to `A − {0}`, tame at `∞`.
   - (2.3.1.3)(i) gives `r(F(j_!F)) = a_0(j_!F) = r + s`.
   - Stationary phase gives `π'*(F(j_!F)|η_∞') ≅ F^(0,∞')(V)`. This uses
     (2.3.3.1)(iii), (2.4.2.1)(ii),(iii) and (2.5.3), which says that
     `F^(∞,∞')` of a tame module is 0.
   - `F(j_!F)` is lisse of rank `r + s` on `A' − {0'}`, with `r_0' = s` and
     tame at `0'`.
   - `RΓ_c = 0`, by involutivity and proper base change.
   - The Grothendieck–Ogg–Shafarevich formula (2.2.1.2) then gives Swan
     conductor `s` at `∞'`.
6. (2.5.6), p. 169, constructs `a* F^(∞',0) ∘ F^(0,∞')(V)(1) ≅ V` for all
   `V`. This uses involutivity (1.2.2.3), (2.3.2.1), (2.4.2.1), (2.3.3.1) and
   (2.5.3). The analogous isomorphisms for the other two transforms, and those
   obtained by exchanging `T` and `T'`, give c).
7. (2.5.7), duality d): not needed for E1b.

**The inclusion `F(G) ⊂ G'_[0,1[`.** La87 states it in b) with "de sorte
que" and gives no separate argument in (2.5.5). The rank and Swan formulas
alone only bound the average slope `s/(r + s)`. The inclusion follows from
step 6 and the rank formula, without circularity. Let `W = F^(0,∞')(V)` and
split `W = W_<1 ⊕ W_≥1` by (2.1.2.4).

- By (2.4.3)(ii) b) with `T` and `T'` exchanged, which is proved in (2.5.4),
  `F^(∞',0)` kills `W_≥1`. So the isomorphism of step 6 gives
  `V ≅ a* Y(1)` with `Y = F^(∞',0)(W_<1)`, a `G`-module.
- Pullback by the automorphism `a` (`π ↦ −π`) and the Tate twist preserve
  rank and Swan conductor. The rank formula of b), proved in (2.5.5) without
  the inclusion, therefore gives `dim W = r(V) + s(V) = r(Y) + s(Y)`.
- The second isomorphism of (2.5.6), for `F^(∞,0')` on `G_[0,1[`, becomes
  after exchanging `T` and `T'` an isomorphism `a'* F^(0,∞')(Y)(1) ≅ W_<1`,
  with `a'` the automorphism `π' ↦ −π'`. Hence
  `dim W_<1 = r(Y) + s(Y)` as well, and `W_≥1 = 0`.

A second route uses Proposition (2.3.1.1), p. 158, applied to `K = j_!F[1]`.
Its formula (i)' gives `r(W_]1,∞[) = s(W_]1,∞[)`, hence `W_]1,∞[ = 0`. Here
La87 defines `r`, `r_x`, `s_x`, `a_x` additively, so they are negative for a
shifted sheaf, and `a_0'` of the transform has absolute value `r`. Formula
(ii)' and Lemma (2.2.1.1) show that `W_1 ⊗ L(a·x')` is purely of slope 1 for
every `a ≠ 0`. To conclude `W_1 = 0` this route also needs the fact that
every character of `I^(1)/I^(1+)` is the restriction of some `L_ψ(a·x')`. I
have not located a source for that fact, so the first route is recommended.

## 4. What the proof uses inside La87 (§§1.2–2.4)

- §1.2 (pp. 141–145): Fourier–Deligne transform (1.2.1.1); involutivity
  (1.2.2.1)–(1.2.2.3); base change (1.2.2.9); transform of the constant sheaf
  (1.2.3.1).
- §1.3 (pp. 146–147): forgetting supports (1.3.1.1) and universal local
  acyclicity (1.3.1.2), both from Katz–Laumon 1985 (2.1.3, 2.4.4);
  perversity and the equivalence on perverse sheaves (1.3.2.3); simple goes to
  simple (1.3.2.4).
- §1.4 (pp. 148–150): the notation `A, A', D, D'`; the types T1–T3 and Theorem
  (1.4.2.1) (cites BBD 4.3.1(ii)); Kummer sheaves and Gauss sums (1.4.3.1),
  (1.4.3.2) (cite SGA 4½ *Sommes trig.* 4.3, 4.20).
- §2.1 (pp. 150–155): henselian traits, `G ⊃ I ⊃ P`, upper filtration
  (2.1.1); finiteness of `P`-images (2.1.2.2); semisimplicity, slopes and the
  slope decomposition (2.1.2.3)–(2.1.2.4); Swan conductor (2.1.2.5); integrality
  of `λ·r(V_λ)` (2.1.2.6, Hasse–Arf, cites Katz 1983 pp. 211–215); tensoring
  with a rank-one module of Swan conductor 1 (2.1.2.7); `L_ψ(1/π)` (2.1.2.8);
  tame and unramified modules (2.1.4)–(2.1.5).
- §2.2 (pp. 155–157): local monodromy and `r_x, s_x, a_x` (2.2.1); Lemma
  (2.2.1.1) (cites BBD 4.0); GOS (2.2.1.2) (cites Raynaud, Bourbaki 286, and
  SGA 5 X 7); tame isomorphism (2.2.2.1); Gabber–Katz canonical extension
  (2.2.2.2) (cites Katz 1986 (1.4)).
- §2.3 (pp. 157–161): Proposition (2.3.1.1) and Corollaries (2.3.1.2),
  (2.3.1.3); the vanishing-cycle triangle (2.3.2) (SGA 7 XIII (1.4.2.2));
  Proposition (2.3.2.1) and Corollary (2.3.2.3); stationary phase at `∞'`
  (2.3.3.1). Remark (2.3.2.4) (semicontinuity) is not used.
- §2.4 (pp. 162–163): traits `T, T'` (2.4.1); local–global comparison
  (2.4.2.1), stated without proof as "immédiat"; concentration in degree 1
  (2.4.2.2); Definition (2.4.2.3).

## 5. External sources

| Source ID | Item | Locator |
|---|---|---|
| `deligne-1973-sga7-xiii-cycles-evanescents` | `RΨ`, `RΦ`; triangle (1.4.2.2); `RΨ Rf_* ≅ Rf_* RΨ` for `f` proper (2.1.7.1) | 2.1.1 (PDF 17); (1.4.2.2) (PDF 16–17); (2.1.7.1) (PDF 20) |
| `deligne-1977-sga4-half-cohomologie-etale` | over a field every complex is universally locally acyclic; Gauss sums | Th. finitude Cor. 2.16 (printed 243); *Sommes trig.* Prop. 4.3 (printed 196) and 4.20 |
| `katz-laumon-1985-fourier-sommes-exponentielles` | (1.3.1.1), (1.3.1.2) | 2.1.3, 2.4.4 |
| `katz-1986-local-to-global-extensions` | canonical extension (2.2.2.2) | Main Theorem 1.4.1; Theorem 1.5.6 |
| `raynaud-1965-bourbaki-286-euler-poincare` | GOS formula (2.2.1.2) | Théorème 1 (§3), proof in §4 |
| `serre-1979-local-fields` | upper numbering, Hasse–Arf, Artin and Swan conductors | IV §3; VI §2 |
| `deligne-1973-local-constants`, `tate-1979-number-theoretic-background` | H88 §4.1 ("[De 1], [Ta]"): finite image after an unramified twist | — |
| `provided-dfb1ff840caee48a9ec4bf735fc5417d1d5b55a59e5f27ad4fe2755bb24fede5` (Katz, *Wild ramification and some problems of "independence of ℓ"*, Amer. J. Math. 105 (1983)) | integrality of `λ·r(V_λ)` (2.1.2.6); single slope after tensoring with a character of larger Swan conductor (compare (2.1.2.7)) | printed pp. 211–213: finite `P`-image, slopes, multiplicities and Swan conductor, Hasse–Arf integrality on p. 213; p. 214: the rationality corollary (whose proof also uses Hasse–Arf), then a slope-bound lemma (`r > Swan(V)` implies `r` exceeds the largest slope of `V`, so `I^(r)` acts trivially on `V`) and a tensor-product lemma (for a rank-one `L` with `Swan(L)` larger than the largest slope of `V`: (1) `L ⊗ V` has the single slope `Swan(L)` with multiplicity `dim V`, on p. 214; (2) `L ⊗ V` has no `P`-invariants or coinvariants, and the proof, on p. 215) (PDF page = printed page − 199) |
| `provided-830095b3f7fe74814d46089e979bcae5137893f26af277d16110ec2fb4bcaf5f` (BBD, *Faisceaux pervers*, Astérisque 100 (1982), original edition) | perverse t-structure used in §1.3; Theorem 4.3.1 cited at (1.4.2.1); 4.0 cited at (2.2.1.1) | chapter 4 begins on printed p. 101 with 4.0; Theorem 4.3.1 (simple perverse sheaves are the intermediate extensions of irreducible lisse sheaves) on printed p. 112 (PDF page = printed page + 1) |

BBD matters only if the chosen base lacks the perverse t-structure on curves
that La87 §1.3 uses. La87 cites it on pp. 135, 138, 147, 149, 155 and 160.

## 6. Open obligations

1. Prove S (S1–S4) on the chosen base, including the twist compatibility S4,
   which has no numbered source (section 2), and the slope inclusion of
   section 3.
2. Compare the complete traits with the henselizations of `A` at `0` and of
   `A'` at `∞'` that Lemma (2.4.2.1) uses (section 1): the restriction
   isomorphism of Galois groups must respect inertia, the upper-numbering
   filtrations and the Swan conductors used in the Library, and the nearby and
   vanishing cycles over the complete trait must agree with those over the
   henselization (plan note §4.1, bridges (b1)–(b4)). This uses the Galois
   side of nonarchimedean local fields in both characteristics.
3. Prove (a)–(c) of section 1, and (d) by importing the Weil/Galois
   dictionary. This needs the characteristic-`p` definitions of the Galois
   side and a statement of E1b.
4. Lemma (2.4.2.1) is stated in La87 as immediate. The formalization must
   supply its proof from the definitions of `RΦ` and the traits.
