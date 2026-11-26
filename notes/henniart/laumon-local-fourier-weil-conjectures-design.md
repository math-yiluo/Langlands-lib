# Laumon's local Fourier bijection on weil-conjectures

The target is `Langlands.Henniart.LaumonLadicTwistBijectionStatement` in
`Langlands.Correspondence.HenniartLadicStatement`. Its prescribed interface is a
bijection of actual irreducible ℓ-adic Galois classes, of ranks `d` and `d+s`
with the same transported Swan exponent `s ≥ 1`, at `X = LaurentSeries k`
for a finite field `k`. One bijection has to commute with every character in
`Langlands.Henniart.LocalNumerical.ladicUnramifiedCharacters X (SeparableClosure X) ℓ`.
At Library commit `2cda61adeed2b8811c903c00be6b0a4097683eb8`, the class and twist
constructions are present in `Langlands.Correspondence.HenniartLadicClasses` and
the target module is absent. The plan uses the prescribed target and its
`LadicHasSwan` predicate as the interface. The four mathematical obligations S1–S4
and Henniart's locators are in the companion [source map](laumon-local-fourier-source-map.md).

## 1. Arithmetic setting and normalization

Fix `k` finite of characteristic `p`, a prime `ℓ` invertible in `k`, and
`E = PadicAlgCl ℓ`. Choose a nontrivial additive character `ψ` of `k` with
values in `E` once, for both directions of the transform. A nontrivial character
of the prime field followed by the finite-field trace gives the choice.
Use `A = 𝔸¹_k` and its dual `A'` with coordinates `x,x'`, and their projective
completions `D,D'`. Use geometric Frobenius for the Weil degree, with value `q⁻¹` on `E(1)`,
and the Tate normalization in the same-character formula `FTψ FTψ ≅ a* (−)(−1)`, where
`a(x) = −x`. In the external formula the shifts `[-2][1][1]` cancel. The
normalization of `FTψ` is `Rp₂!(p₁*K ⊗ Lψ(xx'))[1]` on an input complex `K`.
[Laumon 1987, (0.2), (1.2.1.1) and (1.2.2.3)](https://www.numdam.org/item/PMIHES_1987__65__131_0/)

**Sheaves.** Use arithmetic lisse sheaves on the punctured traits and
arithmetic constructible pro-étale complexes for the Fourier kernels.
Compute nearby cycles after pulling the kernels to the chart over a
single chosen strict henselization of the target. Keep the arithmetic
realization and its descent maps for each input and output. Use the condensed Artin–Schreier
kernel and affine-line Fourier functor in §3.4. Use the corresponding Weil
complex on the geometric fibre with its geometric Frobenius structure for the
global cohomology and perversity inputs. Compare pullback, extension by zero,
tensor by the kernel and `Rp₂!` on the two models using the operation
comparisons in §3.4. Construct the inversion used on the local Galois
representations with the arithmetic compact-support maps. The map on local classes
comes from the arithmetic stalks, with isomorphisms respecting the full local
Galois action. This retains the finite coefficient field and the topology
required by Laumon's G-modules. Finite constant-field extensions, with kernel
character `ψ ∘ Tr`, suffice for the tame calculation and the generic-rank
argument. Use algebraic closures for strict-trait exchange and finiteness,
and separable closures for the Galois-layer arguments. The generic-fibre
exchange in §4.4 relates the complexes and arithmetic actions on these
models. Construct the comparisons, stationary-phase decomposition, inverse and twist
maps over `k`. Check vanishing and ranks on geometric fibres, and use
conservativity of geometric pullback to test whether an arithmetic map
already constructed is an isomorphism. Prove the equalities between
derived comparison maps with the full arithmetic action using the
naturality of specialization and exchange on the strict charts.
[Laumon 1987, (1.2.2.9), (2.1.2)–(2.1.2.1), (2.5.2)](https://www.numdam.org/item/PMIHES_1987__65__131_0/)

**Traits.** Define the local operations first on the henselizations at `0`
and `∞'`, with `x` and `1/x'` as uniformizers, and use the corresponding
charts at `∞` and `0'` for the other two phases. The fraction fields of
these henselizations complete to copies of `k((t))`. Use the Library's
henselian finite étale completion equivalence to compare Galois groups, and
prove the valuation, residue and ramification compatibilities in (b2).
On the geometry side, choose the strict target trait using the maximal
unramified subextension of the chosen separable generic closure. Form
each geometric generic fibre by extension from this strict trait along
the chosen embedding of its fraction field. Compare strict localizations
at the indicated geometric points in Laumon's Lemme (2.4.2.1) over this
same strict target. The pullback of the finite-type
global kernel and the local kernel agree on the prescribed opens, with the
same extension by zero on their boundary. Compare specialization maps as
well as nearby cycles before passing to the cofiber. Use strictly
henselian trait exchange to compare with `Spec k̄[[t']]` for
finiteness and proper exchange. The Galois action is constructed on
the strict henselian chart from the compatible action on its total,
generic and special spaces. The ambient weakly étale base-change map
for the proper projection identifies the restriction of the global
transform with the proper pushforward on this chart, as in §4.4.
Henselization in the source is a limit of
pointed étale neighbourhoods. The strict-local stalk comparison handles
this limit. The product of two henselizations needs this reduction to
finite-type models to use the imported finiteness theorem.
[Laumon 1987, (2.4.1)–(2.4.2.2)](https://www.numdam.org/item/PMIHES_1987__65__131_0/)

**Local transforms.** Use Définition (2.4.2.3) on `T ×_k T'` over `T'`.
With uniformizers `t,t'`, take the stalk at the pair of closed points of
`R¹Φ` of these three kernels, where `V_!` is the generic extension by zero
on `T` and the Artin–Schreier factors are extended by zero from the locus
where their arguments are defined.

| Phase | Input on the product | Argument of `Lψ` |
|---|---|---|
| `(0,∞')` | `pr₁* V_!` | `t/t'` |
| `(∞,0')` | `pr₁* V_!` | `t'/t` |
| `(∞,∞')` | Pullback of `V` on the generic source, tensored before extension by zero | `1/(tt')` |

Use the same definitions with the traits exchanged. The local–global
comparison relates the unshifted local kernels to the global kernels with
Laumon's two shifts for `K = j_!F[1]` or a lisse restriction `F[1]`.
The first use of stationary phase is to get support and concentration for
these stalks. Its second use is to identify the monodromy of the global
transform at infinity, after killing the other summands with the tame
calculation and the slope vanishing. This yields the rank and Swan formulas
in (2.5.5) and the two compositions in (2.5.6).
[Laumon 1987, (2.3.2.1), (2.3.3.1), (2.4.2.1)–(2.4.2.3), (2.5.3)–(2.5.6)](https://www.numdam.org/item/PMIHES_1987__65__131_0/)

## 2. The four bridges and the transported Swan exponent

**(b1) Monodromy over a field.** For an end trait with fraction field `K`,
choose a geometric point and identify the profinite automorphism group of
the finite étale fibre functor of `Spec K` with `G_K = Ω ≃ₐ[K] Ω` for a
separable closure `Ω`. At finite levels, the equivalence sends finite
locally constant sheaves of `Λ`-modules to continuous finite `Λ`-modules
for `G_K` and matches pullback and the stalk action. Lift it at a finite
extension of `ℚ_ℓ` using the compact matrix coefficient descent and stable
integral lattice of §3.2. Compactness supplies a common norm bound for the
finitely many coordinate functions. Use continuity in the finite field and
the open congruence kernels to obtain the continuous reduction tower.
In the arithmetic lisse category the resulting object and morphism
comparison has values in `Langlands.FiniteRepresentation` with
`Langlands.Henniart.LocalNumerical.IsLadicContinuous` (module topology on
endomorphisms) and `Langlands.Henniart.LocalNumerical.IsLadicDefinedOverFiniteExtension`.
It is exact, is compatible with tensors, and identifies positive-rank simple
isomorphism classes with `Langlands.Henniart.LocalNumerical.IrreducibleLadicClass`.
Use finite matrices to move between the external stalk universe and the
arbitrary carrier universe of the Library class. If a geometric point uses
`K^alg`, restrict its automorphisms to `K^sep` and use uniqueness of extension
across the purely inseparable remainder. Match the finite étale
stabilizers with the Krull topology by the finite Galois models. In a
finite basis, continuity of the matrix entries matches the module
topology on endomorphisms and continuity of the evaluation action on the
carrier. Compare the external invariant scalar-extension subspace with
the Library's matrix membership condition in that basis. Laumon
(2.1.2)–(2.1.2.1) specifies the finite model, continuity and fibre functor.

A Weil stalk carries the restriction of an arithmetic action to the dense
local Weil group when an arithmetic realization has been supplied. The
comparison must match the restriction to
`Langlands.Weil.Local.SepClosed.localProjection` and its inertia and degree
maps in `Langlands.Weil.Local.Assembly`. Fix the sign by requiring the
Weil generator in the residue quotient to be geometric Frobenius in both
realizations. Restriction reflects intertwining and irreducibility for
continuous Galois representations by density and closedness. For an
irreducible local Weil representation with finite inertia, the
finite-image normalization is the unramified Weil twist of §3.2. A
power of a Frobenius lift acts by a scalar after centralizing the finite
inertia image. The normalizing value may have nonzero
ℓ-adic valuation. For the original Weil representation with finite inertia,
continuous extension exists precisely when the Frobenius eigenvalues are
units. In a finite coefficient model, this gives boundedness of the
Frobenius powers in both directions and hence of the whole image. Apply
the bounded extension criterion with the residue degree comparisons in
§3.2. The local transform and its inverse will instead produce
representations directly on the whole Galois group in the arithmetic
realization. The global finite-type Weil descent result has its own
geometric fundamental group and its twist can also have nonzero valuation.
[Henniart 1988, §4.1–4.3](https://www.numdam.org/item/ASENS_1988_4_21_4_497_0/)

**(b2) Local restriction and completion.** For a smooth curve over `k`, a
closed point `z` and a lisse sheaf `F` on a dense open containing the generic
point, pull back to the punctured henselian neighbourhood `η_z^h` and apply
(b1). The stalk representation is restriction along the pointed map
`π₁(η_z^h) → π₁(U)`. Compare this local inertia action with the action from
strict localization defining the nearby cycles and with the Library's
`Langlands.LocalGalois.SepClosed.absoluteInertia` after completion. The
`j_*` boundary stalk is the inertia-fixed space, with its residual
Frobenius. Use the completed valuations on each finite henselian Galois
extension to identify residue maps and all integer lower groups, then use
the finite Herbrand functions and restrictions to identify the absolute
upper groups. The identifications preserve inertia, the residue map and
degree, and transport the Swan value. The same argument applies to the
coordinates `x,1/x,x',1/x'`, with residue `k` at the rational ends. This
uses `Langlands.AlgebraicGeometry.PointTopology.henselianFiniteEtaleEquivalence`
in `Langlands.AlgebraicGeometry.PointTopology.HenselianFiniteEtaleEquivalenceProof`
for finite étale base change. See Serre, *Local Fields*, II §3 and IV §§1, 3,
Katz 1986 (1.4.8), and Laumon (2.2.1), (2.4.2.1).

**(b3) Local term and scalar transport.** For a lisse arithmetic sheaf on a
curve, define the Swan term at `z` using the representation of (b2) and the
slope-weighted sum `s(V)` of Laumon (2.1.2.5). For a constructible complex
use signed dimensions and Swan values, including the signed stalk rank
`r_z`. The local conductor in the Euler characteristic is
`a_z = r + s_z − r_z`, weighted by the degree of the closed point over `k`.
Raynaud's formula, in the form of Laumon (2.2.1.2), is the assertion that
these are the local terms. For the stratum comparison, the planned theorem
is `LadicHasSwan X Ω ℓ ι ρ s ↔ s(V) = s` for any representative `V` of `ρ` and
all natural `s`, hence invariance under replacing `ι : E →+* ℂ`.

Use finite inertia for irreducibles and a common finite Galois presentation
of the actual inertia action, with surjective restriction from inertia.
`Langlands.Henniart.LocalNumerical.ladicWeilTransport` first restricts to the
actual Weil group and then extends scalars. For every finite ramification
subgroup, compare fixed spaces by tensoring the finite linear system defining
invariants, or its characteristic-zero averaging projector. Their dimensions
and the Herbrand weights control both the ℓ-adic slope sum and the complex
Swan sum of that presentation. Compare the two with the Artin exponent
through `Langlands.Henniart.LocalNumerical.HasArtinConductor` and
`Langlands.Henniart.LocalNumerical.HasWeilSwan` in
`Langlands.Correspondence.HenniartLocalNumerical`. The latter uses the natural
subtraction `a − d`. Include both irreducible cases. When `V^I = 0`, the
Artin exponent is `d+s(V)`. When `V^I ≠ 0`, normality and irreducibility give
`V^I = V`, so the Artin and Swan exponents vanish and natural subtraction
returns zero. Compare all presentations via common refinements, so the
existential Artin witnesses give the same value. An unramified twist fixes
the inertia action. This comparison uses scalar extension only on finite
algebraic data, with no continuity requirement on `ι`.

**(b4) Canonical extension.** Let `x` be the uniformizer at the source end
of `𝔾_m`. Restriction along `η_0^h → 𝔾_m` identifies the given continuous
finite-model `G_K`-module with the local monodromy of a functorial lisse
arithmetic sheaf on `𝔾_m` tame at `∞`. Require the construction from the
canonical retraction of the tame-at-`∞` quotient of `π₁(𝔾_m)` onto `G_K`.
Use the special-cover quotient, whose geometric finite quotients have a
unique `p`-Sylow subgroup, and use the arithmetic retraction respecting the
geometric retraction and the quotient `Gal(k̄/k)`. This gives base change,
exactness and commutation with pullback of constant twists in the same
construction. Use `1/x` for the version starting at `∞`. The finite étale
equivalence in Katz 1986, Main Theorem 1.4.1, is over the completed generic
point. Its translation to the henselian formulation of Laumon (2.2.2.2)
uses (b2). Katz (1.4.9)–(1.4.11), (1.5.3)–(1.5.6) supply the retraction and
passage to adic sheaves. [Katz 1986](https://www.numdam.org/articles/10.5802/aif.1069/)

**Unramified twists (S4).** A character in
`Langlands.Henniart.LocalNumerical.ladicUnramifiedCharacters` factors through
the residue map to `Gal(k̄/k)` and determines an arithmetic lisse line on
`Spec k`. Pull back the same line to both traits. On the strict target
chart its geometric realization is a constant free line at the finite
and rational coefficient levels, with the arithmetic action on its fibre
over `k̄`. Its dual and evaluation give the dualizability premise of the
nearby-cycles twist isomorphism in §3.3. Identify its generic restrictions
by pullback from the same base line. Apply the isomorphism and verify
that it intertwines the arithmetic actions, specialization and reductions.
On the cofiber `RΦ` it gives the same residue character on the output
stalk as on the input. The Weil
counterpart uses the Frobenius scalar obtained from the arithmetic line.
The global Fourier projection formula in §3 also compares the twists in
the stationary-phase argument. This is the tensor comparison associated with
SGA 7 XIII (2.1.1) and Laumon (2.5.2), with the locator correction for
Henniart's §4.3 in the [source map](laumon-local-fourier-source-map.md#2-laumons-theorem-and-the-locators-henniart-cites).

## 3. Pinned external inventory

All declarations in this section were checked individually with `#print axioms`
at weil-conjectures commit `a25955cde4f85f67bef3149a6efc3efe20c22132`, with
Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Every row in the **proved** tables reports the exact list
`[propext, Classical.choice, Quot.sound]`, including for definitions.
**Absent** means the needed declaration was not found in the pinned source.
The search covered definitions and results using `Swan`, `ramification`,
`Fourier`, `nearbyCycles`, `vanishingCycles`, `local acyclicity`, `Kummer`,
`Gauss`, `stationary phase`, `retraction`, `special cover` and
`Riemann–Hurwitz`, and included
reading the corresponding module families. A declaration can be usable even
when other results in its import closure have holes.

### 3.1 The seven E1b items and Laumon's dependencies

| E1b item in the external-inputs plan §4.1 | Laumon 1987 or underlying source | Pinned coverage and gap |
|---|---|---|
| 1. Local Galois, upper groups, slopes, b1–b2 | (2.1.1)–(2.1.2.6), (2.1.4)–(2.1.5), (2.2.1), (2.4.1), (2.4.2.1) | Proved field/monodromy, finite coefficient model, stable lattice, continuity, pro-`p` open-kernel, finite-type Weil descent and strict boundary ingredients below. The actual filtered completion comparison and local arithmetic-to-Weil comparison are absent as combined statements. Upper numbering, the slope decomposition, its integrality and Swan are absent in the external package. The Library supplies the upper groups and their exact images in finite Galois quotients. |
| 2. Euler–Poincaré and b3 | (2.2.1.1)–(2.2.1.2), Raynaud §§1–4 | Curve-perverse classes, compact-support operations and the curve inputs in §3.6 are proved. Riemann–Hurwitz with the different, the Artin and Swan local terms, the perverse lissity/conductor criterion and Grothendieck–Ogg–Shafarevich (GOS) are absent. |
| 3. `RΨ`, `RΦ`, proper exchange and vanishing | SGA 7 XIII (1.4.2.2), (2.1.1), (2.1.7.1), SGA 4½ *Th. finitude* Cor. 2.16, Thm. 3.2 and Prop. 3.7, Laumon (1.3.1.2), (2.3.2.1), (2.5.3.2) | Proved `RΨ`, tensor-unit specialization and arbitrary-input specialization with an identification on the geometric generic fibre. Also proved are inertia action, finite-level continuity under generation hypotheses, finite and adic constructibility, strict-trait, generic-fibre and proper exchanges, and coefficient changes under the stated pushforward hypotheses below. Specialize the imported arrow to the chosen chart complexes in §4.4 and prove equivariance and compatibility with the exchanges and coefficient maps. The equivariant `RΦ` functor, isolated-support summand for a compactifiable map, and the two relative local acyclicity results for the compactified Fourier kernel are absent. For the constant-coefficient smooth case there are proved inputs below. |
| 4. Global transform of `j_!F` | (1.2.1.1), (1.2.2.1)–(1.2.2.3), (1.2.2.9), (1.2.3.1), (1.3.1.1), (1.3.2.3)–(1.3.2.4), (1.4.1.1), (1.4.2.1), (2.3.1.1)–(2.3.1.3) | Proved ambient arithmetic Fourier functor, degree-zero kernel constructibility, and bounded constructible six-functor ingredients below. The restricted arithmetic transform, Frobenius-compatible realization and bundled Fourier-specific fibre, base-change and inversion statements remain to be built from the arithmetic operations and ambient base-change results below. The Weil transform has natural inversion, a natural derived fibre formula under its Cartesian and finite-type hypotheses, constant and punctual formulas, and curve perversity and simple-object classification. Its degreewise cohomology comparisons at the origin and other rational points give Frobenius-equivariant `E`-linear isomorphisms and hence dimension and vanishing comparisons. At the origin the shift gives the signed rank as the negative compact-support Euler characteristic for (2.3.1.1)(iii). The rank, lissity and conductor formulas in §2.3.1 still require GOS and the slope calculation. The relative forgetting-supports isomorphism of (1.3.1.1) is absent. Its consumer here is covered by curve perversity. For (1.4.2.1)(i), the direct punctual formula `(T1) → (T2')` is present, and the reverse formula `(T2) → (T1')` is obtained by reflection and Tate twist via inversion. For (1.4.2.1)(ii), the irreducible middle-extension output from a nonexceptional input is present. Nonexceptionality of the output in full generality and the combined type exchange require the exceptional-constituent identification in §4.2. The `affineFourierTransform` inversion declarations in §3.5 depend on holes. |
| 5. Three local transforms, exactness and stationary phase | (2.3.2.1), (2.3.2.3), (2.3.3.1), (2.4.2.1)–(2.4.2.3), (2.5.1)–(2.5.2) | The ambient base-change results of §3.4 and the `RΨ` inputs of §3.3 support the local–global comparison. The strict-target identification for the compactified transform, local support and degree assertions, arithmetic decomposition of the infinity stalk, local Fourier functors, exactness and finite constant-base change must be built. The exchanged inverse also needs the finite-origin phase comparison for an arbitrary localized perverse input, via the specialization triangle of SGA 7 XIII (1.4.2.2) and Laumon (1.3.1.2). |
| 6. Canonical extension and tame calculation | (1.1.3.7), (1.4.3.1)–(1.4.3.2), (2.1.2.7)–(2.1.2.8), (2.2.2.1)–(2.2.2.2), (2.5.3.1)–(2.5.3.2), Katz 1986 (1.4.1)–(1.4.6), (1.4.10), (1.5.6) | Proved Kummer torsor and strict Laurent-series tame classification, the short exact Artin–Schreier sequence with constant kernel, affine higher cohomology vanishing, the arithmetic character line with tensor and inverse formulas, and simple-pole irreducibility, translation and geometric ramification results below. The degree-one comparison for the polynomial and Laurent-series rings, pro-`p` cover comparison, two-ended tame fundamental-group comparison, canonical retraction and extension, Kummer/Gauss-sum Fourier formula and exact upper break one are absent. |
| 7. Rank, Swan, inverse, twists and class assembly | (2.4.3)(i) a)–c) and (ii) b), (2.5.4)–(2.5.6), Henniart §4.3 | Global reflection, Tate twist, lisse tensor projection and origin inversion are proved. Nearby cycles have a proved twist projection for dualizable factors and a proved compatibility of their tensor maps with pullback exchange. The local rank and Swan formulas, inverse, equivariant specialization and vanishing-cycle twist comparison, and class bijection are absent. The class assembly needs both local compositions, the separate slope inclusion, the arithmetic tensor comparison S4 and (b3). |

### 3.2 Proved monodromy and local geometry inputs

| Full declaration | Module at the pin | Scope used |
|---|---|---|
| `AlgebraicGeometry.Scheme.etaleSheafEquivDiscreteContinuousRep` | `WeilConjectures.AlgebraicGeometry.EtaleSheafDiscreteContinuousRep` | Field stalk as a discrete continuous representation on the small étale site. Use its additive equivalence and add finite module coefficients via module structures. |
| `AlgebraicGeometry.Scheme.sheafHAddEquivGaloisH` | `WeilConjectures.AlgebraicGeometry.Sites.GaloisModule` | Comparison of abelian sheaf and Galois cohomology at a separably closed point. This covers the field cohomology part of b1. |
| `AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut` | `WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction` | Action of field automorphisms on a finite étale fibre functor by precomposition with `Spec σ`. Identifying the profinite groups for `Spec K` requires the finite étale algebra dictionary. |
| `InfiniteGalois.profiniteGalGrp`, `InfiniteGalois.continuousMulEquivToLimit` | `Mathlib.FieldTheory.Galois.Profinite` | Bundled profinite Galois group of a Galois extension and its topological group equivalence with the inverse limit of finite Galois groups. Use the separable closure and compare evaluation on the finite étale covers. |
| `AlgebraicGeometry.ProEtale.LisseSheaf`, `AlgebraicGeometry.ProEtale.LisseMonodromy.StalkSpace`, `AlgebraicGeometry.ProEtale.LisseMonodromy.rep` | `WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy` | Arithmetic lisse sheaves and their monodromy actions on an `E`-linear stalk. |
| `AlgebraicGeometry.ProEtale.exists_lisseMonodromy` | `WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists` | Monodromy equivalence at algebraically closed points of a connected regular Noetherian scheme. Continuity in the interface is tested by matrix coefficients. |
| `AlgebraicGeometry.ProEtale.universalLisseMonodromy`, `AlgebraicGeometry.ProEtale.universalLisseMonodromy_isEquivalenceAt`, `AlgebraicGeometry.ProEtale.isCompatible_universalLisseMonodromy` | `WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension` | A chosen monodromy functor with the equivalence and restriction compatibility. Use with field points and the normal curves in b2. |
| `PadicAlgCl.exists_finiteDimensional_forall_mem`, `PadicAlgCl.exists_lattice_of_forall_mem` | `WeilConjectures.RepresentationTheory.IntegralModel` | The first descends entrywise continuous finite matrices of a compact topological group to one finite extension of `ℚ_ℓ`. The second takes a finite basis, such a field of coefficients and a common norm bound to give a stable free lattice spanning the representation with the prescribed rank and finite images modulo powers of the maximal ideal. |
| `Representation.IsLAdic`, `Representation.isLAdic_iff_continuous` | `WeilConjectures.RepresentationTheory.PoincareDuality.LAdic` and `WeilConjectures.RepresentationTheory.LAdicContinuous`, respectively | For a `ProfiniteGrp` acting by linear equivalences on a `PadicAlgCl ℓ`-space, the latter gives equivalence between the continuous finite scalar-extension model and finite-dimensionality with joint continuity in the module topology. Transport to the Library's endomorphism and matrix predicates in b1. |
| `exists_isOpen_forall_eq_one_of_tendsto_pow_prime_pow` | `WeilConjectures.RepresentationTheory.ProPGroupPadicMatrix` | Open kernel for a continuous representation by invertible finite matrices over `ℤ_ℓ` when every `p`-power sequence `g^(p^n)` tends to the identity and `p ≠ ℓ`. Apply on the restricted scalar lattice and use compactness of wild inertia. |
| `AlgebraicGeometry.FrobeniusBasePoint.WeilData.fundamentalRep`, `AlgebraicGeometry.FrobeniusBasePoint.WeilData.exists_equivalence_fundamentalRep` | `WeilConjectures.WeilSheaf.WeilMonodromyGeneral` | With Frobenius base-point, Weil group data and the geometric monodromy equivalence, the lisse Weil sheaf gives a Weil representation with continuity on the geometric group. A comparison to the local arithmetic realization is needed. |
| `AlgebraicGeometry.Scheme.FiniteEtale.mem_weilGroup_iff` | `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup` | Characterizes pairs in the Weil group by the action on constant covers. This is the degree normalization used in b1. |
| `AlgebraicGeometry.Scheme.FiniteEtale.eq_top_of_forall_mem_weilGroup` | `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroupDense` | Density criterion for this Weil group by the actions on finite covers. Use to check the arithmetic comparison on finite-type schemes. |
| `Representation.exists_finite_range_twist`, `Representation.exists_continuous_extension_of_isBoundedOn` | `WeilConjectures.RepresentationTheory.WeilGroupTwist` and `WeilConjectures.RepresentationTheory.WeilGroupContinuousExtension`, respectively | The first twists a finite-dimensional irreducible representation over an algebraically closed field to finite image when the degree onto `ℤ` has finite-image kernel. The second extends a bounded finite-dimensional `PadicAlgCl ℓ` representation from a dense Weil-type group to a profinite group, with continuity on the compact kernel and the specified finite-degree detection. For the local comparison supply detection by the residue quotients. |
| `Representation.exists_filtration_isIrreducible_restrict` | `WeilConjectures.RepresentationTheory.Clifford` | With a normal subgroup `P` and element `F` acting in a finite-dimensional representation over an algebraically closed field, a positive power of `F` and `P` stabilize a filtration with `P`-irreducible factors. Use to pass from the tame calculation on characters to arbitrary tame modules after finite constant-field change. |
| `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback` | `WeilConjectures.WeilSheaf.WeilDescent` | The signature takes a smooth, irreducible, **affine** scheme over the finite field. An irreducible lisse Weil sheaf is a constant twist of the pullback of an arithmetic sheaf, with an arbitrary scalar in `Eˣ`. The punctured line is the affine basic open `D(x)` of the affine line, as checked in §5. |
| `AlgebraicGeometry.WeilSheaf.exists_injective_stalk_directImage_range_eq_invariants`, `AlgebraicGeometry.WeilSheaf.exists_stalk_directImage_linearMap_invariants` | `WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants` and `WeilConjectures.WeilSheaf.BoundaryStalkSpecialization`, respectively | Boundary stalk of `j_*F` on the curve and inertia invariants in function-field monodromy. Use the strict-local point identifications to express these in terms of the inertia of the punctured trait. |
| `AlgebraicGeometry.isStrictlyHenselianLocalRing_inertiaInvariants_of_isAffineOpen`, `AlgebraicGeometry.indEtale_inertiaInvariants_of_isAffineOpen`, `AlgebraicGeometry.exists_iso_pullback_geometricFiberMap` | `WeilConjectures.WeilSheaf.BoundaryStrictHenselization` | Strictly henselian and ind-étale boundary neighbourhood from inertia invariants in an integral affine curve chart, and its generic identification with the inertia fixed field when the open is cut out by the indicated nonzero boundary parameter. These use a chosen geometric boundary point over the finite residue field and the chart and pullback hypotheses of the declarations. |
| `IsDiscreteValuationRing.mem_range_fractionRingMap_of_isSeparable` | `WeilConjectures.TraceFormula.Specialization.HenselianTraitLaurentSepClosed` | A source henselian DVR embedded in `k[[t]]` with uniformizer of order one and surjective residue map has fraction field separably closed in `k((t))`. The Library finite étale equivalence supplies essential surjectivity for b2. |
| `AlgebraicGeometry.Scheme.EtaleTorsor.kummer` | `WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor` | Finite étale torsor for an invertible section and invertible exponent with the specified roots of unity. Take a character summand to construct the Kummer line. |
| `PowerSeries.exists_pow_finrank_eq_X_and_adjoin_eq_top` | `WeilConjectures.FieldTheory.TameLaurentSeries` | Over a separably closed residue field, a finite extension of the fraction field of the power-series ring of degree `n` invertible in the residue field is generated by an `n`th root of the uniformizer. This is the strict completed local side of (2.1.1) and (2.2.2.1). |
| `LaurentSeries.irreducible_X_pow_sub_X_sub_C_single`, `LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single` | `WeilConjectures.Mathlib.RingTheory.LaurentSeries` | Irreducibility of `Uⁿ − U − c/t` for `n ≥ 2` and `c ≠ 0`. For the degree-cardinality equation with `c` in the finite field of the character, every deck translation on a root is realized by an automorphism of the algebraic closure. These provide the polynomial and translation inputs to (2.1.2.8). |
| `AlgebraicGeometry.affineLine.not_epi_upperStar_laurentPoint_artinSchreierImage` | `WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity` | At a geometric Laurent point `x = c/t` with `c ≠ 0`, the geometric Artin–Schreier line for a nontrivial character is excluded as a subquotient of a constant sheaf. The exact ramification index at which it loses invariants is the calculation in §4.1. |
| `AlgebraicGeometry.affineLine.artinSchreierSplitSection` | `WeilConjectures.WeilSheaf.ArtinSchreierInertia` | Splitting for the Artin–Schreier sheaf on sections. Its constant-stalk scope alone does not give the ramification needed in (2.1.2.8). |
| `AlgebraicGeometry.Scheme.artinSchreierSequence_shortExact`, `AlgebraicGeometry.Scheme.constantZModIsoKernelGaArtinSchreier` | `WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier` | For a prime `p` vanishing in `Γ(X,𝒪_X)`, the small étale sequence of `F−1` on `𝔾_a` is short exact with kernel the constant `ℤ/p`. Apply on the two affine schemes of Katz (1.4.5). |
| `AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine` | `WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier` | On an affine scheme with `p=0`, `H^q(X_ét,ℤ/p)=0` for `q≥2`. Also applies to every finite étale cover of such an affine scheme. |
| `AlgebraicGeometry.Scheme.subsingleton_sheafH_gaSheaf_of_isAffine` | `WeilConjectures.AlgebraicGeometry.Sites.Ga` | Small étale cohomology of `𝔾_a` in strictly positive degree vanishes on affine schemes. Use degree one in the Artin–Schreier sequence to compute the quotient of the section ring. |

### 3.3 Proved nearby cycles inputs

| Full declaration | Module at the pin | Scope used |
|---|---|---|
| `Profinite.padicAlgClRingObj` | `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` | `E` as a condensed coefficient ring. |
| `AlgebraicGeometry.trait` | `WeilConjectures.TraceFormula.Specialization.Trait` | Standard complete power-series trait. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nearbyCycles` | `WeilConjectures.SixFunctors.NearbyCycles.Basic` | Maps for the total space, geometric generic fibre, special fibre and source. The functor is `Lε* ⋙ Rj_* ⋙ Li*`. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.ofTrait`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.ofTraitHom` | `WeilConjectures.SixFunctors.NearbyCycles.StrictlyHenselianTrait` | Builds the point model from the two ring maps of a trait and a morphism of models from compatible total, generic and special ring maps. Use the strict target as the total scheme for the point case. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.traitGenericModel` | `WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal` | Standard complete trait with source its algebraically closed generic point and with the residue field as special fibre. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_unit_traitGenericModel` | `WeilConjectures.TraceFormula.Specialization.TraitChangeTrait` | Specialization of the tensor unit is invertible for the standard complete trait over a separably closed residue field. Applies to finite discrete coefficients via their condensed ring object. |
| `AlgebraicGeometry.Scheme.strictlyHenselianSections_geometricStalk_isIso` | `WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk` | On a strictly henselian local spectrum, the germ map from global sections of an abelian étale sheaf to the closed geometric stalk is a natural isomorphism. This is the sections input for the finite-coefficient strict-local stalk formula. |
| `AlgebraicGeometry.ProEtale.finiteCoefficientDerivedLowerStarIso` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar` | Derived direct image commutes with passage between condensed finite discrete coefficient modules and ordinary pro-étale modules. |
| `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'` | `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | The derived étale/pro-étale comparison for direct image of bounded below étale input along a qcqs map. Compose with the finite coefficient equivalence for the stalk formula. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.affineSpaceModel`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.geometric` | `WeilConjectures.TraceFormula.Specialization.NearbyFinitenessCases` and `WeilConjectures.TraceFormula.Specialization.TraitModelRestrict`, respectively | The relative affine-space chart and the choice of its total space as the source of `RΨ`. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.unit` | `WeilConjectures.SixFunctors.NearbyCycles.Exchange` | The tensor-unit specialization `𝟙_{X'} ⟶ Ψ_M(𝟙_X)` for source `X`, special fibre `X'` and model `M`. |
| `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`, `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarComp` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | `Lf* ⊣ Rf_*` on the condensed derived categories and the composition isomorphism for derived pullback. Apply the adjunction unit for `j` to an arbitrary total-space complex and restrict to the special fibre. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.twistSpecializationMap` | `WeilConjectures.TraceFormula.Specialization.NearbyCyclesTateTwist` | For arbitrary complexes `W` on the total space and `T` on the source and an isomorphism `a : Lε*T ≅ Lj*W`, gives `Li*W ⟶ Ψ_M(T)`. This is the special pullback of the adjunction unit at `W` followed by `Rj_*` of `a⁻¹`. The arrow uses just the generic identification. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.tensorMap` | `WeilConjectures.SixFunctors.NearbyCycles.Kunneth` | Lax tensor map `Ψ(A) ⊗ Ψ(T) ⟶ Ψ(A ⊗ T)` on the ambient nearby-cycles functor. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_whiskerLeft_twistSpecializationMap_comp_tensorMap`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nearbyCyclesTwistIso` | `WeilConjectures.TraceFormula.Specialization.NearbyCyclesTateTwist` | With `W` dualizable and `a : Lε*T ≅ Lj*W`, composing `Ψ(A) ⊗ Li*W ⟶ Ψ(A) ⊗ Ψ(T)` via specialization with the lax tensor map is invertible. The second declaration gives its inverse as the twist isomorphism `Ψ(A ⊗ T) ≅ Ψ(A) ⊗ Li*W`. |
| `AlgebraicGeometry.ProEtale.CondensedRing.isDualizable_tateTwistDerived`, `AlgebraicGeometry.ProEtale.CondensedRing.isDualizable_tateTwistDerived_of_trait` | `WeilConjectures.TraceFormula.Specialization.NearbyCyclesTateTwist` | Derived Tate lines are dualizable on schemes over a field of characteristic different from `ℓ` and on models over a standard complete trait with that residue characteristic. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.tateTwistSpecializationMap`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nearbyCyclesTateTwistIso` | `WeilConjectures.TraceFormula.Specialization.NearbyCyclesTateTwist` | Bounded constructible Tate versions of the map and isomorphism, with constructibility preservation and pullback comparisons for the Tate lines along `ε`, `j` and `i`. The isomorphism also takes the dualizability of the total-space Tate line. The arithmetic action and vanishing-cycle comparison are supplied by the general line argument in §4.5. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.pullbackExchange`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.pushforwardExchange`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isIso` | `WeilConjectures.SixFunctors.NearbyCycles.Exchange` | The exchange maps on arbitrary inputs. The pullback map is invertible for isomorphic total and generic maps. Use this for arithmetic automorphisms, including those acting on the special fibre. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.map_unit_comp_pullbackExchange_app` | `WeilConjectures.SixFunctors.NearbyCycles.Exchange` | Coherence of tensor-unit specialization with pullback exchange. Applies also to a model automorphism over a residue automorphism, and verifies the constant-input check. |
| `separableClosure.isPurelyInseparable` | `Mathlib.FieldTheory.PurelyInseparable.Basic` | An algebraic extension is purely inseparable over its separable subclosure. Apply inside the algebraic closure of the fraction field. |
| `Algebra.IsUniversalHomeomorphism.of_isPurelyInseparable`, `Algebra.IsUniversalHomeomorphism.isUniversalHomeomorphism` | `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra` | The spectrum map of a purely inseparable extension of fields is a universal homeomorphism, a property stable under base change. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isUniversalHomeomorphism_generic` | `WeilConjectures.SixFunctors.NearbyCycles.UniversalHomeomorphismExchange` | With the source, total and special spaces fixed and `j_a = g ≫ j_s`, `ε_a = g ≫ ε_s`, gives invertible pullback exchange from the `s` model to the `a` model for a universal homeomorphism `g` of the generic fibres. Applies to condensed commutative coefficient rings. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.pullbackExchange_app_of_total_eq_id` | `WeilConjectures.SixFunctors.NearbyCycles.ExchangeGenericUnit` | For this shape of model map over identities, the exchange on any input is given by `Li* Rj_{s,*}` of the unit for `g`, with the composition comparisons. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.pullbackExchange_square` | `WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence` | The two composite exchanges for a commutative square of model maps agree under the pullback identifications. It applies to maps over a residue automorphism and to strict-trait and generic-layer comparisons. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app` | `WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence` | Pullback exchange respects the lax tensor maps via the tensor comparisons for the source and special pullbacks. Applies to the full model automorphisms with their residue maps. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.galoisLayer`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.galoisLayerExchangeIso` | `WeilConjectures.SixFunctors.NearbyCycles.GaloisLayer` | Extends the model's generic field on a fixed special fibre. Identifies nearby cycles of a Galois layer with pushforward along the generic layer map followed by the original specialization operations. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.galoisLayerAction`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.galoisLayerAction_mul`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction` | `WeilConjectures.SixFunctors.NearbyCycles.GaloisAction` | Action, multiplication and exchange compatibility over the fixed special fibre. In the geometric special-fibre model this supplies the inertia action. Galois elements acting on the residue field must also act on the special fibre. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.exists_forall_homology_galoisLayerAction_eq_id`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.exists_forall_homology_galoisLayerAction_eq_id_of_isGenerated` | `WeilConjectures.SixFunctors.NearbyCycles.GaloisContinuityNoetherian` and `WeilConjectures.SixFunctors.NearbyCycles.GaloisContinuityGenerated`, respectively | For a finite discrete coefficient ring, qcqs generic inclusion, and bounded below generic restriction of étale origin, an open subgroup of the Galois layer fixes a given cohomology object. The first requires that object to be noetherian. The second takes generation by finitely many finitely presentable objects and is the form used with the finiteness and generation inputs below. |
| `AlgebraicGeometry.ProEtale.exists_complex_of_plusEtaleOrigin`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nonempty_isColimit_homology_nearbyCycles_galoisTower` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginComplex` and `WeilConjectures.SixFunctors.NearbyCycles.GaloisContinuity`, respectively | A bounded below finite-coefficient complex of étale origin has a representative with terms of étale origin. For such a representative on the generic site and qcqs generic inclusion, nearby cohomology is computed by the filtered colimit over finite Galois layers. Use the layer comparison and action on the arrows to apply this to specialization cones. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_of_weaklyEtale` | `WeilConjectures.SixFunctors.NearbyCycles.OpenExchange` | Weakly étale change of the total space with Cartesian square `IsPullback φ.generic M.j N.j φ.total`. Use for source-side pointed neighbourhoods over a common strict target and the same geometric generic point, so the square is Cartesian by construction. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait` | `WeilConjectures.SixFunctors.NearbyCycles.TraitChange` | `E`-coefficients with bounded constructible geometric generic restriction. Unramified strict henselian DVR inclusion, algebraically closed generic fields algebraic over the respective DVRs, separated finite-type model before base change. |
| `AlgebraicGeometry.ProEtale.CondensedRing.isIso_pullbackExchange_app_of_isPullback_trait_finite` | `WeilConjectures.SixFunctors.NearbyCycles.TraitChangeFiniteCoefficient` | Direct finite-coefficient exchange for an unramified inclusion of strictly henselian DVRs and a separated finite-type source model, with the stated Cartesian squares, compatible algebraically closed generic fields algebraic over the DVRs, invertible residue characteristic, and bounded below generic restriction of étale origin. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_of_inertia` | `WeilConjectures.SixFunctors.NearbyCycles.GaloisTraitChangeTorsion` | Reduces exchange for the torsion étale-origin input to an already invertible exchange `hβ` on the compared Galois layers. It requires the indicated compatible towers, qcqs generic inclusion, invertibility of the degrees of the finite Galois subextensions of the wild layers in the coefficient ring, surjectivity on inertia and injectivity on the tame quotients. The route in §4.4 uses the direct strict-trait exchange under its geometric hypotheses. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient` | `WeilConjectures.SixFunctors.NearbyCycles.ProperExchangeFinite` | Finite-coefficient proper exchange on bounded below étale-origin input. The total and source maps are proper, the special square and the square of `ε` are Cartesian, and the source `j` is qcqs. Use for charts over the same strict target. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_of_isNoetherian` | `WeilConjectures.TraceFormula.Specialization.NearbyProperExchangeNoetherian` | The `E`-coefficient comparison for bounded constructible input, with Noetherian, closed-special-fibre and affine-generic-inclusion conditions, a standard target trait model, and the same properness and Cartesian square requirements. Use on the complete strict models. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel` | `WeilConjectures.TraceFormula.Specialization.NearbyFiniteness` | Finiteness for a finite-type model of a standard complete strictly henselian trait. The second theorem needs the generic identification to factor through the total space. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj_of_finite`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel_of_finite` | `WeilConjectures.TraceFormula.Specialization.NearbyFinitenessTorsionModels` | SGA 4½ *Th. finitude* Thm. 3.2 for `T` a finite discrete commutative coefficient ring, `k'` separably closed, `p` prime with `p ∣ m` whenever `m` vanishes in `k'`, `p` a unit in `T`, and the exponent of `T` invertible on `Spec k'`. On a finite-type standard model over `k'[[t]]`, the first takes a bounded constructible input on the total space and yields a bounded constructible output on the special fibre for geometric `RΨ`. The second takes a model in which the generic map factors through the total space. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModel.quasiCompact_j`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModel.quasiSeparated_j` | `WeilConjectures.TraceFormula.Specialization.NearbyFinitenessTorsionModels` | The generic inclusion of a finite-type standard trait model is qcqs, by its base-change square. |
| `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_iff_of_finite`, `AlgebraicGeometry.ProEtale.CondensedRing.isGeneratedByFinitelyPresentable_homology_of_boundedConstructible` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.BoundedConstructibleFinite` and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleGenerated`, respectively | With finite discrete coefficients, bounded constructibility implies the required étale origin. On a qcqs scheme it gives generation of cohomology sheaves by finitely many finitely presentable objects. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOver.isIso_boundedConstructibleUnit_of_smooth` | `WeilConjectures.TraceFormula.Specialization.NearbySmoothUnit` | Smooth specialization of the unit in the standard trait setting. |
| `AlgebraicGeometry.Etale.smooth_localAcyclicity`, `AlgebraicGeometry.Etale.IsUniversallyLocallyAcyclic` | `WeilConjectures.AlgebraicGeometry.Smooth.SmoothLocalAcyclicity` and `WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf`, respectively | Smooth local acyclicity for constant invertible torsion coefficients. The variant with the Fourier kernel and nonconstant input is new. |
| `AlgebraicGeometry.ProEtale.CondensedRing.exists_distTriang_openClosed_derived` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedTriangle` | The ambient derived open–closed triangle for complementary open and closed immersions. Use its open-extension identification when the special restriction of the specialization cone is zero. |

#### Integral and rational coefficient comparisons for nearby cycles

| Full declaration | Module at the pin | Scope used |
|---|---|---|
| `PadicAlgCl.finite_integersModPow`, `Profinite.integersModPowRingObj`, `Profinite.padicIntegersRingObjToIntegersModPow` | `WeilConjectures.CategoryTheory.RingObjects.Condensed.IntegersModPow` | Finiteness of `𝒪_L/ℓⁿ` for a finite coefficient field `L`, the associated condensed ring and the reduction map from `𝒪_L`. |
| `Profinite.padicIntegersRingObjToResidueField`, `AlgebraicGeometry.ProEtale.padicIntegersRingObjToContinuousMapRingObj`, `Profinite.padicSubfieldRingObjToPadicAlgCl` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Reduction`, `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` and `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`, respectively | Coefficient maps to the residue field `𝔽_L`, to the finite ℓ-adic extension `L`, and from `L` to `E`. The first is the reduction used in the integral constructibility criterion. |
| `AlgebraicGeometry.ProEtale.CondensedRing.exists_derivedCompleteIntegers_iso_integralModel` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.IntegralModelAmbient` | On a noetherian scheme, a bounded constructible `E`-complex admits a derived complete bounded constructible model over `𝒪_L` for some finite `L`, with an isomorphism after the two scalar extensions. This is existence for objects. The kernel, specialization maps and group actions need compatible models in §4.4. |
| `AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalars_integersModPowReduction`, `AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalars_residueField` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible` and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible`, respectively | The finite reductions of bounded constructible integral complexes are bounded constructible on the stated noetherian schemes. |
| `AlgebraicGeometry.ProEtale.CondensedRing.derivedLowerStarIntegersModPowReduction`, `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedLowerStarIntegersModPowReduction` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionTriangleNatural` and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionPullCompatible`, respectively | The canonical comparison for `Rf_*` and derived reduction modulo `ℓⁿ` is invertible for every scheme morphism. Apply it to the actual generic inclusion `j`. |
| `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom`, `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_residueField_app` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCube` and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal`, respectively | The pushforward comparison for derived coefficient change using the pullback mate, with invertibility for `𝒪_L → 𝔽_L` on bounded below input along any scheme morphism. |
| `AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom`, `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_app_padicIntegers_of_isGE`, `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`, `WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso` and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite`, respectively | The scalar comparison for `Rf_*`. For a qcqs scheme morphism and bounded below input it is invertible for `𝒪_L → L` and `L → E`. |
| `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso`, `AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionShriekIso` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull` and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`, respectively | Derived coefficient change for pullback and for extension by zero along an open immersion. |
| `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nearbyCyclesExtendScalarsIso`, `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.upperStarUpperStarNearbyCyclesLowerShriekExtendScalarsIso` | `WeilConjectures.SixFunctors.NearbyCycles.ExtendScalars` | `RΨ` commutes with derived scalar extension at an input when the supplied `Rj_*` comparison is invertible at its geometric generic restriction. The second applies the resulting comparison to an open extension by zero followed by special-fibre restrictions. Specialization and Galois compatibility are the comparison obligations in §4.4. |
| `AlgebraicGeometry.ProEtale.derivedCompleteIntegers_leftDerivedUpperStar_obj`, `AlgebraicGeometry.ProEtale.derivedCompleteIntegers_rightDerivedLowerStar_obj` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Basic` | Derived pullback between qcqs schemes and derived pushforward preserve derived completeness for the indicated integral coefficients. |
| `AlgebraicGeometry.ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_residueField` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegralCriterionResidue` | A derived complete integral complex is bounded constructible on a noetherian scheme if its first derived reduction to `𝔽_L` is bounded constructible. |
| `AlgebraicGeometry.ProEtale.isHomotopyLimit_canonicalReductionTowerCone` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms` | A derived complete `𝒪_L`-complex is a homotopy limit of its scalar-restricted reductions modulo `ℓⁿ` with the canonical transitions and units. |
| `AlgebraicGeometry.ProEtale.isEquivalence_mapMod_upperStarFromPoint`, `AlgebraicGeometry.ProEtale.geometricStalkComparisonIso` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint` and `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.GeometricStalk`, respectively | At a separably closed field the first identifies modules on its pro-étale site with condensed coefficient modules. The second identifies the pro-étale geometric stalk defined using the site comparison with the étale derived stalk of a bounded below input of étale origin. Use to match finite reductions at the point. |

### 3.4 Proved global Fourier inputs

#### Arithmetic condensed model

| Full declaration | Module at the pin | Scope used |
|---|---|---|
| `Profinite.PadicAlgCl.constRingHom`, `Profinite.PadicAlgCl.constRingHom_surjective` | `WeilConjectures.CategoryTheory.RingObjects.GlobalSections` and `WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections`, respectively | Constant global sections of `Λ = Profinite.padicAlgClRingObj ℓ`. Postcompose `ψ : AddChar k E` with the multiplicative map of the injective constant-section ring hom. The result is the required nontrivial `AddChar k (MonObj.Γ Λ)`. |
| `Profinite.continuousMapConstRingHom` | `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections` | Constant global sections for a finite ℓ-adic coefficient field. |
| `AlgebraicGeometry.ProEtale.condensedArtinSchreierPushforward`, `AlgebraicGeometry.ProEtale.condensedArtinSchreierTranslationAction`, `AlgebraicGeometry.ProEtale.condensedArtinSchreierProjector`, `AlgebraicGeometry.ProEtale.condensedArtinSchreierSheaf`, `AlgebraicGeometry.ProEtale.condensedArtinSchreierSheafOf` | `WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier` | Pushforward of the coefficient module along `u ↦ u^q − u`, pullback action of deck translations, arithmetic projector with weights `q⁻¹ψ(−a)`, its image, and pullback by a global function on a `k`-scheme. This supplies the actual arithmetic line used in both local and global kernels. |
| `AlgebraicGeometry.ProEtale.condensedArtinSchreierProjector_evaluation` | `WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierProjectorFacts` | Over the Artin–Schreier cover, evaluation on the identity sheet identifies the character image with the coefficient module when `q` is invertible. |
| `AlgebraicGeometry.ProEtale.condensedArtinSchreierSheafOf_lisse_tensor_inv` | `WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierLisse` | Lissity with local rank-one model and the tensor addition, negative-function and inverse-character isomorphisms for nontrivial `ψ` and `ℓ ≠ p`. The signature provides existence for the tensor and inverse maps. |
| `AlgebraicGeometry.ProEtale.nonempty_iso_condensedArtinSchreierSheafOf_derivedPullback` | `WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierPullback` | Derived pullback of the degree-zero character image is isomorphic to the degree-zero character image for the pulled-back function over the same character field. |
| `AlgebraicGeometry.ProEtale.condensed_fourier_kernel_coefficient_comparison` | `WeilConjectures.AlgebraicGeometry.CondensedFourierKernelCoefficientComparison` | Extends the character line from a finite intermediate field of `PadicAlgCl ℓ` via its condensed coefficient map, identifying the line for the induced global-section character. This comparison is for the ordinary kernel module. |
| `AlgebraicGeometry.ProEtale.condensedFourierKernel` | `WeilConjectures.AlgebraicGeometry.CondensedFourierKernel` | Uses the arithmetic character line of the pairing on the actual product. |
| `AlgebraicGeometry.ProEtale.condensedFourierTransform`, `AlgebraicGeometry.ProEtale.condensedAffineFourierTransform`, `AlgebraicGeometry.ProEtale.condensedFieldFourierTransform` | `WeilConjectures.AlgebraicGeometry.CondensedFourierTransform` | Ambient derived functor given by derived pullback, tensor by the degree-zero kernel, compact support for the supplied compactification of the second projection, and the shift. The specializations use the standard pairing and shift by the dimension and, for `PUnit`, give the affine-line formula with `[1]`. |
| `AlgebraicGeometry.affineTraceLineCompactification` | `WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower` | Standard affine chart of the projective line over the target. Transport it to the actual second projection using the pullback description of relative affine space. |
| `AlgebraicGeometry.AffineSpace.isPullback_map`, `AlgebraicGeometry.Compactification.precomp`, `AlgebraicGeometry.Compactification.copy`, `AlgebraicGeometry.Compactification.ofIsOpenImmersion` | `Mathlib.AlgebraicGeometry.AffineSpace` for the first. `WeilConjectures.Compactification.Defs` for the others. | The affine-space base-change square and transport of a compactification by the resulting source isomorphism and equality of composites. The last gives the factorization of an open immersion with proper part the identity. |
| `AlgebraicGeometry.ProEtale.CondensedRing.condensedFourierKernel_boundedConstructible` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFourierKernelBounded` | Bounded constructibility of the degree-zero kernel for the stated admissible coefficients and separated finite-type schemes over a finite or algebraically closed field. |
| `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar`, `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarCompatibility`, `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriek`, `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleTensor`, `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleTensorObjCompatibility` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | Bounded constructible pullback and its ambient comparison, extension by zero and the ℓ-adic tensor. The tensor comparison fixes the left factor. Use the symmetry to compare with the ambient right tensor. |
| `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek` | Ambient compact-support functor for the supplied compactification. For the identity proper part of an open immersion, its bounded constructible restriction identifies with extension by zero. |
| `AlgebraicGeometry.Scheme.strictLocalizationToBase` | `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization` | The morphism from the strict localization at a chosen geometric point to the ambient scheme. |
| `AlgebraicGeometry.Scheme.weaklyEtale_strictLocalizationToBase` | `WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationWeaklyEtale` | Over an affine target this morphism is weakly étale. At infinity use an affine chart followed by its open immersion into the projective target. |
| `AlgebraicGeometry.ProEtale.CondensedRing.pullbackSquareComparison`, `AlgebraicGeometry.ProEtale.CondensedRing.baseChangeMap` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing` | The composition comparison of derived pullbacks for a commutative square and its adjunction mate `Lg* Rp_* ⟶ Rp'_* Lg'^*`. Use this canonical map before applying nearby cycles. |
| `AlgebraicGeometry.ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale` | For a Cartesian square with `g` and its pullback `g'` weakly étale, the ambient derived base-change map for `Rp_*` is invertible on all complexes over the condensed commutative coefficient ring. Use for the proper projection restricted to a strict target trait and to the affine target open. |
| `AlgebraicGeometry.ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase` | For `p` proper in a Cartesian square, both bases Noetherian schemes over fields with `ℓ` invertible, the ambient `E`-coefficient base-change map is invertible on bounded constructible input. Use at the closed target boundary to check zero special restriction of the compactified pushforward. |
| `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification`, `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility`, `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriek` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar` | Compact support on bounded constructible ℓ-adic complexes for separated finite-type schemes over the field. The first two take the explicit compactification and compare with the ambient functor. The last uses the chosen compactification. |
| `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl`, `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence` and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriekIso`, respectively | Comparison of compactifications by common refinement and the bounded constructible extension by zero identification for an open immersion. |
| `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionPadicAlgCl` | Compact-support composition for bounded constructible ℓ-adic complexes on separated finite-type schemes. Use in kernel convolution. |
| `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism`, `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleExceptionalProjectionMorphism` | `WeilConjectures.PoincareDuality.ProjectionFormula` | Projection morphism and invertibility for arithmetic compact support with bounded constructible ℓ-adic factors. Use for kernel convolution and the globally pulled-back twist. |
| `AlgebraicGeometry.ProEtale.CondensedRing.trace` | `WeilConjectures.PoincareDuality.Poincare` | Arithmetic smooth trace on the twisted and shifted coefficient unit for a smooth morphism of the specified pure relative dimension. Its rank-one affine-line normalization is used in the arithmetic convolution calculation. |
| `AlgebraicGeometry.ProEtale.CondensedRing.exists_distTriang_openClosed_boundedConstructible`, `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero` | `WeilConjectures.TraceFormula.OpenClosedTriangle` and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward`, respectively | Arithmetic localization on finite-type bounded constructible complexes and invertibility of the ambient closed adjunction unit when the complementary open pullback is zero. Use to identify the convolution with the pushforward from its closed support by the adjunction unit. |

#### Weil model and comparison

| Full declaration | Module at the pin | Scope used |
|---|---|---|
| `AlgebraicGeometry.affineLine` | `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace` | The line indexed by `PUnit` over the specified base field. |
| `AlgebraicGeometry.WeilSheaf`, `AlgebraicGeometry.WeilComplex`, `AlgebraicGeometry.WeilSheaf.IsLisse`, `AlgebraicGeometry.WeilSheaf.toComplex`, `AlgebraicGeometry.WeilComplex.upperStar` | `WeilConjectures.WeilSheaf.Category` | Constructible sheaves and bounded constructible complexes with Weil structure, lissity, degree-zero complex and pullback. |
| `AlgebraicGeometry.WeilSheaf.extensionByZero`, `AlgebraicGeometry.WeilSheaf.subsingleton_stalk_extensionByZero` | `WeilConjectures.WeilSheaf.OpenImmersion` and `WeilConjectures.WeilSheaf.StalkExtensionByZero`, respectively | Quasi-compact open immersion and stalk vanishing on the boundary. |
| `AlgebraicGeometry.WeilComplex.derivedLowerShriek` | `WeilConjectures.WeilSheaf.LowerShriek` | Compactly supported pushforward on bounded constructible Weil complexes, with the finiteness hypotheses of that module. |
| `AlgebraicGeometry.WeilSheaf.artinSchreierIdempotent`, `AlgebraicGeometry.artinSchreier`, `AlgebraicGeometry.fourierKernel`, `AlgebraicGeometry.fourierTransform` | `WeilConjectures.WeilSheaf.Fourier` | Character projector on the geometric finite cover with Weil structure, its Artin–Schreier line, lisse pairing kernel and actual shifted Weil Fourier transform. The codomain supplies bounded constructibility. |
| `AlgebraicGeometry.artinSchreierOf` | `WeilConjectures.WeilSheaf.FourierInversion.Defs` | Pulls the kernel line back by a function, for chart and fibre comparisons. |
| `AlgebraicGeometry.nonempty_iso_fourierTransform_comp_inv` | `WeilConjectures.WeilSheaf.FourierInversion` | Natural opposite-character inversion for `ψ ≠ 1`, with Tate twist and shifts. |
| `AlgebraicGeometry.affineLine.neg`, `AlgebraicGeometry.nonempty_iso_fourierTransform_comp_self` | `WeilConjectures.WeilSheaf.FourierInversion.Reflection` | Actual same-character natural inversion with reflection and Tate twist. This is the formula used in (2.5.5) and (2.5.6). |
| `AlgebraicGeometry.nonempty_iso_kernelConvolution_fourierKernel` | `WeilConjectures.WeilSheaf.FourierInversion.ConvolutionKernel` | The Weil same-character convolution is the constant line on the antidiagonal, extended by zero with twist `(-1)` and shift `[-2]`. Its arithmetic counterpart uses the finite-type exchange and arithmetic projection results above. |
| `AlgebraicGeometry.WeilComplex.tateTwist` | `WeilConjectures.WeilSheaf.TateTwist` | Global Tate twist. Compare the twist at a local stalk with the residue character and preserve the slope data. |
| `AlgebraicGeometry.nonempty_iso_fourierTransform_comp_upperStar` | `WeilConjectures.WeilSheaf.FourierStalkFibre` | Existence of a natural isomorphism on derived Weil complexes for pullback of the transform along the supplied Cartesian target square. The right side pulls back the input, tensors by the pulled-back kernel, and applies compactly supported pushforward and `[1]`. The separatedness, quasi-compactness and finite-type premises are those of the fibre square. |
| `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_baseChange` | `WeilConjectures.FourierTransform.Properties.BaseChange` | Small-étale finite-coefficient kernel transform under a cartesian base change with the declared hypotheses. Usable on torsion levels with the model comparison. |
| `AlgebraicGeometry.nonempty_iso_fourierTransform_obj_adicConstant`, `AlgebraicGeometry.nonempty_iso_fourierTransform_obj_delta` | `WeilConjectures.WeilSheaf.FourierFirstFormula` | The constant and punctual formulas of (1.2.3.1). The constant formula has `ψ ≠ 1`. |
| `AlgebraicGeometry.WeilComplex.IsCurvePerverse`, `AlgebraicGeometry.WeilComplex.isCurvePerverse_shift_one_toComplex`, `AlgebraicGeometry.isCurvePerverse_fourierTransform_obj_iff`, `AlgebraicGeometry.simple_fourierTransform_obj`, `AlgebraicGeometry.WeilComplex.simple_iff` | `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | Curve-perverse conditions, a criterion for `j_!F[1]` after ruling out punctual subsheaves, preservation by Fourier and the simple-object classification on the line. These cover the curve case of (1.3.2.3)–(1.3.2.4) and the classification used in (1.4.2). |
| `AlgebraicGeometry.WeilSheaf.nonempty_iso_fourierTransform_derivedLowerShriek_of_isPullback`, `AlgebraicGeometry.WeilSheaf.nonempty_iso_fourierTransform_toComplex_of_isPullback` | `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | The first gives the forward formula of (1.4.2.1)(i) for an input `i_!E` where `i` is a closed immersion and its product with the target has finite projection `π`. The output is `π_*((i×id)*Lψ(xx') ⊗ q*E)[1]` with `q` the projection to `Z`. The second applies the formula to a sheaf vanishing on the open complement. Specialize to a single closed point for `(T1) → (T2')`. |
| `AlgebraicGeometry.WeilSheaf.exists_isLisse_iso_fourierTransform_of_isZero_upperStar` | `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | Punctual correction transforms to a shifted lisse sheaf. This can be used for boundary pieces of type (1.4.2.1). |
| `AlgebraicGeometry.WeilSheaf.exists_iso_carrier_lowerStar_tensorObj_fourierKernel_inv` | `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | Under the finite reduced support and product hypotheses, the inverse-kernel punctual formula splits geometrically as the sum of linear Artin–Schreier lines for the geometric points, with multiplicities. |
| `AlgebraicGeometry.WeilSheaf.IsNonexceptional`, `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.IsFourierPartner`, `AlgebraicGeometry.exists_middleExtension_fourierTransform`, `AlgebraicGeometry.isNonexceptional_of_isUnramifiedAtInfinity` | `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | The hypothesis of the middle-extension theorem is `ψ ≠ 1` and a dense-open irreducible lisse Weil input with no geometric linear Artin–Schreier constituent for any `a ∈ k̄`, including zero. The output is an irreducible lisse Weil sheaf on a dense open with an isomorphism of its shifted middle extension to the Fourier transform. The separate unramified-at-infinity test gives nonexceptionality for an irreducible lisse input that is geometrically nonconstant and extends lisse at infinity. |
| `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isEmpty_iso_linearCharacter` | `WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters` | Linear Artin–Schreier lines for distinct parameters in `k̄` are pairwise nonisomorphic on the dense geometric open for `ψ ≠ 1`. Use for the Frobenius orbit of an exceptional constituent. |
| `AlgebraicGeometry.WeilSheaf.isZero_higherLowerShriek_fourierKernelTensor` | `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | Relative transform concentrated in degree one **given** that the Fourier transform of that sheaf is a degree-zero sheaf. The lissity and concentration for Laumon's specific open must come from the local conductor calculation. |
| `AlgebraicGeometry.nonempty_equiv_stalk_homologySheaf_fourierTransform_origin` | `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | Existence of a Frobenius-equivariant `E`-linear isomorphism from the degree-`r` stalk of the Weil transform at the rational origin to `H_c^(r+1)(Ā,K)`. It gives both the degreewise dimensions used in (2.3.1.1)(iii) and the degreewise vanishing comparison there. |
| `AlgebraicGeometry.nonempty_equiv_stalk_homologySheaf_fourierTransform_rationalPoint` | `WeilConjectures.WeilSheaf.FourierStalk` | The corresponding degreewise Frobenius-module isomorphism at a rational `a`, with compact-support cohomology of `K ⊗ Lψ(ax)` in degree `r+1`. Use at finite closed points after passage to their residue fields. |
| `FrobeniusModule.Equiv.toLinearEquiv`, `FrobeniusModule.Equiv.map_frobenius` | `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule` | Projections to the underlying linear isomorphism and the equation intertwining the two Frobenius automorphisms. The linear isomorphism preserves dimension in each degree. |
| `AlgebraicGeometry.WeilSheaf.constantTwist` | `WeilConjectures.WeilSheaf.Tensor` | Multiply the Frobenius structure by a scalar. An arbitrary Weil scalar need not come from a continuous Galois character. |
| `AlgebraicGeometry.nonempty_iso_tensorLisse_upperStar_comp_fourierTransform` | `WeilConjectures.WeilSheaf.FourierBaseLinear` | Natural global Fourier projection formula for a lisse Weil sheaf pulled back from `Spec k`. |
| `AlgebraicGeometry.WeilComplex.derivedLowerShriekCompTensorLisseIso` | `WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerShriek` | Compact-support projection formula for a lisse factor. The local projection comparison uses `Rj̄_*` and specialization as in §2. |
| `AlgebraicGeometry.WeilSheaf.geometricFiberPullback` | `WeilConjectures.WeilSheaf.GeometricFiberPullback` | Weil realization of a constructible arithmetic sheaf, by geometric pullback with its canonical Frobenius. |
| `AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` | `WeilConjectures.WeilSheaf.CondensedModelWeil` | Comparison to the geometric condensed Weil model. |
| `AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackCompToCondensedIso` | `WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback` | Compatibility of the arithmetic geometric pullback with the condensed model, including Weil structure. |
| `AlgebraicGeometry.ProEtaleWeilSheaf.derivedEquivCondensed`, `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarCompToCondensedIso`, `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroCompToCondensedIso`, `AlgebraicGeometry.WeilComplex.derivedLowerShriekCompToCondensedIso` | `WeilConjectures.WeilSheaf.CondensedModelWeilDerived` | Derived equivalence and comparison for pullback, open extension and compact support. The last uses the same compactification on both sides. |
| `AlgebraicGeometry.ProEtale.adicSheafEquivCondensedModTensorIso` | `WeilConjectures.WeilSheaf.Native.NativeCondensedModelTensor` | Tensor comparison on adic sheaves. For the Fourier kernel use exact tensor by a lisse line and the degree-zero and derived identifications. |
| `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationGeometricFiberWeilIso`, `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekGeometricFiberWeilIso` | `WeilConjectures.WeilSheaf.CondensedModelBoundedConstructible` | Frobenius-compatible geometric fibre comparison for the arithmetic `Rf_!`, first for the supplied compactification and then for the chosen one. Compose with the model comparisons to relate the arithmetic Fourier functor to the Weil transform. |
| `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekCompToPoint` | `WeilConjectures.TraceFormula.CompactPullback` | Compact support to the base point after compactly supported direct image. This is part of the cohomology input for GOS and the fibre formula. |
| `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl`, `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs` and `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported`, respectively | The arithmetic compact-support exchange morphism and its invertibility for Cartesian squares of separated finite-type schemes over a single field. Use for closed-point and convolution squares. Pullback from a finite field to its algebraic closure uses the specialized geometric-fibre comparison above. |
| `AlgebraicGeometry.ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_sum_localTerm` | `WeilConjectures.TraceFormula.LefschetzVerdier` | Proper fixed-point localization of a trace for a decomposed proper fixed locus. Raynaud's GOS proof still needs the identification of the local term of a curve automorphism with its intersection multiplicity. |

### 3.5 Inversion declarations depending on holes

Each row reports `[propext, sorryAx, Classical.choice, Quot.sound]`. Use the
same-character Weil inversion from §3.4 for the proof. The finite-level
arguments can use the proved coefficient and exchange results without
taking torsion inversion as an input.

| Full declaration | Module at the pin | Declaration carrying the `sorry` |
|---|---|---|
| `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_inv`, `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_comp_self` | `WeilConjectures.FourierTransform.Inversion` | `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace` in `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace`, traced with `#print sorries`. |
| `AlgebraicGeometry.WeilComplex.nonempty_iso_affineFourierTransform_comp_inv` | `WeilConjectures.WeilSheaf.WeilFourierInversion` | The same declaration, in its own body. |
| `AlgebraicGeometry.WeilComplex.nonempty_iso_affineFourierTransform_comp_self` | `WeilConjectures.WeilSheaf.WeilFourierInversion` | The same declaration, in its own body. |

### 3.6 Proved curve degree and cohomology inputs

| Full declaration | Module at the pin | Scope used |
|---|---|---|
| `AlgebraicGeometry.Scheme.arithmeticGenus_pullback` | `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` | Invariance of `dim H¹(𝒪)` under extension of the ground field on a qcqs scheme. |
| `AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`, `AlgebraicGeometry.Scheme.degree_relativeDifferentials`, `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_degree_add` | `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` | The two genera agree on a smooth proper curve. With `H⁰(𝒪)=k`, the degree of `Ω¹` is `2g−2` and Riemann–Roch gives `χ(L)=deg L+1−g` for a line bundle. |
| `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_isAlgClosed` | `WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective` | Supplies `H⁰(𝒪)=k` for a proper, reduced, connected, nonempty scheme over an algebraically closed field. |
| `AlgebraicGeometry.Scheme.Hom.ramificationIndex`, `AlgebraicGeometry.Scheme.Divisor.pullback`, `AlgebraicGeometry.Scheme.Divisor.degree_pullback_eq_finrank_functionField_mul` | `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback` | The uniformizer valuation and pullback of a divisor along a finite map. For finite flat maps of smooth proper integral curves over an algebraically closed field the degree scales by the function-field degree. |
| `AlgebraicGeometry.Scheme.Divisor.degree_dual_toModules_idealSheaf` | `WeilConjectures.AlgebraicGeometry.Curve.DivisorDegree` | Identifies the degree of the line bundle of an effective divisor on a smooth proper curve with the sum of its multiplicities weighted by the residue degrees. |
| `AlgebraicGeometry.Scheme.picDegreeHom_toPic` | `WeilConjectures.AlgebraicGeometry.Curve.Picard` | Identifies the divisor degree with the degree of the associated line bundle on a smooth proper curve over an algebraically closed field. Use for the canonical divisors, whose coefficients may be negative. |
| `AlgebraicGeometry.ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero` | `WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero` | The projective line over an algebraically closed field has genus zero. Use the comparison of the two genera above. |
| `AlgebraicGeometry.IsConnectedCurve.sheafH_rootsOfUnitySheaf_canonical_of_isProper` | `WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityCohomology` | For a smooth proper connected curve over an algebraically closed field and invertible `n`, the sizes of `H⁰`, `H¹`, `H²` of `μ_n` are `n`, `n^(2g)`, `n`, and higher cohomology vanishes. Use `n=ℓ` and a primitive root of unity for the geometric constant-coefficient Euler characteristic. |
| `AlgebraicGeometry.ProEtale.bijective_cohomologyComparison` | `WeilConjectures.AlgebraicGeometry.ProEtale.EtaleCohomologyComparison` | Étale cohomology of an abelian sheaf agrees with pro-étale cohomology of its comparison pullback. Use with the constant finite coefficients in the geometric curve calculation. |
| `AlgebraicGeometry.ProEtale.finiteCoefficientDerivedEquivalence` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived` | Derived equivalence between condensed finite discrete coefficient modules and ordinary pro-étale modules. Identify the constant unit in this comparison for the finite-level Euler characteristic. |

## 4. Definitions, statements and proof dependencies

Proposed module names below are relative to `Langlands.Correspondence.Laumon`.
Proposed declarations are in `Langlands.Henniart.Laumon` unless a full name is
shown. Entries marked **new** give the definition or proposition to formulate
and, for a proposition, the inputs for its proof. They can be developed in the
order shown, with the algebraic completion and slope work independent of the
geometric comparison of Fourier operations. The **import** entries consume
§3 declarations with the axiom status recorded there.

### 4.1 End traits, field monodromy and the slope layer

| Module and Lean name | Source | Inputs and result |
|---|---|---|
| `Traits` · `endTrait`, `endUniformizer`, `puncturedEnd`, `fourierCharacter` | Laumon (0.2), (2.1.1), (2.4.1), pp. 150–151, 162 | **New.** The pointed henselizations at the two rational ends in both lines, their coordinate maps and generic and geometric points, and a choice of `ψ ≠ 1` from the trace and a primitive `p`th root of unity in `E`. |
| `FieldMonodromy` · `FiniteEtaleFieldMonodromyStatement`, `LadicFieldMonodromyStatement` | Laumon (2.1.2)–(2.1.2.1), p. 152. Katz (1.5.3)–(1.5.6) for finite levels and the inverse limit | **New, b1.** Use the field points, discrete module equivalence, lisse monodromy, finite matrix coefficient descent, lattice theorem and continuity equivalence from §3.2. Compare the field fibre functor's automorphism group with the separable closure Galois group using the finite Galois algebras, their transition maps and the stabilizer bases. Compare matrix, joint action and endomorphism continuity via finite coordinate maps. The span of the basis over the common finite field identifies the external continuous scalar-extension model with the Library's witness for `IsLadicDefinedOverFiniteExtension`. Match the compatible finite reductions, changes of carrier universe, all linear intertwiners, exactness, tensors and irreducible classes. |
| `Completion` · `HenselianCompletionGaloisStatement`, `HenselianCompletionRamificationStatement` | Katz (1.4.8)–(1.4.9), pp. 81–82. Serre II §3, IV §§1, 3. Laumon (2.1.1) | **New, b2.** Apply the Library henselian completion equivalence at the chosen local coordinate, with `k[[t]]` as completed valuation ring. Construct restriction with compatible separable closures and keep the profinite topology via finite quotients. The finite lower groups compare on quotients of the integer rings by powers of the maximal ideals. Transfer upper, wild and inertia groups, residue maps and degree. |
| `BoundaryMonodromy` · `boundaryMonodromy`, `BoundaryStalkInertiaStatement` | Laumon (2.2.1), pp. 155–156, (2.4.2.1), p. 162 | **New, b2.** Pointed pullback along `η_z^h → U`, (b1), the completion comparison, and the `j_*` stalk and functorial monodromy inputs in §3.2. Identify the strict-local inertia and residual degree action with the Library at the chosen completion, compatibly with change of geometric point. |
| `UnramifiedLines` · `unramifiedLine`, `UnramifiedLineMonodromyStatement`, `LocalWeilRestrictionStatement` | Laumon (2.1.1), (2.1.5), (2.5.2), Henniart §4.1–4.3 | **New.** The residue quotient and (b1–b2) give the same pulled-back arithmetic line at both ends. Compare its Frobenius with the Weil scalar and use the actual local projection and dense restriction for arithmetic-origin representations. Include preservation and reflection of intertwiners, finite model and simplicity on the restricted continuous image. |
| `TameInertia` · `LocalTameInertiaQuotientStatement` | Laumon (2.1.1), p. 151. Serre IV §2 | **New comparison.** Over the strict trait use the prime-to-`p` Kummer towers and the completed Laurent-series classification of §3.2. Use (b2) and the finite first lower group structure to identify Weil and Galois tame inertia `I/P` with the inverse limit of `μ_n(k̄)` for `p ∤ n` as topological groups. Retain the natural residue Galois action on the roots of unity for §4.3. |
| `Langlands.LocalFactor.Ramification.Wintenberger.Absolute` · `Langlands.Ramification.Wintenberger.localAbsoluteUpperFiniteImage` | Serre IV §3, Prop. 14 and its first remark, pp. 74–75 | **Proved in the Library**, with `[propext, Classical.choice, Quot.sound]`. For every local field and separable closure, restriction to every finite Galois subextension sends the absolute upper group of level `u ≥ −1` onto the finite group at the same upper level. Apply over `LaurentSeries k` and its finite constant extensions via (b2). |
| `Slopes` · `WildImageFiniteStatement`, `slopeSummand`, `slopeSupport`, `ladicSwan`, `SlopesExactStatement` | Laumon (2.1.2.2)–(2.1.2.5), p. 152. Serre IV §§2–3. Katz 1983 pp. 211–213 | **New in the ℓ-adic layer.** Restrict a stable lattice of a finite-model representation to a finite free `ℤ_ℓ`-lattice and import the pro-`p` open-kernel theorem of §3.2 for its continuous action. The finite first lower groups supply `g^(p^n) → 1` on wild inertia. Compactness and the open kernel give finite wild image. Use the Library upper filtration and a finite quotient of wild inertia realizing this action. Average over the images of its positive upper groups and form their consecutive invariant summands, including `V^P` at slope zero. Prove normality-stability, independence of the finite model for the wild action, additivity and exactness of the projectors. The tame condition is that the wild group acts trivially, equivalent to having slopes in `{0}`. An action of tame inertia with infinite image can also occur on a positive-slope block. |
| `SlopeIntegrality` · `FiniteInertiaPositiveBreakModelStatement`, `SlopeIntegralityStatement` | Laumon (2.1.2.4)–(2.1.2.6), pp. 152–153. Katz 1983 pp. 211–214. Serre IV §§2–3 and VI §2, Thm. 1 | **New.** For an arbitrary continuous finite-model `I`-module, produce a finite-image `I`-module of the same rank and with the same dimensions of fixed vectors for every `I^u`, `u > 0`. Use finite-image models of irreducible inertia factors and exact positive upper invariants as below. Apply the exact absolute finite-image theorem, the weighted conductor comparisons and the equal-characteristic finite-inertia integrality input to each slope block. This gives rational slopes with `λ·rank(V_λ)` integral on all inertia-stable slope blocks. |
| `SlopeCalculus` · `IrreducibleSingleSlopeStatement`, `UnramifiedTwistSwanStatement`, `SwanOneTensorStatement` | Laumon (2.1.2.4)–(2.1.2.7), pp. 152–154. Katz 1983 pp. 211–215. Serre IV §3 and VI §2 | **New ℓ-adic comparisons.** For a Swan-one line, a slope below one becomes one, a slope above one stays fixed, and the slope-one part has slopes at most one after tensoring. Use `SlopeIntegralityStatement` on the inertia-stable blocks of `V_1 ⊗ L`. If such a block has slope `λ < 1` and rank `m`, then `λ ≤ 1 − 1/m ≤ 1 − 1/rank(V_1)`. This gives the fixed-space equality test in (2.1.2.7)(ii) for `0 ≤ ε < 1/rank(V_1)` at `I^{1−ε}` when `V_1 ≠ 0`. Twisting by a line trivial on inertia and coordinate negation preserve all slopes. For a simple module of rank `r`, stability of the decomposition gives its unique slope `s(V)/r`. |
| `ArtinSchreierBreak` · `ArtinSchreierPoleOneStatement` | Laumon (2.1.2.8), p. 154. Serre IV §§1–3, especially §2, Exercise 5 | **New.** Import the arithmetic character line and tensor identities of §3.4 and the simple-pole polynomial and geometric ramification inputs of §3.2. Identify the local stalk with the corresponding deck character by the projector and (b1–b2). Compute the finite break by valuation and Herbrand and apply the exact absolute finite-image theorem. Apply the tensor and inverse identities to obtain the break of the ratio of two distinct linear-parameter kernels, including over a finite constant extension. |

For the finite model of the positive breaks, first take an irreducible
`I`-module over `E` and choose a stable `𝒪_L`-lattice for its action over a
finite ℓ-adic field `L`. Let `H` be its compact image and `P_H` its finite
wild image. The kernel `U` of reduction of `H` on the lattice modulo the
maximal ideal is open, normal and pro-`ℓ`. It intersects `P_H` trivially.
The group `H/P_H` is procyclic by the tame inertia comparison. Commutators
of `U` with `H` therefore lie in `U ∩ P_H`, so `U` acts centrally and
hence by scalars on the irreducible module. Its image in `H/P_H` is open
and lies in the pro-`ℓ` factor. Extend the scalar character of that image
to the procyclic quotient. In the ℓ-primary factor choose a generator
`γ` and write its open subgroup as generated topologically by
`γ^(ℓ^a)`. The scalar there is a principal unit since the subgroup is
pro-`ℓ`. Choose an `ℓ^a`th root in a finite enlargement of `L`. The root
is again a principal unit. In a finite ℓ-primary factor it has the
required order bound, and in a copy of `ℤ_ℓ` it defines a continuous
character by the limits of its powers on the finite reductions. Use
the trivial character on the prime-to-`ℓ` factor.

Twist the irreducible action by the inverse of this tame character to
kill `U`. The resulting action is finite and agrees on `P` and each
positive upper group. For a general `I`-module, take a composition
series and sum these finite-image models of its factors. Exactness of
positive upper invariants gives equality of every positive-break fixed
dimension. For the finite model, choose an open normal subgroup of
`G_K` whose intersection with `I` is contained in its inertia kernel.
Surjectivity of inertia restriction identifies the quotient through
which the action factors with a finite inertia model in the Library
sense. Use `Langlands.Ramification.Wintenberger.localAbsoluteUpperFiniteImage`
to identify every positive upper invariant space with the one at the
same index in the finite model. Use finite-to-finite upper compatibility
to compare refinements and characteristic-zero scalar extension on the
finite matrix actions. Apply finite inertia Swan
integrality to each slope summand of the finite model to obtain
`λ·rank(V_λ) ∈ ℤ` for `λ > 0`. Total rank and the positive fixed
dimensions account for the slope-zero multiplicity. The proof of the
Artin and transported Swan identity in (b3) uses the actual
finite-inertia action of an irreducible arithmetic Galois class.

For the pole computation, use the completed equation `u^q − u = c/t`,
where `q` is the cardinality of the character field and `c` is nonzero in
the residue field. Use the irreducibility theorem for degree `q` and the
translations by the character field for the Galois group. For an extended
residue field and `c` in that field, the irreducibility theorem still applies
and the roots are again all the translates of `u`. In the normalized
valuation on the extension, `v(u) < 0` gives `qv(u) = −v(t) = −e`.
Use `e ≤ q` to get `e = q`, residue degree one, and uniformizer `π = u⁻¹`.
For nonidentity deck translation by `a`, evaluate
`σ_a(π) − π = −a/(u(u+a))` to get valuation two. This gives full lower groups
at `0` and `1`, and trivial lower groups from `2` onwards. Apply Herbrand on
the interval from `0` to `1` and apply the exact absolute finite-image
theorem to restriction to the splitting field. The nontrivial character
then has a single upper break `1`. Use the
geometric obstruction in §3.2 when checking the corresponding absence of
constant geometric constituents.

For the slope layer, the Library provides
`Langlands.Ramification.Local.localAbsoluteUpperRamificationGroup` and
`Langlands.Ramification.Local.localWildInertia` in
`Langlands.LocalFactor.Ramification.Herbrand.GeneralAbsolute`,
`Langlands.Ramification.Local.localUpperRamificationGroup` in
`Langlands.LocalFactor.Ramification.Herbrand.GeneralFinite`.
For finite-to-finite refinement use
`Langlands.Ramification.Local.upperQuotientCompatibility` in
`Langlands.LocalFactor.Ramification.Herbrand.LocalQuotientProof`.
`Langlands.Ramification.Local.upperBreakMultiplicities` in
`Langlands.LocalFactor.Ramification.Breaks` uses complex coefficients.
Use its filtration and finite multiplicity calculation as the comparison
for the ℓ-adic projectors. Consume the equal-characteristic versions of
`Langlands.Ramification.Local.FiniteUpperBreakWeightedSwan`,
`Langlands.Ramification.Local.FiniteUpperBreakArtinIdentity`, and
`Langlands.Ramification.Local.PresentationUpperBreakIndependence` in
`Langlands.LocalFactor.Ramification.LocalWeilBreakStatement` when relating
those projectors to the Library's conductor. The finite first lower
group input uses `Langlands.Ramification.isPGroup_lowerGroup_one` in
`Langlands.LocalFactor.Ramification.LowerGroupQuotients` on the
separated integer-ring filtrations. For the finite integrality input
use the equal-characteristic analogue of
`Langlands.Ramification.Padic.exists_nat_inertiaSwanConductor` in
`Langlands.LocalFactor.Ramification.ArtinExponent`, based on the finite
Artin character over the fixed field of inertia and subtraction of the
codimension of inertia invariants.

### 4.2 Arithmetic Fourier and Euler–Poincaré

| Module and Lean name | Source | Inputs and result |
|---|---|---|
| `FourierRealization` · `fourierProjectionCompactification`, `boundedConstructibleArithmeticFourier`, `ArithmeticFourierRestrictionStatement` | Laumon (1.2.1.1), p. 141, and (2.3.3.1), p. 161 | **Import** the arithmetic character line, kernel and ambient `condensedFieldFourierTransform` of §3.4. Choose the character using the constant-section map `E → MonObj.Γ Λ`. Supply `A × A' ↪ D × A' → A'` as the compactification, using the relative projective line over `A'` and the affine-space pullback isomorphism. **New** specialization and bounded constructible restriction. Compose the imported restricted pullback, tensor by the bounded constructible kernel, `Rp₂!` for that compactification, and `[1]`. Compare the inclusion of this functor with the ambient functor, including on the zero-extended input. |
| `FourierRealization` · `extendedFourierKernel`, `ArithmeticFourierCompactifiedTargetStatement` | Laumon (2.3.2.1)(iii), p. 160, and (2.3.3.1)(iii), p. 161 | **New.** Write `B_K` for the kernel tensored with the source pullback of `K` and extended by zero to `D × A'`, before shift. Unfold the chosen compactification to get `M_K ≅ Rq_* B_K[1]`, where `q : D × A' → A'`. Extend `B_K` by zero in the target direction to `B̄_K` on `D × D'`, and use `q̄ : D × D' → D'`. Verify that `Rq̄_* B̄_K[1]` restricts to `M_K` on `A'` by weakly étale base change and has zero special restriction at `∞'` by the ambient Noetherian proper base-change theorem. Localization identifies it with the zero extension of `M_K`. |
| `FourierRealization` · `ArithmeticArtinSchreierWeilComparisonStatement`, `ArithmeticFourierWeilComparisonStatement` | Laumon (1.1.3.2), (1.2.1.1), (1.2.2.9) and (2.4.2), pp. 140–145, 162–163 | **New** Frobenius-compatible comparisons. For the torsor line, use finite direct-image exchange, identify the regular coefficients and translations, and carry the projector and its image to the Weil projector. Pull back along the pairing and compare exact tensor by the lisse line. Use the geometric-fibre comparison of §3.4 at `k̄` and the compactification comparison on the arithmetic bounded constructible domain to align the explicit projective chart with the compactification chosen in the Weil functor. Compose the comparisons with the shift and the Weil realization of `j_!`. |
| `FourierRealization` · `ArithmeticFourierFibreStatement`, `FourierCommutesWithFiniteBaseChangeStatement` | Laumon (1.2.2.1)–(1.2.2.2), (1.2.2.9), pp. 142–145 | **Import** the arithmetic compact-support exchange and its invertibility for the finite-type squares in §3.4. **New** arithmetic fibre formula using derived pullback of the kernel, including `RΓ_c[1]` at the origin. Use the same exchange for finite constant-field changes, where both schemes are of finite type over `k`. Identify the coefficient lines by the map of Artin–Schreier torsors given by the additive trace polynomial, with character `ψ ∘ Tr` on the extended constant field. |
| `FourierRealization` · `ArithmeticFourierKernelCohomologyStatement`, `ArithmeticFourierInversionStatement` | Laumon (1.2.2.3), (1.2.3.1), pp. 142–145, and (2.5.6), p. 169 | **New** arithmetic convolution and natural inversion. Use the imported Weil fibre, constant and convolution formulas, arithmetic composition, projection formula and smooth trace in §3.4. Tensor the two arithmetic kernels on the triple product using the character addition map. On `x+y ≠ 0`, scale the middle variable and use the compact-support vanishing of the nontrivial Artin–Schreier line on the line, detected by the Weil constant transform and its fibre. On `x+y = 0`, use compact support of the unit line. Compare its trace with the geometric affine-line trace and use finite-type exchange to obtain `E(−1)[−2]` with its arithmetic Tate action along the antidiagonal. Reassemble by open–closed localization and use composition and projection to identify the product of transforms with the convolution. The two shifts `[1]` cancel `[-2]`. This gives reflection and Tate twist by natural arithmetic maps, with the Weil identity as the comparison. |
| `FourierTypes` · `WeilFourierTypeExchangeStatement` | Laumon (1.4.2)–(1.4.2.1), pp. 148–149. BBD (4.3.1)(ii) | **Import** the direct punctual formula, Weil inversion and the nonexceptional middle-extension result of §3.4. **New** bundled exchange with nonexceptionality of the output. Apply the punctual formula to a closed point of degree `m` for `(T1) → (T2')`, then use inversion for the reflected, Tate-twisted punctual output of `(T2)`. For `(T3)`, use the middle-extension result to obtain the irreducible lisse output on a dense open. Exclude a linear geometric constituent of this output by identifying such an irreducible extension with type `(T2')` by the argument below and applying inversion. |
| `CurveRiemannHurwitz` · `curveDifferent`, `CurveDifferentialsDifferentStatement`, `TameCurveDifferentStatement` | Serre III §§3, 6–7, especially Prop. 14, pp. 59–60, and IV §2. Raynaud §4 Lemma 1 | **New.** For a finite generically separable morphism `f : Y → X` of smooth projective geometrically connected curves over a perfect field, define the effective different divisor by the exponents of the completed local DVR differents. Identify the completed cokernel of `f*Ω¹_X → Ω¹_Y` with the relative differentials. Their length is the local different exponent by the differential characterization. In the tame case this exponent equals the ramification index minus one. Use the curve degree and ramification-index inputs in §3.6. |
| `CurveRiemannHurwitz` · `CurveRiemannHurwitzDifferentStatement` | Raynaud §4 Lemma 1. Katz (1.2)–(1.3), (1.4.2) for the tame comparison | **New**, using `CurveDifferentialsDifferentStatement` and the proved canonical degree, divisor degree, pullback degree and genus base change of §3.6. Establish the formula below for finite separable maps over a perfect field, including the algebraically closed case and its tame formula. |
| `EulerPoincare` · `localSwanTerm`, `genericRank`, `stalkRank`, `totalConductor`, `compactEulerCharacteristic` | Laumon (2.2.1), pp. 155–156. Raynaud §3 | **New.** Arithmetic curve with finite stratification, (b2) and the slope layer. Define the signed rank, stalk rank, Swan term and their conductor combination `a_z`. Use compact support to define a signed integer from finite-dimensional geometric cohomology. Include the boundary formula for `j_!` when using a projective completion. |
| `EulerPoincare` · `CurveConstantEulerCharacteristicStatement` | Raynaud §4 Lemma 1 | **New** constant-coefficient calculation `χ(C̄,𝔽_ℓ)=2−2g(C)` for smooth projective geometrically connected curves. Use the roots-of-unity cohomology of §3.6, the genus comparison and a primitive `ℓ`th root over the algebraic closure to compute the dimensions. Use the étale-to-pro-étale comparison and identify the constant unit under the finite condensed coefficient equivalence. Reduce finite coefficient fields to `𝔽_ℓ` by scalar extension. |
| `EulerPoincare` · `CurveAutomorphismLocalTermStatement`, `FinitePushforwardConductorStatement` | Raynaud §4, Lemmas 1–2 and formulas (3)–(4). Serre IV §1, VI §2 | **New.** For a smooth normalized projective curve carrying a finite group, compare the local term of a nonidentity automorphism with the graph–diagonal intersection length, equal to the lower ramification multiplicity. Use the proper trace-localization input of §3.4. For finite maps compare ranks and Artin/Swan terms by induction and the different. Apply `CurveRiemannHurwitzDifferentStatement` and `CurveConstantEulerCharacteristicStatement` to compare the two constant-coefficient Euler characteristics in Raynaud's finite-pushforward step. Also identify the equivariant Euler characteristic of the regular-cover construction, the coefficient step of Raynaud's Lemma 2. |
| `EulerPoincare` · `TorsionEulerPoincareStatement`, `AdicEulerPoincareStatement` | Raynaud §3 Théorème 1 and §4. Laumon (2.2.1.2), p. 156 | **New, b3.** Use the preceding trace and conductor comparisons, dévissage to finite monodromy on a lisse open, and modular reduction and induction on finite groups in Raynaud §4. First prove `χ_c(Ū,F) = rank(F) χ_c(Ū,E) − Σ_z deg(z) sw_z(F)` in its finite-coefficient version, with `z` over the boundary. For an integral lattice compare the characteristic-zero Euler characteristic with its reduction by derived reduction and finite cohomology. Wild invariant ranks commute with reduction by prime-to-ℓ averaging. Add finite-support strata and alternating cohomology to reach `χ(D̄,K)=r(K)χ(D̄,E)−Σ_z deg(z)a_z(K)` on the projective completion. Use this for the compact-support version on open curves. |
| `FourierRanks` · `FourierStalkEulerCharacteristicStatement` | Laumon (2.3.1.1), proof, pp. 158–159 | **Import** the degreewise origin and rational-point Frobenius-module comparisons of §3.4. Use their linear equivalences and the degree shift to identify the signed stalk rank of the transform at `a` with `−χ_c(Ā,K⊗Lψ(ax))`, with the constant kernel at the origin. The **new** arithmetic statement uses the Fourier realization and finite constant-field base change of §4.2 to carry these dimension equalities to the arithmetic transform and to each finite closed point via a rational point over its residue field. |
| `FourierRanks` · `CurvePerverseLissityStatement`, `FourierLocalRankStatement`, `FourierLissityAtFinitePointsStatement`, `FourierZeroExtensionRanksStatement` | Laumon (2.2.1.1), (2.3.1.1)(i)–(iii) and their inverse formulas, (2.3.1.2)–(2.3.1.3), pp. 155, 158–159 | **New**, using the imported curve heart, (b2), `FourierStalkEulerCharacteristicStatement`, GOS and the slope-one tensor rule. Prove `a_z=0` iff the shifted perverse sheaf is lisse at `z`, with the same signed stalk and generic ranks. Apply GOS to the fibre Euler characteristics to obtain the conductor formulas. For the generic value avoid cancellation on the slope-one summand by passing to a finite constant extension with sufficiently many parameters, whose kernel ratios have break one. Inversion gives the primed formulas. For `K=j_!F[1]` with `F` tame at `∞`, obtain lissity of the unshifted transform on `A'−{0'}`, rank `r(F)+s_0(F)` and signed `r_{0'}=s_0(F)` by GOS. The version tame at `0` is needed for the exchanged inverse. |

For the Riemann–Hurwitz package let `n=[k(Y):k(X)]`. Use the normalized
valuation on the completed local ring at each closed point `y` of `Y`
to define the exponent `δ_y` of the different over the completed local
ring at `f(y)`. The local map is finite flat and has separable fraction
and residue extensions. The canonical differential map is generically
invertible, hence injective, and its cokernel has length `δ_y` at `y`.
Indeed the relative Kähler module commutes with completion for these
finite maps and the completed extension has a monogenic presentation,
whose polynomial derivative generates both the different and the
annihilator of the cyclic relative Kähler module. This identifies
`ω_Y` with `f*ω_X ⊗ 𝒪_Y(D_f)` for `D_f=Σ_y δ_y[y]`, and proves that the
support is finite. In the tame case, use a uniformizer equation
`t=u^e h(u)` with a unit `h` in the completed ring after the unramified
part. Since `e` is prime to the residue characteristic, `dt/du` has
valuation `e−1`.

Take degrees over an algebraic closure using the divisor pullback and
canonical-degree results of §3.6. The finite map is flat by
torsion-freeness over the local DVRs of the smooth target. Under this
extension of constants, closed points split according to the separable residue degree and the
length of the differential cokernel at each point above `y` is `δ_y`.
Use flat base change for genus. The result over the original perfect
field is
`2g(Y)−2 = n(2g(X)−2) + Σ_y [κ(y):k] δ_y`.
Over the algebraic closure each weight is one.
[Raynaud, §4 Lemma 1](https://www.numdam.org/item/SB_1964-1966__9__129_0/)

For the exceptional-constituent identification, work with the Weil
representation of the irreducible lisse sheaf on the dense open.
Restriction to the normal geometric group is semisimple by the span of
the conjugates of a simple submodule. If one geometric constituent is
`Lψ(ax)`, use distinctness of the linear characters to identify its orbit
with the closed point of parameter `a` of degree `m`. Choose a
Frobenius-to-the-`m` eigenline in this isotypic space. On that constant
extension the line is the restricted arithmetic Artin–Schreier line
times a constant Weil character. Identify its induced sheaf with the
finite pushforward of the kernel tensored by this character from the
closed point. Its map onto the irreducible input is an isomorphism since
the geometric orbit consists of distinct lines. The finite pushforward
is lisse on the whole line and agrees with the direct-image middle
extension. This identifies type `(T2)` in the classification of (1.4.2)
and works on either line.

### 4.3 Canonical extensions and the global tame input

| Module and Lean name | Source | Inputs and result |
|---|---|---|
| `TameCovers` · `GeometricTameKummerCofinalityStatement`, `TamePuncturedLineEquivalenceStatement` | Laumon (1.1.3.7), (2.1.1), (2.2.2.1), p. 157. Katz (1.2)–(1.3), (1.4.2) | **New** two-ended comparison. Import the Kummer torsor from §3.2, use `LocalTameInertiaQuotientStatement` from §4.1 and use `CurveRiemannHurwitzDifferentStatement` with `TameCurveDifferentStatement` from §4.2. Prove cofinality of the Kummer covers among geometric covers of `𝔾_m` tame at both ends, compare both restrictions to the local towers, and descend the comparison through the pointed constant-field exact sequences. Use (b2) for compatibility with the henselian and completed models. |
| `ArtinSchreierComparison` · `artinSchreierQuotient`, `AffineArtinSchreierCohomologyStatement`, `ArtinSchreierLaurentPolynomialStatement` | Katz (1.4.5), p. 80 | **Import** the short exact Artin–Schreier sequence with constant kernel and the affine `𝔾_a` and constant `ℤ/p` vanishing of §3.2. **New.** On `Spec B` for an `𝔽_p`-algebra `B`, identify `H¹(ℤ/p)` with `B/(F−1)B` naturally in `B` and use the imported higher vanishing. Prove that `R[T] → R((T⁻¹))` induces an isomorphism on these additive quotients by the power-series splitting below. |
| `ProPCoverComparison` · `maximalProPQuotient`, `AffineEtaleFundamentalGroupCohomologyStatement`, `FreeProPComparisonStatement`, `ArtinSchreierCoverComparisonStatement` | Katz Prop. (1.4.2), Lemma (1.4.3), (1.4.4)–(1.4.6), pp. 79–81, and (2.3.7)–(2.3.8), pp. 96–97 | **New.** Compare cohomology of a connected affine `𝔽_p`-scheme with continuous fundamental-group cohomology by the finite étale Galois towers and higher vanishing on every finite cover. Construct the maximal pro-`p` quotient from finite `p`-group quotients, apply the freeness criterion and test maps between free pro-`p` groups on continuous `𝔽_p`-characters. The degree-one comparison above therefore gives an equivalence on finite étale covers of `Spec R[T]` and its punctured neighbourhood with `p`-group monodromy. |
| `SpecialCovers` · `specialCover`, `SpecialCoverEquivalenceStatement` | Katz (1.3.1)–(1.3.3), Main Theorem (1.4.1), pp. 74–79 | **New.** The special-cover condition is tame at the opposite end with a unique `p`-Sylow in the geometric monodromy. Reduce to a `p`-group cover after a finite constant extension and a prime-to-`p` Kummer covering, using `TamePuncturedLineEquivalenceStatement`. Use `ArtinSchreierCoverComparisonStatement` after that covering. Compare the finite descent actions on the affine and local sides, including Kummer deck transformations and constant-field automorphisms, and descend both covers and morphisms using their compatible fibre functors. |
| `CanonicalExtension` · `KatzGabberRetractionStatement`, `canonicalExtension`, `CanonicalExtensionMonodromyStatement` | Katz (1.4.8)–(1.4.11), (1.5.3)–(1.5.6), pp. 81–85. Laumon (2.2.2.2), p. 157 | **New, b4.** From the special-cover equivalence get the two quotient retractions and their compatibility over the residue Galois group. Inflate lattice reductions, pass to the limit and extend scalars using (b1–b2). For `x` or `1/x` obtain a functorial arithmetic extension with the required monodromy, tameness and tensor behaviour. Include the geometric finite-monodromy compatibility of Laumon (2.2.2.2) for finite-image inputs. |
| `TameFourier` · `kummerLine`, `gaussLine`, `KummerGaussFourierStatement` | Laumon (1.1.3.7), (1.4.3.1)–(1.4.3.2), pp. 149–150. SGA 4½ *Sommes trig.* (4.3), (4.20) | **New.** Use the Kummer torsor from §3.2, where the prime-to-`p` roots of unity are present, and the arithmetic Artin–Schreier line. For a nontrivial character `χ` realize the Kummer summand `K_χ` and the arithmetic Gauss line `H_c¹(𝔾_m ⊗ k̄,K_χ⊗Lψ)` with its geometric Frobenius. Prove boundary cleanliness `j_! ≃ Rj_*`, concentration and rank one for the Gauss line, and the Fourier formula `FT(j_!K_χ[1]) ≅ j'_!K_{χ⁻¹}[1] ⊗ G(χ,ψ)` via change of variables and the fibre computation. The imported constant and punctual formulas handle the trivial character. |

For the geometric cofinality, normalize `D` over `k̄` in a connected
geometric cover of degree `n`. The normalization is smooth projective.
Use tame Riemann–Hurwitz with `g(D)=0` and boundary terms `e_y−1` to get
`2g−2=−r₀−r∞` for the respective numbers of points over the two ends.
Deduce genus zero and a single point over each end. The genus-zero
Riemann–Roch formula of §3.6 at the point over infinity supplies a
degree-one function `u`. Subtract its value over zero. The divisor of
the pullback of `x` is then the divisor of `u^n`. Rescale `u` over `k̄`
to obtain the model `u^n=x`. Tameness gives `p ∤ n`. At `0` and `∞`, restrict this
tower using `x` and `1/x` and invert the Kummer coordinate at the second end.
Compare the actual restriction maps of geometric tame groups through
these finite quotients and their transition maps. On the group of deck
transformations `μ_n(k̄)`, the constant Galois action is cyclotomic.
Geometric Frobenius acts by the inverse of the `q`th power. Use these maps
and the identity on the residue quotient in the arithmetic exact
sequences to obtain both arithmetic isomorphisms of (2.2.2.1).

For the degree-one Artin–Schreier comparison, put `u=T⁻¹`. The
decomposition `R((u))=R[T] ⊕ uR[[u]]` is additive and stable under
absolute Frobenius `F`. On the second summand `F` is topologically
nilpotent for the `u`-adic filtration, since it multiplies the
orders of monomials by `p`. The coefficientwise finite series
`Σ_{m≥0} F^m` inverts `1−F` there. Thus constants and the
polynomial part give exactly the same Artin–Schreier quotient
on the two rings. Combine this with the natural connecting
isomorphism from the affine Artin–Schreier exact sequence.

For the pro-`p` step, each finite connected étale Galois cover
of an affine scheme is affine and has the imported higher
`ℤ/p` vanishing. Each degree-one class on such a cover is an
`𝔽_p`-torsor and becomes trivial on a further finite Galois
cover. Take filtered colimits of the Hochschild–Serre spectral
sequences over these covers. The rows of positive fibre degree
vanish in the colimit, using that cochains on a finite deck
group have finite image for the degree-one row. The surviving
row is continuous fundamental-group cohomology. In particular
its `H²` vanishes, so the maximal pro-`p` quotient is free by
Katz (2.3.8.1). The map on these quotients induces the
degree-one Artin–Schreier comparison on characters and is an
isomorphism by (2.3.7). This realizes the pointed restriction
map on covers used in the descent in (1.4.1).
[Katz 1986, (1.4.3)–(1.4.6) and (2.3.7)–(2.3.8)](https://www.numdam.org/articles/10.5802/aif.1069/)

### 4.4 Nearby and vanishing cycles on the Fourier charts

| Module and Lean name | Source | Inputs and result |
|---|---|---|
| `StrictTargetTrait` · `strictTargetTrait`, `StrictTargetTraitGaloisStatement` | SGA 7 XIII (0.2.5), (1.3.2.1)–(1.3.2.2), (2.1.3)–(2.1.4). Laumon (2.4.1)–(2.4.2.1) | **New.** Use the localization in the chosen maximal unramified extension, equivalently the pointed strict henselization of the target. Realize it at a rational end as the colimit of finite constant extensions. Identify restriction of the generic Galois action to this trait and its residue with the unramified quotient in (b2). |
| `NearbyCycles` · `traitNearbyModel`, `arithmeticNearbyStalk`, `StrictNearbyStalkFormulaStatement`, `NearbyStalkGaloisStatement` | SGA 7 XIII (1.3.2.1)–(1.3.2.2), (2.1.1), (2.1.2.3), Prop. (2.1.4), (2.1.7.1). Laumon (2.3.2), (2.3.3), (2.4.2) | **New** chart models and arithmetic action on their nearby stalks. Use the chart over the strict target as total space and source, with generic and special fibres formed over this strict target. For the stalk formula use the strict-local sections theorem, comparison of sites and weakly étale exchange on source-side pointed neighbourhoods over the fixed strict target. Equip the pullback of the arithmetic input with its canonical isomorphisms under the model automorphisms. Use the exchange isomorphisms and their square law to obtain the full action. On the separable model identify the restriction to inertia with `galoisLayerAction`. |
| `NearbySpecialization` · `nearbySpecialization`, `NearbySpecializationNaturalityStatement` | SGA 7 XIII (1.4.2.2), (2.1.1)–(2.1.2), pp. 97–99. Laumon (2.3.2.1), (2.4.2.1) | **Import** `twistSpecializationMap` of §3.3 for `Li*B ⟶ Ψ_M(K)` with `B=Le*K` and `ε=j≫e`. Define `nearbySpecialization` for the chart by supplying the composition isomorphism `Lε*K ≅ Lj*B` to that arrow. **New** coherent naturality with pullback exchange, proper pushforward exchange, the arithmetic action and coefficient changes. Use the defining adjunction formula and the unit and counit identities of the mates. |
| `StrictTraitBaseChange` · `StrictTraitConstantBaseChangeStatement` | Laumon (2.5.2), p. 165. SGA 7 XIII (1.3.2.1)–(1.3.2.2) and (2.1.2.3) | **New.** For a finite constant extension with its embedding into the fixed geometric residue field, identify the two strict target traits, lifted charts and specialization arrows. The arithmetic action restricts to the open subgroup fixing the new constants. |
| `NearbyCycleCoefficients` · `NearbyCyclesIntegralModelStatement`, `NearbyCyclesReductionStatement` | SGA 4½ *Th. finitude* Thm. 3.2 and Prop. 3.7. SGA 7 XIII (1.4.2.2), (2.1.1). Laumon (2.4.2.1)–(2.4.2.2), pp. 162–163 | **Import** integral model existence on the noetherian finite-type charts, finite reductions and finite-coefficient constructibility and comparison theorems in §3.3. **New** compatible integral model comparisons for the arithmetic inputs, the specialization map and `RΨ`. Choose the integral line and lattice for the Fourier kernels and enlarge the finite coefficient field for diagrams of inputs. Use `Rj̄_*` comparison for reduction modulo `ℓⁿ` at every level and the bounded below residue-field comparison for the first uniformizer reduction. Compose with the stated pullback and extension-by-zero comparisons. On the completed strict model supply finite type and the `p`-invertibility and étale-origin conditions for the reductions. |
| `NearbyCycleCoefficients` · `NearbyCyclesRationalizationStatement`, `NearbyCyclesCoefficientNaturalityStatement` | SGA 4½ *Th. finitude* Thm. 3.2. SGA 7 XIII (1.4.2.2), (2.1.1). Laumon (2.4.2.2), (2.5.2) | **Import** the two scalar extension comparisons for `Rj̄_*` on bounded below input and qcqs generic inclusion and the composition with `RΨ` in §3.3. **New** comparisons on the coefficient tower with the actual chosen `E`-valued functor and the specialization units. Use the adjunction mates defining the pushforward comparisons and naturality on the finite generic layers and on the special fibre to match transitions, units and the full arithmetic action. Extend `𝒪_L → L → E` after producing the integral models. |
| `NearbyGenericFibre` · `NearbyGenericFibreComparisonStatement` | SGA 7 XIII (1.3), (1.4.2.2), (2.1.1). SGA 4½ *Th. finitude* Thm. 3.2, Prop. 3.7. Laumon (2.4.2.1)–(2.4.2.3) | **Import** the universal-homeomorphism exchange and its description by the generic adjunction unit from §3.3. **New** comparison for the two choices of geometric generic field, with fixed source, total and geometric special spaces on each trait. Prove that it intertwines the lifted Galois actions and arbitrary-input specialization, and commutes with the reduction tower and rationalization. Identify the finite-layer maps inside the separable model below. |
| `VanishingCycles` · `vanishingCycles`, `VanishingCyclesTriangleStatement`, `VanishingCyclesProperExchangeStatement`, `VanishingCyclesTraitChangeStatement` | SGA 7 XIII (1.4.2.2), (2.1.1), (2.1.7.1). SGA 4½ *Th. finitude* Prop. 3.7. Laumon (2.4.2.1), (2.5.2) | **New** with **imported** nearby operations. Form the cofiber of `nearbySpecialization` on a functorial complex model and use its equivariance. Compare the triangles under reduction, rationalization and generic-fibre exchange using the compatible maps above. Prove the long exact sequence and comparison maps with proper direct image, pointed local restriction and strict-trait change. For proper exchange both charts and their geometric fibres are over the same strict target. Use the direct strict-trait comparison for completion, with the prescribed Cartesian total-space and fibre squares over the respective DVRs, algebraically closed generic fields and compatible field maps. |
| `VanishingCycles` · `StrictIdentityTraitCyclesStatement` | SGA 7 XIII (2.1.2.3), Prop. (2.1.4). SGA 4½ *Th. finitude* Prop. 3.7 | **New** check of the models. For the identity map of a henselian target and a finite constant coefficient ring `Λ` with `p` invertible, the strict-local stalk formula gives `ΨΛ=Λ[0]`. Specialization is the identity under this identification, the action is trivial and `ΦΛ=0`. Compare with the imported tensor-unit isomorphism on the complete strict identity trait. |
| `NearbyCycleContinuity` · `FiniteNearbyVanishingStalkActionStatement`, `AdicNearbyVanishingStalkStatement` | SGA 7 XIII (1.3), (1.4.2.2), (2.1.1). SGA 4½ *Th. finitude* Thm. 3.2. Laumon (2.4.2.2)–(2.4.2.3), p. 163 | **New.** Transport finite-level constructibility from the complete algebraically closed generic model to the separable generic model using the preceding exchanges. Prove continuity and finite generation of the arithmetic nearby and vanishing stalks from this finiteness, the finite separable generic-layer actions and the derived complete integral comparison. Then rationalize to obtain finite-model continuous representations of the whole target Galois group for the local functors, using (b1–b2). |
| `FourierTraitRestriction` · `ArithmeticFourierTraitRestrictionStatement` | Laumon (2.3.2.1)(iii), p. 160, (2.3.3.1)(iii), p. 161. SGA 7 XIII (2.1.2.3), (2.1.7.1) | **Import** the ambient weakly étale base-change isomorphism of §3.4. **New** comparison for the Cartesian squares below. Pull back the actual arithmetic transform to the strict trait of a finite point and the compactified transform to the strict trait at `∞'`. Identify each with the shifted proper pushforward of the pulled-back extended kernel, and identify the generic restriction at `∞'` with that of the transform on `A'`. Prove compatibility with specialization, the group actions and the coefficient tower via the natural base-change map. |
| `KernelAcyclicity` · `FiniteFourierChartAcyclicityStatement`, `InfiniteFourierChartAcyclicityStatement` | Laumon (1.3.1.2), (2.3.2.1)(i), (2.3.3.1)(i). SGA 4½ *Th. finitude* Cor. 2.16. Katz–Laumon 1985 (2.4.2)–(2.4.4), pp. 157–160 | **New.** At a finite target, use the constant-family complex pulled back from the source over a field and tensor by the lisse kernel on `A`. For the infinite target, prove relative local acyclicity of the zero-extended Artin–Schreier kernel along `U × {∞'}`, where the original perverse input is lisse after a shift. Use the finite partial compactification of the Artin–Schreier torsor, its character splitting and the smooth and radicial factorization in Katz–Laumon. Check at invertible torsion levels, then compare with the adic model. The smooth unit and local acyclicity imports of §3.3 handle the applicable smooth pieces. |
| `IsolatedNearbyCycles` · `IsolatedNearbyCyclesSummandStatement` | Laumon Lemme (2.5.3.2), p. 167. SGA 7 XIII (2.1.7.1) | **New.** For a compactifiable map of finite-type trait models proper on the generic fibre, proper exchange applied with the zero-extended generic complex computes nearby cycles on the target by the special fibre. Split off the contribution of an isolated closed support point of that fibre. Retain the hypotheses of isolation, compactifiability and properness on the generic fibre for the tame chart. |
| `FourierFiniteCycles` · `FourierFiniteVanishingCyclesStatement`, `FourierFiniteCycleRankStatement` | Laumon (2.3.2), (2.3.2.1)(i)–(iii), (2.3.2.3)(i)–(ii), pp. 159–160 | **New.** Use `ArithmeticFourierTraitRestrictionStatement` at the finite target point before proper exchange on that strict chart. Finite-chart acyclicity reduces `RΦ` of the transform to the single source point at infinity. The perverse stalk triangle concentrates it in degree `−1` with the global convention `K` perverse and kernel shift `[1]`. Its dimension is the signed stalk rank minus the signed generic rank. Apply §2.3.1 to get `r(V_1)−s(V_1⊗Lψ(ax))` at `a ≠ 0`, and `r(V_{<1})−s(V_{<1})` at `0'`, for `V` the source monodromy at infinity. |
| `StationaryPhase` · `FourierInfinityStationaryPhaseStatement` | Laumon (2.3.3.1)(i)–(iii), p. 161. SGA 7 XIII (2.1.7.1) | **New.** Use `ArithmeticFourierTraitRestrictionStatement` at `∞'` to identify the transform's generic monodromy with the nearby cycles of the strict target pushforward. Apply proper exchange over that trait. The extended kernel has zero special restriction at `∞'`, so its nearby and vanishing cycles agree there. Infinite-chart acyclicity leaves the finite singular locus of `K` together with source infinity. The finite-support decomposition on the projective source gives the degree-`−1` target Galois representation as the direct sum of local contributions induced from the finite residue degrees, plus the contribution at infinity. Other cohomological degrees vanish. Preserve the decomposition under morphisms and the residue action. |

Let `S=Spec R` be the henselian target trait with fraction field `K'`
and separable closure `Ω_s`. Choose the special point through the
maximal unramified subfield `K^nr ⊂ Ω_s`. Its valuation ring `R^nr`
has residue field `k̄` and gives the pointed strict henselization
`S^nr`. At a rational end, take the colimit of `R ⊗_k k_d` for the
finite subfields `k_d ⊂ k̄`, with the embeddings into `K^nr` fixed.
Henselian lifting of the finite separable residue fields identifies
this tower with the pointed unramified tower. For a closed end of
larger residue degree use its residue field and choose the geometric
branch. The unique valuation extension and completion comparison of
(b2) match the restrictions of `G_{K'}` on `R^nr` and on `k̄`
with the Library residue action. Inertia is `Gal(Ω_s/K^nr)`.

For an arithmetic chart `X → S` with kernel complex `B`, form
`X^nr = X ×_S S^nr` and pull `B` back to `B^nr` on `X^nr`.
Take `j : X^nr ×_{S^nr} Spec Ω_s → X^nr` using `K^nr ⊂ Ω_s`
and `i : X^nr ×_{S^nr} Spec k̄ → X^nr`. A closed geometric stalk
at `x̄` is the cohomology complex of the generic fibre of the
strict localization `(X^nr)_(x̄)` over this same `S^nr`.
For bounded below finite coefficients of étale origin, compare
direct images and stalks with the small étale site, then use
exactness of sections on the strictly local scheme, where sections
are the closed stalk. The pullback square used for each pointed
source neighbourhood or strict localization has right edge `j` and
is Cartesian by base change from `Spec Ω_s → S^nr`. This gives the
strict-local formula of SGA 7 XIII, Proposition (2.1.4).

The base change of the arithmetic generic point to an unramified
stage of degree `d` has algebra `Ω_s ⊗_{K'} K_d ≅ ∏_d Ω_s`.
The chosen embedding `K_d ⊂ Ω_s` selects one factor at every
stage. Form `j` over `S^nr` with that embedding before taking the
direct image. On the identity trait, the strict-local generic
fibre is `Spec Ω_s`, so for the finite constant ring `Λ` its
cohomology complex is `Λ[0]`, with the trivial action.
Specialization sends each constant section to the same section,
and its cone is zero. The imported tensor-unit calculation for
`Spec k̄[[t']]` gives the same check on the complete strict trait.

For `σ ∈ G_{K'}`, its restriction to `R^nr`, its map on `Ω_s`
and its residue automorphism on `k̄` define compatible
automorphisms of the three spaces over the arithmetic chart.
The map `X^nr → X` identifies the pulled-back complex under the
total-space automorphism with `B^nr`. The pullback exchange therefore
gives an isomorphism from the pullback of `Ψ(B^nr)` along the
special-fibre automorphism to `Ψ(B^nr)`. The square law and
composition of the canonical pullback identifications give the
action law. At a rational special point the geometric lift is
preserved over the residue automorphism. The comparison with
condensed modules at a separably closed point in §3.3 identifies
pullback along this automorphism coherently with the identity on
coefficients, giving an action on the stalk. At other closed points
the action permutes the geometric stalks, with the decomposition
subgroup acting on each. Inertia
fixes `R^nr` and `k̄`. On the geometric generic fibre it acts
through the same model maps defining the fixed-special-fibre
`galoisLayerAction` over `K^nr`. This identifies the inertial part
of the full action used in the proof of continuity.

For a finite constant extension `k₁ ⊂ k̄`, the associated henselian
trait has fraction field `K₁ = K' k₁`. The two pointed strict
henselizations identify with `S^nr` and the generic and special
fibre diagrams identify over it. The geometric specialization
map is the same map under these identifications. Its arithmetic
action restricts to `Gal(Ω_s/K₁)`, the preimage of
`Gal(k̄/k₁)` under the residue map. Use the chosen branch in
the case of a nonrational closed point. Apply the same
identification to the Fourier kernels using the trace comparison
for `ψ` in §4.2.

For specialization, `B^nr` is an arbitrary complex on the
strict total space, and every Fourier chart has `e` the identity.
Use `twistSpecializationMap` with the canonical identification of
the two generic restrictions from `ε=j≫e`. On the tensor unit the
result agrees with `NearbyCyclesModel.unit` under the monoidal unit
identifications. The
pullback exchange for a square of generic maps is the mate of the
identification of their composite pullbacks. After composing with the
pulled-back specialization, take its adjoint along the new `j`. The
counit cancels the old unit and gives the identification of the generic
restrictions. This also characterizes the new unit and proves
commutativity on the special fibre. The proper exchange uses the same
unit identity with the counit for the total-space pushforward. Apply
these identities to model automorphisms and use the coefficient
exchange mates for reduction and coefficient extension. This gives
natural maps of specialization arrows on the actual complexes before
taking cofibers.

For a proper map of the strict charts, the squares of `i` and of
`ε=j` are Cartesian because both are base changes from the same
strict trait. Construct the proper exchange there and check it on
the bounded below étale-origin finite reductions. Use the pushforward
coefficient comparisons for `j`, the proper map and its special-fibre
map to identify the exchange at each reduction. Derived completeness
then gives the integral exchange, and the scalar comparisons for
these qcqs maps identify its rationalization with the `E`-exchange.
For standard complete models the direct `E`-coefficient theorem
applies with its Noetherian, closed and affine hypotheses.

To restrict the arithmetic transform at a finite target point `a`,
let `S_a` be its chosen strict target trait and `g_a : S_a → A'`
the strict localization map. Use the Cartesian square

```text
D × S_a  --g_a'-->  D × A'
   | q_a               | q
   v                   v
  S_a    --g_a--->    A'
```

Here `q_a` is the proper projection and `g_a'` is the pullback of
`g_a`. Both horizontal maps are weakly étale. Apply the ambient
base-change isomorphism to `B_K` and shift by `[1]` to obtain
`Lg_a* M_K ≅ (Rq_{a,*} Lg_a'^* B_K)[1]`. The special and the chosen
geometric generic restrictions in the specialization triangle
are those of this identification.

At infinity let `g_∞ : S_∞ → D'` be the strict localization,
formed in the affine chart with coordinate `1/x'`. The corresponding
Cartesian square is

```text
D × S_∞  --g_∞'-->  D × D'
   | q_∞               | q̄
   v                   v
  S_∞    --g_∞--->    D'
```

The same ambient theorem identifies the pullback of the compactified
transform `M̄_K = (Rq̄_* B̄_K)[1]` with
`(Rq_{∞,*} Lg_∞'^* B̄_K)[1]`. The generic point of `S_∞` maps into
`A'`. Along this open, the extension `B̄_K` restricts to `B_K` and
the weakly étale square of the two global projections identifies
`M̄_K` with `M_K`. Thus the geometric generic restriction of the
strict pushforward carries the actual global transform's monodromy
at `∞'`. At the closed boundary `Spec k → D'`, both bases of
the proper projection square are Noetherian over `k`, and the
extension `B̄_K` is bounded constructible. Proper base change
there sends its zero boundary restriction to the zero boundary
restriction of `M̄_K`. On the strict chart the zero special
restriction of the kernel gives the comparison of nearby and
vanishing cycles used in stationary phase.

Both restriction isomorphisms are the canonical
`baseChangeMap` applied to the extended kernel. For the Galois
action, paste the projection square with the square for an
automorphism of the strict target and its lift on the product.
The two composites of the exchange maps agree by the composition
law of derived pullback and the unit and counit identities for
adjunction mates. This intertwines the descent identifications
from the arithmetic schemes, including the maps on the geometric
generic and special fibres. Apply the naturality of
`nearbySpecialization` to the resulting isomorphism on the strict
target, so it identifies the two specialization arrows before
proper nearby-cycle exchange. The same mate identity and the
pushforward and pullback coefficient comparisons make the
identification compatible with finite reductions and rationalization.

For the generic-fibre comparison, let `K₀` be the fraction field of
the strict trait under consideration and choose an algebraic closure `Ω_a`.
Take `Ω_s` to be its subfield of separable elements over `K₀`. For
`K₀=K^nr` this is also a separable closure of `K'`, so use the original
choice of `Ω_s`. Write
`M_a`, `M_s` for the models obtained using `Ω_a`, `Ω_s`, with the same
total space and chosen geometric special fibre, and the same source.
The model map `M_a → M_s` has identity total-space, source and
special-fibre maps, and generic map `g` obtained by base change of
`Spec Ω_a → Spec Ω_s`. This map is a universal homeomorphism by pure
inseparability. The invertible exchange `Ψ_s → Ψ_a` of §3.3 respects the
arbitrary-input specialization since the adjunction unit for
`j_a=g≫j_s` is the composite of the units for `j_s` and `g`.

On the fixed strict target, every arithmetic `K'`-automorphism
of `Ω_s` extends uniquely to `Ω_a` by (b1), and the lifts commute
with `g`. They have the same restrictions on the strict trait and
on `k̄`. The square law for exchange intertwines the resulting
actions, with pullback along the residue automorphisms. The expression for
`Ψ_s → Ψ_a` as `Li*Rj_{s,*}` of the generic adjunction unit and
naturality of the coefficient-change mates identify its reduction
and scalar-extension squares.

For continuity, apply the direct strict-trait exchange along
`R^nr → k̄[[t']]`, with compatible algebraically closed generic
fields and the same special residue field. The total-space square
is pulled back along this inclusion and each geometric fibre is
formed over its own strict trait. Use the finite-coefficient
finiteness theorem on the resulting standard complete strict trait
at each `𝒪_L/ℓⁿ` level. Carry that constructibility back to the chosen
strict henselization and across `Ψ_s ≅ Ψ_a`. The actions for continuity
are the ones on `X^nr`. Now use the finite Galois
layers of the separable closure over the fraction field of the strict
henselian trait. The input on this base generic fibre has bounded
below étale origin and the generic inclusion before taking the
layers is qcqs. The geometric nearby cohomology is generated by
finitely many finitely presentable objects on the qcqs special fibre,
so the inertia continuity theorem of §3.3 applies to `RΨ_s`. For `RΦ_s`,
use the specialization on `X^nr` at each finite generic layer and its
compatibility with the layer maps from `nearbySpecialization`.
Exactness of filtered colimits and the nearby cohomology colimit
identify the cohomology of the geometric specialization cone with
the colimit of the finite-layer cone cohomologies. The image of a
finite layer on the stalk is fixed by the open inertia subgroup
fixing that layer.
A finite stalk is generated by the image of one such layer. For the
full action, choose an open normal subgroup in `G_{K'}` whose
intersection with inertia acts trivially on the finite stalk. Its
action then factors through an open subgroup of the procyclic residue
quotient, using `Langlands.Galois.FiniteField.profiniteEquivalence` in
`Langlands.Galois.FiniteField.ComparisonProof`. For a homomorphism
from that subgroup to a finite group,
multiplication by the image exponent gives an open subgroup of the
kernel. Thus the finite stalk action is continuous on `G_{K'}`.

For the passage to the adic stalk, use derived completeness of the
integral pullbacks and pushforward and of the specialization cone.
Its residue reduction is bounded constructible by finite-level
finiteness and the triangle, so apply the integral constructibility
criterion. Work at the geometric special stalk in the resulting
condensed module model using the equivalence at a separably closed
point in §3.3. Evaluate at the one-point profinite set, where covers
split, so evaluation is exact and preserves products. Compare the
evaluations at finite levels to the étale stalks. Apply the canonical
homotopy-limit cone to the integral stalk. The finite cohomology
groups of the reductions form Mittag–Leffler towers, so identify the
integral cohomology with the inverse limits of these finite modules
with their compatible Galois actions. Its quotient modulo the
uniformizer embeds into cohomology of the finite residue complex by
the reduction triangle. Lift a finite set of generators of that
quotient. Successive approximation with the uniformizer makes their
span dense for the inverse-limit topology. The span is compact, as
the continuous image of a finite free module over the complete
DVR, so it is the entire cohomology module. Compare the resulting
quotient topology with its adic topology. Invert `ℓ` and extend to
`E` by the rationalization comparison. Naturality under the
arithmetic maps identifies the resulting stalks of the actual
arithmetic `RΨ` and `RΦ`.

### 4.5 The three local functors and their vanishing ranges

| Module and Lean name | Source | Inputs and result |
|---|---|---|
| `LocalFourier` · `localFourierZeroInfinity`, `localFourierInfinityZero`, `localFourierInfinityInfinity` | Laumon Définition (2.4.2.3), p. 163 | **New.** First form the three local kernel complexes of §1 and their `R¹Φ` stalks. Use the following comparison and concentration statements for finite rank, continuity and exactness needed to bundle the functors, including in the exchanged direction. |
| `LocalFourierComparison` · `LocalFourierChartComparisonStatement`, `LocalFourierConcentrationStatement`, `LocalFourierExactStatement` | Laumon Lemme (2.4.2.1)(i)–(iii), Prop. (2.4.2.2), (2.5.1), pp. 162–165 | **New.** Over the same chosen strict target identify the global kernel on each pointed source chart with the local kernel using the coordinates, weakly étale exchange and the extension-by-zero squares and shifts. Apply the strict-trait exchange separately for comparison with complete traits. This is a comparison of `RΦ` for all three phases, before taking degree one. Use the canonical extensions or the tame extension as required to supply global representatives. Apply the finite and infinity results to prove support at the special pair and concentration in degree 1 in the unshifted convention. Use the cohomology sequence for short exact sequences of local modules to prove exactness. |
| `TraitSpecialization` · `TraitSpecializationTriangleStatement` | SGA 7 XIII (1.4.2)–(1.4.2.2), (2.1.1)–(2.1.2). Fu 2014, Lemma 4.1, pp. 112–113 | **New.** For an arithmetic bounded constructible complex `K` on the henselian origin trait with rational special point `i`, generic immersion `j`, and structural map `b` to `Spec k`, construct the natural specialization triangle `b* i* K → K → j_! RΦ_id(K) →`. Use the special and generic complexes with their Galois actions and the equivariant specialization map. Build the first map on compatible torsion complex models and compare their cones under reduction before passing to adic coefficients. Use the ambient open–closed triangle of §3.3 for the cone. |
| `LocalFourierComparison` · `LocalFourierOriginPhaseFromVanishingCyclesStatement` | Laumon (1.3.1.2), (2.3.3.1), (2.5.6). SGA 7 XIII (1.4.2.2). Fu 2014, Lemma 4.1, pp. 112–113 | **New.** For `K` the restriction of an arithmetic curve-perverse complex to the rational origin trait, identify the degree `−1` finite-origin phase in the Fourier transform at infinity with `F^(0,∞')(H⁻¹ RΦ_id(K))`. Inputs are the specialization triangle, vanishing cycles exchange and concentration, and infinite-chart acyclicity for the zero-extended Artin–Schreier kernel with a base-pulled coefficient complex. See the comparison below. |
| `LocalFourierBaseChange` · `LocalFourierConstantBaseChangeStatement`, `LocalFourierReflectionStatement` | Laumon (2.4.2.1)–(2.4.2.3), (2.5.2) and (2.5.6). SGA 7 XIII (2.1.1) | **New.** Use `StrictTraitConstantBaseChangeStatement` on the same strict target model, then the specialization cofiber and coefficient comparisons to show base change for all three functors as restriction of the arithmetic actions. Simultaneous negation of the two coordinates preserves the kernel, so compare source and target negation on stalks. |
| `LocalFourierBaseChange` · `NearbyBaseLineTensorStatement`, `VanishingBaseLineTensorStatement`, `LocalFourierBaseLineTensorStatement` | SGA 7 XIII (1.4.2.2), (2.1.1)–(2.1.2). Laumon (2.5.2), (2.5.6). Henniart §4.3 | **Import** `nearbyCyclesTwistIso` and monoidality of exchange from §3.3. Supply the dualizable line on the strict total space and the generic identification by pulling it back from the same arithmetic line. **New** equivariance, commutativity of the specialization square and compatibility with the coefficient tower. Pass to the cofiber and degree-one stalk to get S4, including the Tate twist used in inversion. |
| `LocalTameFourier` · `TameFourierGenericDirectImageStatement`, `TameFourierInfinityNearbyVanishingStatement` | Laumon (2.5.3.1)–(2.5.3.2), pp. 165–167. SGA 4½ *Th. finitude* Cor. 2.16, p. 243 | **New.** For a nontrivial Kummer character use the blow-up chart `(t,t') ↦ (tt',t')` to compute the generic direct image, including its target Kummer factor. Compare the geometric generic restrictions and evaluate the resulting nearby stalk by constant-family acyclicity in the product variable. Use the isolated-support lemma and the zero target special restriction to deduce the arithmetic `(∞,∞')` vanishing. |
| `LocalTameFourier` · `LocalFourierTameCharacterStatement`, `LocalFourierTameVanishingStatement` | Laumon (2.5.3.1)–(2.5.3.2), pp. 165–167, and (1.4.3.2)(iii) | **New.** Apply the finite and infinity comparisons to the constant and punctual formulas and to `KummerGaussFourierStatement`. For the trivial input the transforms are respectively `E`, `E(-1)` and zero. For a nontrivial Kummer character the first two are the corresponding `t'` Kummer line with Gauss factors `G(χ,ψ)` and `G(χ⁻¹,ψ)`, respectively, and the third is zero by the preceding chart calculation. For every tame module, apply the filtration theorem of §3.2 to the action of tame inertia and a Frobenius lift. After finite constant extension, the factors are Kummer characters times unramified lines, which are handled by S4. Exactness and geometric conservativity transfer the rank, tameness and vanishing tests back to `k`. |
| `LocalFourierSlopeVanishing` · `LocalFourierInfinityZeroVanishingStatement`, `LocalFourierInfinityInfinityVanishingStatement` | Laumon (2.5.4), p. 167, from (2.3.1.1)(i), (2.3.2.3)(ii), (2.3.3.1)(iii) and (2.4.2.1) | **New.** Globalize at `∞` with canonical extension tame at `0`. The finite-origin rank formula gives `F^(∞,0') = 0` on slopes `≥ 1`. For slopes `≤ 1`, compare the global generic rank with the tame-origin summand in the stationary-phase decomposition and prove `F^(∞,∞') = 0`. Include the exchanged form of both statements. |

For the line comparison, write `W` for the base line pulled back to
the strict total space and `T` for the same line on the source.
The local triviality and inverse line supply the evaluation and
coevaluation for `W` at each coefficient level. Pullback from the
base gives `Lε*T ≅ Lj*W`, and `Li*W` has the residue action of the
original line. Apply `nearbyCyclesTwistIso` to the input `A`.
Under this comparison, `nearbySpecialization` for `A ⊗ T`
becomes specialization for `A` tensored with `Li*W`. Before the
special pullback, take the adjoints of the two maps under
`Lj* ⊣ Rj_*`. Both are the same tensor comparison of generic
restrictions. The monoidality
of pullback exchange and the specialization naturality of §4.4
intertwine the arithmetic action, including the action on `W`.
The same diagram commutes with the coefficient changes. Tensoring
by the invertible line preserves the cofiber, which gives the
vanishing-cycle comparison and the corresponding twist of local
Galois representations.

For the finite-origin comparison, identify `Rb_*K → i*K` at each
finite level by taking the colimit of sections over pointed finite
unramified neighbourhoods. On the chosen strict henselization these
sections compute the closed stalk, by the strict-local sections
comparison of §3.3. This identification respects the residue action.
Use its inverse and the adjunction for `b` to obtain `b* i* K → K`.
Its two restrictions are the identity at the closed point and the
specialization map on the chosen geometric generic point, with the
full arithmetic action from §4.4. The cone has zero special restriction, and its generic
restriction is the cone of specialization, namely `RΦ_id(K)` on `η`.
The localization map identifies the cone with its generic extension by
zero. Keep the residue action on `i* K` in this construction.

On `T ×_k T'`, tensor the pulled-back triangle with the kernel extended by
zero at `t'=0`, with the global Fourier shift `[1]`. All three terms have
zero special restriction on the target, so nearby and vanishing cycles
agree. The contribution of the first term `b* i* K` vanishes by infinite-chart
local acyclicity for the lisse-along-source coefficient, using the strong
torsion form for the pulled-back coefficient complex. Thus the arithmetic
map from `K` to `j_! RΦ_id(K)` induces the isomorphism of finite-origin
phases. Compare the three terms and their maps on the compatible reductions.
For perverse `K`, `RΦ_id(K)` is concentrated in degree `−1`. Its shift and
the kernel shift convert the degree `−1` stationary-phase stalk on the
right into the degree `1` stalk defining the local functor on
`H⁻¹ RΦ_id(K)`. This comparison applies when the intermediate Fourier
transform has a nonzero stalk at the origin. Its origin stalk participates
in the specialization map, which accounts for the difference between nearby
and vanishing cycles there.
[Fu 2014, Lemma 4.1](https://intlpress.com/site/pub/files/_fulltext/journals/mrl/2014/0021/0001/MRL-2014-0021-0001-a008.pdf)

For the tame infinity calculation take `t=1/x` and `t'=1/x'`. Let
`h(t,t')=(y,t')=(tt',t')` be the affine chart of the blow-up mapping the
compactifiable chart to `𝔸¹_y × T'`. On the generic fibre `h_η'` is an
isomorphism and the kernel becomes `Lψ(1/y)`. Since `t=y/t'`, the generic
direct image of the original zero-extended input kernel is
`pr_y* (j_{y,!}(K_χ(y) ⊗ Lψ(1/y))) ⊗ pr_{η'}* K_χ(1/t')`, where
`j_y` is the inclusion `y ≠ 0` on the `y`-line. Use the multiplicative
Kummer identity to obtain this formula over the target generic point.

On a geometric generic fibre, the pullback of `K_χ(1/t')` is the
constant sheaf of its one-dimensional geometric stalk. On underlying
nearby stalks, the generic direct image therefore gives the nearby
stalk of the constant family in `y` tensored with this one-dimensional
space. This comparison uses the generic pullback in `RΨ`, before
`Rj̄_*`, and can be made after trivializing the line there. Apply
constant-family local acyclicity to the pullback of
`j_{y,!}(K_χ(y) ⊗ Lψ(1/y))` from the `y`-line. At `y=0` the source
zero extension has zero stalk. The underlying nearby stalk of the
generic direct image at `(0,s')` thus vanishes. The original kernel
has zero special restriction on `T'`, and infinity-chart acyclicity
makes the source point `(∞,s')` isolated in its nearby support in the
special fibre of `h`. Lemme (2.5.3.2) makes its geometric nearby stalk a
direct summand of the zero stalk just computed. Use geometric
conservativity to deduce vanishing on the arithmetic model. This
argument only tests vanishing after the generic trivialization. The
arithmetic target Kummer line retains its Galois action in the original
generic formula.
[Laumon 1987, (2.5.3.1)–(2.5.3.2)](https://www.numdam.org/item/PMIHES_1987__65__131_0/)

### 4.6 Numerical comparison and assembly

| Module and Lean name | Source | Inputs and result |
|---|---|---|
| `LocalFourierRankSwan` · `LocalFourierZeroInfinityRankSwanStatement` | Laumon (2.5.5), pp. 167–169, for (2.4.3)(i) b) | **New.** For the canonical extension `F` tame at infinity, compare `M = FTψ(j_!F)` with `F^(0,∞')(V)` at `∞'` by stationary phase and the tame vanishing of `F^(∞,∞')`. From the global rank formula `M` has rank `r+s` on `𝔾_m`, signed origin rank `s` and tame monodromy at `0'` from the finite-cycle and tame calculations. The arithmetic origin fibre and reflected double transform give `RΓ_c(Ā',M)=0` because the input origin stalk vanishes. Apply GOS on `𝔾_m` with its two boundary terms and the origin stalk of `M` to get Swan `s` at `∞'`. Use the rank and Swan identities here independently of any slope restriction on the image. |
| `LocalFourierInverse` · `LocalFourierLeftCompositionStatement`, `LocalFourierExchangedCompositionStatement` | Laumon (2.5.6), p. 169, using (1.2.2.3), (2.3.2.1), (2.3.3.1), (2.4.2.1), (2.5.3)–(2.5.4) | **New.** Apply the finite-origin cycle comparison to the reflected double transform of `j_!F`, and identify the relevant source monodromy at its infinity by stationary phase. This gives `a* F^(∞',0) F^(0,∞')(V)(1) ≅ V` naturally for every `V`. For `W` at `∞'` of slopes `< 1`, extend canonically to `A'−{0'}` with tame monodromy at `0'`. The first global transform on `A` of this extension by zero has finite-origin vanishing cycles `Y = F^(∞',0)(W)` and tame monodromy at `∞`, by the finite-origin comparison and the infinity slope vanishing. In the second global transform at `∞'`, the tame infinity phase vanishes. The finite-origin phase is `F^(0,∞')(Y)` by `LocalFourierOriginPhaseFromVanishingCyclesStatement` applied to the intermediate perverse transform. The reflected double-transform formula identifies this phase with `a'* W(-1)`, giving `a'* F^(0,∞') F^(∞',0)(W)(1) ≅ W` over `k`. |
| `LocalFourierInverse` · `LocalFourierSlopeLessThanOneStatement`, `LocalFourierEquivalenceStatement` | Laumon (2.4.3)(i) b)–c), (ii) b), (2.5.4)–(2.5.6). Companion source map §3 | **New.** With `W=F^(0,∞')(V)` split `W=W_<1 ⊕ W_≥1`. The reverse transform kills `W_≥1`. Set `Y=F^(∞',0)(W_<1)`. The left composition identifies `V` with the reflected Tate twist of `Y`, and the exchanged composition identifies `W_<1` with the reflected Tate twist of `F^(0,∞')(Y)`. Use the rank formula on `V` and `Y`, and invariance of rank and Swan under reflection and Tate twist, to require equal dimensions of `W` and `W_<1`. The separate vanishing of `W_≥1` then allows bundling the equivalence on the `<1` full subcategory. Reflection transport and S4 for the Tate line put both compositions in terms of the same quasi-inverse. Exact slope projectors show this subcategory is closed under subquotients, so the equivalence identifies its simples with the irreducible representations in it. |
| `SwanComparison` · `TransportedLadicSwanStatement` | Laumon (2.1.2.5)–(2.1.2.6), Serre IV §3 and VI §2, Henniart §4.1–4.2 | **New.** Use the Library's finite-inertia and irreducible Weil-transport inputs at `ℓ ≠ p`, actual finite inertia presentations, scalar invariance of the fixed dimensions, and weighted break, refinement and Artin identities as in b3. Prove the equality of the slopes' Swan sum and the predicate `LadicHasSwan` for arbitrary `ι`, including the unramified case, and deduce invariance under `ι` and twists. This part can be proved as soon as §4.1 and the conductor inputs are available. |
| `TwistBijectionProof` · `Langlands.Henniart.laumonLadicTwistBijection` | Laumon (2.4.3)(i) b)–c), (2.5.2), (2.5.5)–(2.5.6), (2.6.2), Henniart §4.3 | **New proof of the prescribed statement.** Transport the two completed ends to `X` by the coordinate `t` and match constants. Use (b1), the local equivalence and rank/Swan to map an irreducible Galois class in the first subtype to the second. For a class in the second subtype, comparison with `s(V)` gives its single slope `s/(d+s)<1`, and the inverse yields rank `d` and Swan `s`. Pass to quotient classes and produce the two subtype inverse identities. S4 on the underlying representations gives the equation with `Langlands.Henniart.LocalNumerical.ladicUnramifiedTwist`, and b3 supplies the requested Swan proof for the twisted source class. |

The first composition and the exchanged composition on slopes `<1` involve
different boundary calculations. The rank and Swan identities alone control
the average slope. The dimension comparison in §4.6 is the separate step
needed before using the essential image of the equivalence in the numerical
bijection.

### 4.7 Interfaces shared with other parts of the Library

- The ramification layer for local fields of either characteristic owns the
  upper filtration, its finite quotient and inertia comparisons, finite
  presentations and conductor invariance, and the finite-inertia slope
  calculation. The absolute-to-finite upper image is proved by
  `Langlands.Ramification.Wintenberger.localAbsoluteUpperFiniteImage` in
  `Langlands.LocalFactor.Ramification.Wintenberger.Absolute` as in §4.1.
  For finite representations and their conductors, use the results of
  the interfaces `Langlands.Ramification.Local.WeilBreakComparisonStatement`
  and `Langlands.Ramification.Local.InertiaSurjectivityPresentationAndConductorIndependenceStatement`
  in `Langlands.LocalFactor.Ramification.LocalWeilBreakStatement` and
  `Langlands.LocalFactor.Ramification.LocalInertiaPresentationStatement`,
  respectively. The general statements are present at the Library pin.
  Their equal-characteristic proofs and the equal-characteristic conductor
  integrality needed here remain dependencies. The geometry uses them
  through the ℓ-adic projectors and the Swan comparison.
  [Conductors and ramification](../local-factors/conductors-and-ramification.md)

- Work over `LaurentSeries k` with `Langlands.LocalField.Laurent.valuativeRel`,
  `Langlands.LocalField.Laurent.localField`,
  `Langlands.LocalField.Laurent.powerSeriesEquivIntegers` and
  `Langlands.LocalField.Laurent.residueEquiv` in
  `Langlands.LocalField.LaurentSeries`. The residue group and inertia are
  `Langlands.LocalGalois.SepClosed.absoluteResidueHom` and
  `Langlands.LocalGalois.SepClosed.absoluteInertia` in
  `Langlands.Galois.Local.AbsoluteDefinitions`. Use also
  `Langlands.LocalGalois.SepClosed.absoluteResidueQuotientEquiv` in
  `Langlands.Galois.Local.ResidueProjectionQuotient`. The group, projection,
  degree and inertia equivalence are
  `Langlands.Weil.Local.SepClosed.localWeilGroup`,
  `Langlands.Weil.Local.SepClosed.localProjection`,
  `Langlands.Weil.Local.SepClosed.localDegree` and
  `Langlands.Weil.Local.SepClosed.localGaloisInertiaEquiv` in
  `Langlands.Weil.Local.Assembly`. These fix the group on which the sheaf
  comparisons land.

- Use the existing class operations in
  `Langlands.Correspondence.HenniartLadicClasses` and the Weil-side strata
  `Langlands.Henniart.LocalNumerical.weilRefinedStratum` in
  `Langlands.Correspondence.HenniartLocalNumerical`. The separate inputs
  `Langlands.Henniart.LadicFiniteInertiaStatement` and
  `Langlands.Henniart.LadicWeilTransportStatement` provide the two class-side
  prerequisites of `TransportedLadicSwanStatement`. The numerical reduction
  `Langlands.Henniart.LaumonNumericalReductionStatement` consumes the bijection
  together with `Langlands.Henniart.LadicWeilOrbitComparisonStatement` to
  obtain `Langlands.Henniart.LaumonNumericalStatement`. The complex
  finite-image dictionary `Langlands.Henniart.WeilGaloisDictionaryStatement`
  belongs to that orbit comparison. These interfaces name the dependencies
  of the proof and of its numerical consumer.

## 5. Lean feasibility checks

Private `lean_check` probes in the pinned environment compiled together
with the Library's `Langlands.MathlibBase`,
`Langlands.Correspondence.HenniartLadicClasses`, and
`Langlands.LocalField.LaurentSeries`. The external declarations used here
are in §§3.2–3.4, with their defining modules and axiom lists.

- Over `Spec (LaurentSeries k)`, the affine scheme instances allow
  `AlgebraicGeometry.ProEtale.universalLisseMonodromy_isEquivalenceAt` at the
  algebraic-closure point. For an arithmetic lisse sheaf, compose its
  `AlgebraicGeometry.ProEtale.LisseMonodromy.rep` with
  `AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut` and a supplied lift of
  automorphisms from the separable to the algebraic closure. Lean bundles
  the result using `Langlands.FiniteRepresentation.of` with the exact
  group `SeparableClosure X ≃ₐ[X] SeparableClosure X`, and both the Library
  continuity and finite-extension predicates type-check on it. The probe
  supplies the lift as data. The group-topology comparison and the proofs
  of the two predicates are obligations of `LadicFieldMonodromyStatement`.
  Independently, `IrreducibleLadicClass` at this field and separable closure
  elaborates with arbitrary carrier universe and the local valuative
  relation installed.

- The Krull-topology Galois group of `SeparableClosure (LaurentSeries k)`
  over `LaurentSeries k` has the compactness instance. On an arbitrary
  bundled `Langlands.FiniteRepresentation` of this group, Lean checks both
  Library predicates and instantiates `Representation.isLAdic_iff_continuous`
  using `InfiniteGalois.profiniteGalGrp` and the action by linear
  equivalences from the bundled representation. The equivalences between
  its joint continuity and finite model and the two Library predicates
  are the coordinate comparisons of b1.

- On `AlgebraicGeometry.affineLine k`, take the basic open where its
  coordinate is invertible. Lean synthesizes that its inclusion is
  quasi-compact and over `Spec k`. It also supplies `IsAffine` for the
  basic open and elaborates the Weil descent theorem there with smoothness
  and irreducibility supplied. Geometrically the open is smooth and
  irreducible as a nonempty open of the smooth integral affine line.
  For a Weil sheaf on that open,
  `AlgebraicGeometry.WeilSheaf.extensionByZero` followed by
  `AlgebraicGeometry.WeilSheaf.toComplex` and
  `AlgebraicGeometry.fourierTransform ψ` gives an actual
  `AlgebraicGeometry.WeilComplex` on the line.

- Over the same affine line, `AlgebraicGeometry.AffineSpace.isPullback_map`
  identifies the actual second projection with a relative affine line
  over the target. Transport
  `AlgebraicGeometry.affineTraceLineCompactification` with
  `AlgebraicGeometry.Compactification.precomp` and
  `AlgebraicGeometry.Compactification.copy`. With this compactification
  and the character mapped by `Profinite.PadicAlgCl.constRingHom`,
  `AlgebraicGeometry.ProEtale.condensedFieldFourierTransform` elaborates.
  Lean composes it with
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification`
  of the basic open immersion, compactified by the identity proper part
  via `AlgebraicGeometry.Compactification.ofIsOpenImmersion`. This gives
  the ambient arithmetic transform of the zero-extended input. The
  bounded constructible restriction, Frobenius-compatible comparison and
  rank and lissity results are the propositions of §4.2.

- For the proper projection in `AlgebraicGeometry.affineTraceLineCompactification`
  over the affine target, Lean constructs the pullback square along
  `AlgebraicGeometry.Scheme.strictLocalizationToBase` at a geometric
  point. It uses the weakly étale instance on that map and the
  pullback instance on the source to check invertibility of the
  ambient `AlgebraicGeometry.ProEtale.CondensedRing.baseChangeMap`
  with `Profinite.padicAlgClRingObj`. This is the projection
  comparison used on the strict target in §4.4.

- For an arbitrary Weil complex and integer `r`, a probe obtains the
  Frobenius-module equivalence at the origin from
  `AlgebraicGeometry.nonempty_equiv_stalk_homologySheaf_fourierTransform_origin`.
  Its projection `FrobeniusModule.Equiv.toLinearEquiv` gives equality
  of the `E`-dimensions of the degree-`r` stalk and of degree `r+1`
  compact-support cohomology. This is the linear input to the signed
  Euler-characteristic calculation in §4.2.

- In the complete strict point-trait probe the residue field `κ` is
  separably closed. Lean checks that specialization of the finite
  condensed coefficient unit is invertible in
  `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.traitGenericModel κ`
  using `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_unit_traitGenericModel`.
  Starting with the point model for `κ[[t]] → κ((t))` and
  `κ[[t]] → κ`, the probe instantiates
  `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.galoisLayerAction`
  for an automorphism of `SeparableClosure (LaurentSeries κ)` over
  `LaurentSeries κ`. This tests the fixed-special-fibre action used
  for inertia. The separate probe with
  `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.ofTraitHom`
  forms a morphism from three compatible ring automorphisms of
  a trait and its generic and special field maps. Lean checks the
  invertible exchange for that morphism over the special automorphism.
  `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.affineSpaceModel`
  and `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.geometric`
  also give the degree-one relative affine-space example.

- A complete point-trait probe, parameterized by the residue field `κ`,
  uses the separable subfield inside
  `AlgebraicClosure (LaurentSeries κ)` and fixes the total space and
  special fibre for both generic choices. Lean builds the model morphism
  with generic map induced by the field inclusion. It checks the
  invertible exchange using
  `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isUniversalHomeomorphism_generic`
  and accepts the unit of
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`
  for the separable generic map at an arbitrary complex on the total
  space. The equivariance, specialization, scalar and strict-trait
  compatibilities on the Fourier charts are specified in §4.4.

- On the complete strict point trait with the total space as source
  and `ε=j`, Lean elaborates
  `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.twistSpecializationMap`
  at an arbitrary complex using the identity generic identification.
  It also checks
  `AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.nearbyCyclesTwistIso`
  with the second complex assumed dualizable. The probe uses finite
  discrete condensed coefficients. The arithmetic and cofiber
  comparisons for a pulled-back line are specified in §4.5.

- On that relative affine-line model over the standard complete strict
  trait, Lean synthesizes finiteness of the quotient `𝒪_L/ℓⁿ` for a
  finite ℓ-adic extension, and elaborates the nearby-cycles functor with
  `Profinite.integersModPowRingObj`. The comparison
  `AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedLowerStarIntegersModPowReduction`
  specializes to the actual generic-inclusion morphism of that model.
  The identifications of the specialization and action maps with those
  of the reduction tower are in §4.4.

Use `Langlands.MathlibBase` in the import closure of modules that use
weil-conjectures. The Mathlib umbrella includes three conflicting modules.
The source and import rule are recorded in the
[repository roots note](../library/roots-and-import-rule.md#weil-conjectures-and-langlandsmathlibbase)
and the [MathlibBase documentation](../../Langlands/MathlibBase.md).

## 6. Source editions

Printed locators throughout refer to the following retained copies. The
SHA-256 values identify the files used for the source comparison.

- Laumon 1987, `laumon-1987-fourier-weil`,
  `c666e214ae586651b9f171f6a39d755e58f96379970ffa98bafb2d9be591fc8e`.
  §§1.2–1.4 and 2.1–2.5, pp. 141–169, and (2.6.2), p. 172.
  [Publ. Math. IHÉS 65](https://www.numdam.org/item/PMIHES_1987__65__131_0/)
- Henniart 1988, `henniart-1988-numerical`,
  `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
  §§4.1–4.3, pp. 509–511.
  [Ann. Sci. Éc. Norm. Supér. 21](https://www.numdam.org/item/ASENS_1988_4_21_4_497_0/)
- SGA 7 XIII, `deligne-1973-sga7-xiii-cycles-evanescents`,
  `898f984a6010f8088537f6cb3d4fe9d8b20d5a4ffb43e258f613dc35e97f7b2a`.
  (0.2.5), (1.3.2.1)–(1.3.2.2), (1.4.2)–(1.4.2.2),
  (2.1.1)–(2.1.4), (2.1.7.1).
- SGA 4½, `deligne-1977-sga4-half-cohomologie-etale`,
  `fb2939521f4c0ea0cdd55a90bec2e618e32fb433c78b194e705c6d989f4e42a6`.
  *Th. finitude* Cor. 2.16, Thm. 3.2 and Prop. 3.7, and *Sommes trig.*
  (4.3), (4.20).
- Katz 1986, `katz-1986-local-to-global-extensions`,
  `de5a870ed52f6b0c66235cb4a5e6a3c4158b89ea8bd7f77f977b63d95694057b`.
  §§1.2–1.5, especially Thms. 1.4.1 and 1.5.6 and Cor. 1.4.10.
  (2.3.7)–(2.3.8) for the pro-`p` comparison criteria.
  [Ann. Inst. Fourier 36](https://www.numdam.org/articles/10.5802/aif.1069/)
- Raynaud, `raynaud-1965-bourbaki-286-euler-poincare`,
  `fd0cf10b653f40e43f2ef7211fed427b7c5c80022c42bedecbf1544b050baa40`.
  §§1–4, especially §3 Thm. 1 and §4 Lemmas 1–2.
  [Séminaire Bourbaki 286](https://www.numdam.org/item/SB_1964-1966__9__129_0/)
- Serre, `serre-1979-local-fields`,
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
  II §§3–4, III §§3, 6–7, IV §§1–3 and VI §2.
- Katz 1983,
  `provided-dfb1ff840caee48a9ec4bf735fc5417d1d5b55a59e5f27ad4fe2755bb24fede5`,
  `d7a7450db266b9e7d795c72941efb9d79e9b91a847af51cace77f6be4f665db7`.
  *Wild ramification and some problems of independence of ℓ*, pp. 211–215.
- Katz–Laumon 1985, `katz-laumon-1985-fourier-sommes-exponentielles`,
  `13395f500749855ac1e3156ab833b505bbfcadaae4089babb5877b960cea9475`.
  (2.1.3) and (2.4.2)–(2.4.4), printed pp. 154, 157–160.
  [Publ. Math. IHÉS 62](https://www.numdam.org/item/PMIHES_1985__62__145_0/)
- Beilinson–Bernstein–Deligne,
  `provided-830095b3f7fe74814d46089e979bcae5137893f26af277d16110ec2fb4bcaf5f`,
  `b1e10440e13cb6bf307f74030b577e0cf5056e41b35ca56640dc2f0d2109b9e0`.
  *Faisceaux pervers* (4.0) and (4.3.1), pp. 101–103, 112.
- Fu 2014, `fu-2014-thom-sebastiani-characteristic-p`,
  `566da1f0c1998db71563e92075a273db8059febb393983ba42e91fa12568aaba`.
  Lemma 4.1, pp. 112–113, gives the equivariant specialization-triangle
  argument for the finite-origin phase in Laumon (2.5.6).
  [Mathematical Research Letters 21](https://intlpress.com/site/pub/files/_fulltext/journals/mrl/2014/0021/0001/MRL-2014-0021-0001-a008.pdf)
- The seven E1b items and bridges b1–b4 are in the external-inputs plan
  `operator-external-inputs-plan-2026-11-16`, `external-inputs-plan.tex`
  §4.1, lines 470–497,
  `816bb31b7194dea7eb38a661bf53ae670c17a2ec0bd7d1e7e4bcfa2c94aad03a`.
