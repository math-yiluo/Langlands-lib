# Renard S19: the chosen special compact subgroup and actual standard Levis

This focused source map supplements [the Chapter V ledger](chapter-v-structural-inputs.md),
row S19. It records the actual objects needed for V.5.1(2),(3),(5), the
boundedness comparison, and the remaining corrected-building requirements.
It does not prove the structural assertions.

## Sources and scope

The original sources read for this map are:

- Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026
  edition, `renard-2026-representations-groupes-reductifs-padiques`, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
  V.5.1, printed page 122 / PDF page 128. The source states one adapted
  maximal compact open subgroup with all five properties. The minimal
  parabolic inside a standard Levi is the intersection with the same
  ambient chosen minimal parabolic.
- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Definition 1.3.39, Lemma 1.3.42 and Proposition 1.3.43 (PDF60–61);
  Definition 2.2.1 and Fact 2.2.3 (PDF101); Notation 2.6.15,
  Lemma 2.6.16 and Remark 2.6.18 (PDF133–134); Axioms 4.1.2,
  4.1.4 and 4.1.6 and Definition 4.1.3 (PDF189–191);
  Theorem 4.2.15 and Example 4.2.16 (PDF204–205); proof of
  Theorem 5.2.1 (PDF218).
- Kaletha–Prasad, corrections of 1 November 2024,
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  the Henselian convention in Section 2.2 and the positive character
  valuation in Sections 2.5–2.6 (PDF24–25); corrected Section 4.1,
  including the full axiom list in Definition 4.1.26 (PDF27–28);
  the additional AS5 assumption in Chapter 7 and its general proof
  dependency (PDF33).

There is no restriction to characteristic zero, split, unramified or
quasisplit groups. The intended field hypotheses are `Field F`,
`ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`.
Fix an actual connected reductive group scheme `G/F`, a chosen maximal split
`i : S.toGrp ⟶ G`, and a generic cocharacter `ν`. Standard indices are all
`J ⊆ simpleRelativeRoots i ν`, including the empty index set.

## One apartment point and one subgroup

For `D : KPApartmentData i (localFieldOrder F)` and `x : D.Apartment`, write

```text
K₀ = D.specialCompactSubgroup x
   = rationalCommonNormKernel G ∩ D.reducedFixer (D.apartmentMap x).
```

`D.IsSpecialApartmentVertex x` means geometric specialness and vertexhood
in the same affine-root apartment. Specialness says that every affine-root
hyperplane has a parallel affine-root hyperplane through `x`; it is not
defined by a desired property of `K₀`. The apartment remains an affine
torsor without a chosen origin.

The formula uses the actual common rational-character valuation kernel
`G(F)^1`. The full reduced fixer may be larger. The source parahoric `P_x`
is the facet stabilizer inside `G(F)^0`; the required inclusion is
`P_x ≤ K₀`, and equality is not imposed. An actual construction of `G(F)^0`
and of `P_x`, with the comparison to this same building action, is still
needed before the inclusion can be supplied. A sharp-fixer inclusion alone
does not identify the actual parahoric.

All standard indices must use this same `D`, `x` and `K₀`. Separate
existence assertions with independently chosen compact subgroups do not
supply the common witness needed by the decomposition and basis consumers.

## Source-to-declaration map

The namespace abbreviations used in this table are
`KP = Langlands.Geometry.Building.KPApartmentData`,
`GS = Langlands.GroupScheme`, and `Std = GS.Standard`.
Publication status is recorded separately below; a named proposition target
is not a proof.

| Source clause | Actual declarations and required conclusion |
| --- | --- |
| Chosen subgroup | `KP.IsSpecialApartmentVertex` and `KP.specialCompactSubgroup`; membership is `mem_specialCompactSubgroup`. `specialCompactSubgroup_le_reducedFixer` and `specialCompactSubgroup_le_rationalCommonNormKernel` give its two defining inclusions. Compactness, openness, maximality and existence remain structural conclusions. |
| S19(2), Renard V.5.1(2) | `KP.specialCompactNormalizer` is the actual normalizer restricted to `K₀`; `KP.specialCompactWeylMap` is its map to `GS.relativeWeylGroup i`. The required assertion is surjectivity of this map. Its denominator is the actual centralizer `Z_G(S)(F)`, rather than just `S(F)`. KP Lemma 1.3.42 and corrected AS5 are the geometric source route; the proof of KP Theorem 5.2.1 even gives representatives in the parahoric. |
| S19(3), Renard V.5.1(3) | Use `GS.standardParabolicPoints i ν J`, `GS.standardLeviPoints i ν J` and `GS.standardUnipotentPoints i ν J` in the same ambient `GS.rationalPoints G`. The required identity is `(K₀ ∩ P_J(F) : Set G(F)) = (K₀ ∩ M_J(F)) * (K₀ ∩ U_J(F))`, with the right side the literal pointwise set product. No abstract product object or replacement subgroup supplies that identity. |
| S19(5), actual Levi and torus | `Std.leviScheme`, `Std.leviHom` and `Std.leviTorusHom` fix the actual closed Levi, its inclusion and the factor of the same torus. `Std.leviTorusHom_comp` recovers the original `i`, and `Std.isMaximalSplitTorus_leviTorusHom` retains maximal splitness. |
| S19(5), chosen compact intersection | `KP.specialCompactLeviSubgroup ν J x` is the preimage of the same `K₀` along the actual Levi inclusion on points. `KP.specialCompactLeviSubgroup_map` identifies its ambient image with the literal `K₀ ∩ M_J(F)`. `Std.leviPointsEquiv` supplies the actual rational-point comparison. |
| S19(5), minimal parabolic | `GS.StandardLeviMinimalParabolicCompatibilityStatement` asks for actual Levi reductivity, ambient and intrinsic minimal parabolicity, the all-test pullback identity and the literal rational-point image intersection, uniformly in the same `i,ν,J`. The intrinsic subgroup is `Std.leviGenericParabolic`. Its all-test comparison with the ambient dynamic parabolic is proved by `Std.leviGenericParabolic_eq_comap_dynamic`. The comparison with the chosen standard minimal parabolic and its point-image formula are `Std.leviGenericParabolic_eq_comap_standard` and `Std.leviGenericParabolic_points_map`, under the explicit standard endpoint equality. |

The all-test minimal-parabolic target refines Renard's rational-point
formulation using actual subgroup functors and closed Levi representations.
The refinement is derived content, not a claim that the quoted source proves
scheme-level minimality. `IsMinimalParabolicFunctor` requires representation
by an actual parabolic over `F` and compares rational parabolic functors on
every test scheme. Rational-point minimality alone is insufficient.

The remaining geometric part of S19(5) must construct inherited actual
root-valuation/apartment data for each actual Levi, compare evaluations with
the ambient roots, and identify its special compact subgroup with the same
`specialCompactLeviSubgroup`. It must also supply compactness, openness,
maximality, Weyl representatives and the compact-parabolic product within
each Levi. Renard's S19(5) additionally includes Iwasawa and Cartan inside
Levis; those belong to the sibling decomposition targets. This focused
compact-subgroup program does not replace them.

## Explicit boundedness and topology

All names in this paragraph lie in
`Langlands.AlgebraicGeometry.PointTopology`. The public
`IsAlgebraicallyBounded F X B` tests every global regular function on an
actual affine scheme `X/F`, using `rationalPointAlgebraHom`. Each function
has a uniform nonzero valuative upper bound on its evaluations, equivalently
a finite lower bound in the source's additive valuation convention. Zero
evaluations remain included.

`AffineBoundedCompactnessProperty F` states the corrected source comparison:
a nontrivially valued rank-one field with its valuation topology, Henselian
valuation ring and local compactness; an actual finite-type affine scheme;
and a **closed** subset of its rational points. Under those hypotheses
algebraic boundedness is equivalent to compactness. The target installs
`rationalPointTopology F X`, the named canonical evaluation topology.
`LocalFieldAffineBoundedCompactnessProperty F` states the full local-field
specialization without an additional characteristic or Henselian premise.
Both declarations are proposition targets, not proved compactness theorems.

KP Axiom 4.1.2 supplies boundedness and openness of `G(F)^1_x` in valid
building data. KP Theorem 4.2.15(1), including its proof, makes this subgroup
maximal among bounded subgroups when `x` is a vertex. For the local-field
compact version the comparison, finite-type scope and closedness must be
available. Example 4.2.16 explains why a general maximal bounded subgroup
need not fix a vertex when `G(F)^0 ≠ G(F)^1`; it does not contradict the
vertex conclusion used here.

## Validity, existence and publication boundary

The source's corrected Definition 4.1.26 requires Axioms 4.1.1, 4.1.2,
4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22.
A weak `KPApartmentData`, or a partial predicate adding full V6, V7, AS2
and the first AS5 Weyl inclusions, does not establish all those axioms.
In particular, the first AS5 inclusions do not supply its additional special
clauses, nor do they construct `G(F)^0` or the actual parahoric.

The general existence target must quantify over every actual connected
reductive `G/F` and produce actual corrected building/root-valuation data,
a special vertex and the displayed `K₀`. A conditional assertion on supplied
valid data is an additional target. Even an existential weak `D,x` satisfying
desired compact-subgroup conclusions does not by itself establish existence
of fully corrected data. This gap remains visible when combining the compact,
Iwasawa, Cartan and simultaneous-basis targets at one witness.
An existence assertion using only the partial validity predicate is likewise
a supplementary target; documenting its omitted axioms does not supply the
full corrected-data existence assertion.

Status at this note's preparation, Library base
`538f554630aa4cd24a084e698b1768d7143ba586`:

- `AffineBoundedness` and `AffineBoundedCompactnessStatement` are published.
  Their definition and statement candidates are respectively
  `b31bd296-8ab2-4602-a798-1504d338f9f3` and
  `0ae60ec4-96de-4f6c-ad6b-f008211ee531`. Publication of the latter supplies
  target propositions, not proofs of the comparison.
- `SpecialCompact` and `SpecialCompactLevi` are submitted adapters,
  candidates `4d9f8fd2-8bb8-4d20-8f21-472d4815a11f` and
  `5fd70f2e-3088-4f40-9cc4-817d845d7007`. Both have terminal machine
  acceptance and independent semantic approval, and await Library
  publication.
- `SpecialCompactLeviMinimalParabolicStatement` is submitted statement
  candidate `64640483-edf8-4cf0-b0c8-6382e5c55171`. Its comparison adapters
  compile, and the exact global declaration was inspected as returning
  `Prop`. Machine validation is accepted; independent semantic acceptance
  and publication remain pending.
- The compactness/existence, Weyl-surjectivity, literal product,
  inherited-apartment, actual-parahoric inclusion and common-witness
  obligations have not been discharged by those focused units. This note
  is not a completion declaration for their host task.

Author: Worker 1229. The original Chapter V ledger is Worker 164's source
audit; this map uses the original Renard and KP passages independently and
preserves that ledger's structural and in-book proof boundaries.
