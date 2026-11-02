# KP Bundle A: source ledger and construction boundaries

This is the initial source ledger for Bundle A of the standing KP program
`f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703`. It records mathematical source targets,
not completed formalization. Every formal-status field below is empty: no
accepted, published Lean result for these complete targets has been verified in
this ledger. The other bundles still require their own original-source audits.

The normative sources are Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, and the
authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`. Both readable originals are in
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.
Their fingerprints and precise locators are included in every relevant row.
The operator roadmap is design guidance, not theorem evidence.

## Reading and scope

The original passages behind these rows were read at PDF pages 34–40, 161–163,
188, 199–205 and 213–215, together with corrections PDF pages 1–3, 25 and 27–29.
Book PDF pages 35–36 and 202 were visually checked. In particular, the overbar
in Theorem 4.2.10 matters: the closed union is a union of **facet closures**.
The OCR text alone drops that overbar. The theorem does not require the building
to be locally finite; that is only the first case in its proof.

The Chapter 4 targets are consequences of specified building axioms. They do
not supply a general reductive-group building construction. The program still
requires the descended construction and every corrected axiom in its
Theorem 9.2.7 certificate. None of the source-only rows below closes that boundary.

## Structured ledger

The JSON block is the structured ledger. Each row has the same fields.
`lean_declarations`, `modules`, acceptance, publication and trust reports stay
empty until their exact results have been verified. An owner task records an
obligation; it is not evidence of its fulfillment. Conditional code will remain
`conditional` until its missing instance is constructed.

```json
{
  "schema_version": 1,
  "program_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
  "coverage": "Bundle A named targets only; further bundle rows remain to be source-audited.",
  "status_convention": "A null formal_status means no verified Lean declaration of this target is recorded. Non-null values are definition, statement, proved or conditional; acceptance and publication are separate mandatory evidence.",
  "rows": [
    {
      "source_item": "Proposition 2.11.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.130–131 / PDF pp.161–162"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.25, Section 2.11",
        "change": "Notation corrections to P_G(lambda), U_G(lambda), Z_G(lambda) and the corresponding H-subgroups."
      },
      "hypotheses": [
        "A is a commutative unital ring; G is an affine A-group scheme with a G_m-action by group-scheme automorphisms, denoted lambda. Conjugation by a cocharacter is an instance.",
        "Part (4): H is a closed G_m-stable subgroup scheme of G.",
        "Part (5): A is a field, G and H are connected of finite type, and G→H is a faithfully flat surjective equivariant homomorphism.",
        "Part (6): G is of finite type over A."
      ],
      "conclusion": "Representability of P and U as closed subgroup schemes, with U normal in P; Z=P(lambda)∩P(-lambda); compatibility with arbitrary base change and stable closed subgroups; induced quotient maps in (5); unipotence of U fibres in (6).",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Dynamic orbit extension from G_m to A^1; schematic subgroup functors; equivariant quotient maps"
      ],
      "consumer_or_regression": "General valued root-group and integral-model inputs; compare the existing GL_n dynamic instance.",
      "formal_status": null,
      "owner_task": "2b5e4a00-9d44-49a4-9c89-979fb5b6233e",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 2.11.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.131 / PDF p.162"
      },
      "erratum": null,
      "hypotheses": [
        "The affine A-group scheme G with its G_m-action is of finite presentation.",
        "Connectedness of P and Z fibres in (2) additionally assumes connected G fibres."
      ],
      "conclusion": "P,U,Z are finitely presented; U has connected fibres; the stated Lie algebras are the zero and positive weight spaces, with Lie(P)=Lie(G)_0 ⊕ Lie(G)_+; multiplication gives the stated semidirect decomposition with ordered factors Z and U.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 2.11.1; weight decomposition; Lie algebras; semidirect products"
      ],
      "consumer_or_regression": "Compare the ordered Z/U product to the GL_n block-Levi construction and later root-group models.",
      "formal_status": null,
      "owner_task": "2b5e4a00-9d44-49a4-9c89-979fb5b6233e",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 2.11.3",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.131–132 / PDF pp.162–163"
      },
      "erratum": null,
      "hypotheses": [
        "G is a smooth affine A-group scheme of finite presentation with the G_m-action.",
        "The open immersion is an isomorphism when A is a field and G is connected and solvable.",
        "Part (3) additionally assumes G is a reductive group scheme.",
        "Part (4) assumes A is a field."
      ],
      "conclusion": "Z,P,U are smooth; multiplication U(-lambda)×P(lambda)→G is an open immersion; P is parabolic and U its unipotent radical in the reductive case; U is split over a field.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Propositions 2.11.1–2.11.2; smoothness; scheme-theoretic open immersion; reductive groups"
      ],
      "consumer_or_regression": "General big-cell input to building/root-group constructions. GL_n or split-only results remain intermediate instances.",
      "formal_status": null,
      "owner_task": "2b5e4a00-9d44-49a4-9c89-979fb5b6233e",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 1.1.15",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.6–7 / PDF pp.37–38"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.1–2, Section 1.1",
        "change": "Convex subsets are nonempty; geodesic hypothesis restored in the convex-ball/hull discussion; in the theorem proof take positive epsilon<r and a nonnegative approximating epsilon sequence."
      },
      "hypotheses": [
        "X is a complete nonpositively curved geodesic metric space.",
        "Part (1): M⊆X is nonempty, bounded, closed and geodesically convex.",
        "Part (2): M⊆X is nonempty and bounded; it need not itself be closed or convex."
      ],
      "conclusion": "Part (1): M has a unique barycenter, fixed by every isometry carrying M onto itself. Part (2): the setwise stabilizer of M in the isometry group has a fixed point in X.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Definitions 1.1.2, 1.1.4, 1.1.8, corrected 1.1.12, and 1.1.14; Lemmas 1.1.11 and 1.1.13; completeness"
      ],
      "consumer_or_regression": "Bounded isometric actions (Corollary 1.1.19), then the constructed-building instance and Corollary 4.2.14.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 4.2.7",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.170 / PDF p.201"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.28–29, Section 4.2",
        "change": "Add Axiom 4.1.6 to the opening hypotheses; the metric of Proposition 4.2.1 is G-invariant and the apartment-independence argument is corrected."
      },
      "hypotheses": [
        "k has a discrete valuation, its valuation ring is Henselian and its residue field is perfect; G is connected reductive over k.",
        "B is the Chapter 4 building satisfying Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9, with the compatible Weyl-invariant Euclidean apartment metrics of Section 4.2."
      ],
      "conclusion": "The apartment metric on B satisfies the midpoint nonpositive-curvature inequality of Definition 1.1.8.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Section 4.2 metric; apartment midpoints; retractions and their nonexpansion/distance laws; Euclidean parallelogram identity"
      ],
      "consumer_or_regression": "Theorem 1.1.15 applied to the actual constructed building after Theorem 4.2.10.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 4.2.10",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.171–172 / PDF pp.202–203"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.28–29, Section 4.2",
        "change": "Add Axiom 4.1.6 to the opening hypotheses; the metric of Proposition 4.2.1 is G-invariant and the apartment-independence argument is corrected."
      },
      "hypotheses": [
        "k has a discrete valuation, its valuation ring is Henselian and its residue field is perfect; G is connected reductive over k.",
        "B is the Chapter 4 building satisfying Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9, with the compatible Weyl-invariant Euclidean apartment metrics of Section 4.2."
      ],
      "conclusion": "B is complete; for every collection of facets, the union of their CLOSED facets (the closures of those facets) is closed. Local finiteness is not a hypothesis of the theorem.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Section 4.2 metric; Lemma 4.2.11 and discrete affine-root hyperplane spacing; compact closed chamber"
      ],
      "consumer_or_regression": "Fixed-point theorem on the constructed building; finite-residue and non-locally-finite cases must not be conflated.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Corollary 4.2.14",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.173 / PDF p.204"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.28–29, Section 4.2",
        "change": "Add Axiom 4.1.6 to the opening hypotheses; the metric of Proposition 4.2.1 is G-invariant and the apartment-independence argument is corrected."
      },
      "hypotheses": [
        "k has a discrete valuation, its valuation ring is Henselian and its residue field is perfect; G is connected reductive over k.",
        "B is the Chapter 4 building satisfying Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9, with the compatible Weyl-invariant Euclidean apartment metrics of Section 4.2.",
        "H is a bounded subgroup of G(k), with boundedness in the algebraic sense of Definition 2.2.1.",
        "For the second assertion, H preserves a nonempty closed convex subset Y of B; Y need not be bounded."
      ],
      "conclusion": "H fixes a point of B, and fixes a point in Y when such a preserved Y is specified.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Theorem 1.1.15; Proposition 4.2.7; Theorem 4.2.10; Proposition 4.2.13 relating algebraic boundedness and bounded action"
      ],
      "consumer_or_regression": "Actual parahoric/fixer and compact-subgroup consumers, retaining the reduced/enlarged and G(k)^0/G(k)^1 distinctions.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 4.4.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.182–183 / PDF pp.213–214"
      },
      "erratum": null,
      "hypotheses": [
        "k has a discrete valuation, Henselian valuation ring and perfect residue field; G is connected reductive over k.",
        "B satisfies Axioms 4.1.1, 4.1.4 and 4.1.9. S is a maximal k-split torus, N its normalizer, and A its associated affine apartment."
      ],
      "conclusion": "The G(k)-equivariant map (g,x)↦g·x from G(k)×A onto B has fibres given by (g,x)~(h,y) iff some n∈N(k) has n·x=y and g^(-1)hn∈G(k)_x. The full stabilizer can be replaced by G(k)^natural_x or an intermediate subgroup, subject to the source comparison.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Apartment conjugacy; transporter to the normalizer; point stabilizers; Proposition 4.4.3 for the affine apartment conventions"
      ],
      "consumer_or_regression": "Actual building quotient presentation; conditional algebraic quotient child cd3fd695-b511-4653-8f4d-769e99d8aab0 supplies only a reusable prerequisite.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Corollary 4.4.5",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.183–184 / PDF pp.214–215"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.29, Section 4.4",
        "change": "Replace the existential pair by EVERY corresponding pair and remove the intervening such-that wording."
      },
      "hypotheses": [
        "B1 and B2 are buildings for the same G satisfying Axioms 4.1.1, 4.1.4 and 4.1.9; A1 and A2 correspond to the same maximal k-split torus.",
        "For EVERY pair x1∈A1 and x2∈A2 corresponding under the canonical affine isomorphism of Proposition 4.4.3, G(k)^0_(x1) is a subgroup of G(k)^0_(x2).",
        "The field and reductive-group conventions are those of Chapter 4 (discrete valuation, Henselian valuation ring, perfect residue field, connected reductive G)."
      ],
      "conclusion": "The canonical apartment isomorphism extends uniquely to a G(k)-equivariant building isomorphism B1→B2; corresponding facet subgroups G(k)^0_F agree.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Propositions 4.4.3 and 4.4.4; apartments containing point pairs; facet recovery from stabilizers"
      ],
      "consumer_or_regression": "Regression must reject a single-pair replacement for the universal hypothesis; quotient surjectivity alone does not establish the building isomorphism.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    }
  ]
}
```

## Initial interfaces and the next mathematical gates

Metric definition child `bd4b31f8-44f8-447c-b747-e26d93a271d1` has a staged
candidate `3baeb443-a6c3-4cdf-9ef8-cce5431d3585`, authored by Worker 1221.
At the parent's fetch, its machine validation passed, while semantic acceptance
and publication were still false. Its proposed module is
`Langlands.Geometry.Metric.KPDefinitions`, namespace
`Langlands.Geometry.Metric.KP`. It uses a primitive midpoint inequality and
separates geodesic existence, completeness, convexity and barycenters. Its
radius and joint diameter take values in the extended nonnegative reals; the
finite real readings require explicit boundedness and nonemptiness. The
candidate does not supply the fixed-point theorem. These are staged-interface
pointers, to be rechecked after publication before dependent statements are opened.

The corrected convexity predicate must exclude the empty set. Theorem 1.1.15
requires actual existence and uniqueness of a barycenter, including radius-zero
cases, and a fixed point of every bounded isometric group action (Corollary
1.1.19). Supplying a fixed point as input would not establish those conclusions.
The building application must then prove completeness and nonpositive curvature
of the constructed building.

Derived quotient child `cd3fd695-b511-4653-8f4d-769e99d8aab0` asks for the actual
algebraic quotient, its group action, apartment embedding criterion and exact
stabilizer formula from an explicit covariant subgroup family. It also asks for
comparison maps under a universally quantified subgroup inclusion. This is a
conditional construction prerequisite. A parahoric family and the full quotient
point stabilizer need not coincide. The child must retain the normalizer's
point stabilizer, exhibit a proper-containment example, and avoid inferring a
building isomorphism from quotient surjectivity alone.

The existing algebraic-group program
`2b5e4a00-9d44-49a4-9c89-979fb5b6233e` owns dynamic parabolics, centralizers,
unipotent groups and general algebraic open cells. Its published
`Langlands.GroupScheme.Dynamic.Basic` interface is a reuse input, not by itself
a proof of every assertion of Propositions 2.11.1–3. General open cells require
the source's scheme-theoretic open immersion, beyond an assumed product map or
a split matrix instance. A verified reuse bridge remains required for the complete
source targets in the ledger.

The common field interface remains Mathlib's `IsNonarchimedeanLocalField`.
`Langlands.LocalField.ResidueNormalization` and the existing canonical
`Langlands.PadicField` realization are reuse inputs. Field child
`1453f721-e7ff-4221-87e1-6921dfa200e4` asks for an actual Laurent-series fixture
over every finite field, residue and normalization comparisons, negative
monomial calculations and a characteristic-two test. Its publication as a task
supplies no field theorem. Generic topologies and compact/open integral-point
results remain owned by Conrad program
`886bf565-95e9-4dc6-8a9d-73284a523668`; the KP program constructs its specific
models and later proves the comparisons.

## Trust and release accounting

The host environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. No external project is
adopted by this note. The roadmap's external pins remain survey leads. Any
adoption still requires a focused host compile, a mathematical and dependency
audit, and its exact pin and licence. No theorem-level axiom report is asserted
for an unproved target.

Bundle A is open. Bundles B–F, the general constructed instance, the depth-zero
and positive-depth consumers, regression examples, GL comparisons and Renard
bridges are also open. This source ledger neither narrows those obligations nor
claims that the proposed Chapter V structural interfaces have already been
published in the Renard program.
