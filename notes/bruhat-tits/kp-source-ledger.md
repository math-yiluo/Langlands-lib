# KP Bundles A–C: source ledger and construction boundaries

This source ledger covers Bundle A, initial Bundle B targets and Bundle C of the standing KP program
`f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703`. It records mathematical source targets,
not completed formalization. Every formal-status field below is empty: no
accepted, published Lean result for these complete targets has been verified in
this ledger. The remaining Bundle B targets and Bundles D–F still require public ledger entries. Private source audits and unsubmitted drafts are not publication evidence.

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

For the initial Bundle B extension, the original-source audit also covered book
PDF pages 188–197, 266–267, 280–292, 307, 353–360 and 393–399, and
corrections PDF pages 27, 30–41. Axiom 4.1.22 at PDF page 195 was visually
checked to distinguish the special fibre from its maximal reductive quotient.
The extension has three new rows: corrected Definition 4.1.26, Theorem 7.5.3
and Theorem 9.2.7. Source references in the assembly map below are dependencies
of those rows; they are not additional completed formal targets.

The Bundle C extension adds eleven source-only rows for the Iwahori–Weyl
quotient, Cartan and Iwasawa decompositions, the replaced Lemma 5.3.5,
Iwahori factorization, all four corrected Theorem 7.8.1 clauses, and the
narrow component/Kottwitz interfaces in Sections 11.5 and 11.7. Its source
audit covered book PDF pages 133–136, 217–222, 261–263, 286–288, 292–293,
299–304, 451–456 and 460–465, and corrections PDF pages 24–25, 30, 33–36
and 42–46. Book PDF page 465 was visually checked for the placement of
invariants and the torsion-free quotient notation. This extends the ledger
to twenty-three rows without assigning a formal status to any new target.

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
  "coverage": "Bundle A named targets, initial Bundle B targets (corrected Definition 4.1.26, Theorem 7.5.3 and Theorem 9.2.7), and Bundle C decompositions and narrow component/Kottwitz interfaces. Remaining Bundle B items and Bundles D–F still need public rows.",
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
    },
    {
      "source_item": "Definition 4.1.26",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.165 / PDF p.196; axioms at printed pp.157–164 / PDF pp.188–195"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.27, Section 4.1",
        "change": "Replace the definition's shorter axiom list by 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22. AS3 includes the identity in U_psi and U_psi+; 4.1.8(2) requires a nonempty bounded subset; 4.1.9 uses the restricted building and its corrected parabolic wording."
      },
      "hypotheses": [
        "The Chapter 4 ambient conventions are a discretely valued field k with Henselian valuation ring and perfect residue field, and a connected reductive k-group G. Finiteness of the residue field is not required.",
        "Building, apartment, action, root-group and integral-model data must satisfy all ten listed axioms. This is a definition of availability, not an existence assertion or permission to assume these data at the general endpoint."
      ],
      "conclusion": "Bruhat–Tits theory is available precisely when every axiom in the corrected ten-item list holds. In the program, the general constructed instance must also satisfy unramified descent Axiom 4.1.27; a conditional package of axioms alone does not meet that requirement.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22, with the corrections applied",
        "Source construction map 4.1.28 and Chapter 9; see the certificate map below for the separately derived 4.1.16 route and the full isomorphism scope of 4.1.17"
      ],
      "consumer_or_regression": "Theorem 9.2.7 certificate on the descended instance; tests must retain parahoric/full-fixer, reduced/enlarged and special-fibre/reductive-quotient distinctions.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 7.5.3",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.260–261 / PDF pp.291–292; Chapter 7 hypotheses at printed pp.235–236 / PDF pp.266–267"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.33 and 35, Chapter 7 and Section 7.5",
        "change": "Add AS5 of Axiom 4.1.6 to the Chapter 7 hypotheses. The proof of 7.5.1 uses AS5 for the affine Weyl identification; its saturation intersection is over conjugates n I n^(-1). Corrections to 7.5.2 use Z' and the preimage of I^sharp intersect Z(k)."
      },
      "hypotheses": [
        "k has a discrete valuation omega with Henselian valuation ring and omega(k^times)=Z, as stipulated outside Section 7.10. The residue field need not be perfect.",
        "G is connected reductive. To each maximal k-split torus S is assigned an affine apartment A(S), an equipollence class of root-datum valuations in the sense of 6.1.2 and 6.1.7, with the normalizer action of 6.1.8 and the equivariance required by Axiom 4.1.4.",
        "AS5 of Axiom 4.1.6 is assumed in addition. For general G, valuations and AS5 are not constructed merely by stating the Chapter 7 hypotheses; in the perfect-residue setting Chapter 9 supplies them.",
        "Write N=N_G(S) and Z=Z_G(S). Fix a chamber C in A(S), I=G(k)^0_C and the wall reflections R. The two ambient groups are G(k)^0 and G(k)^natural, with N intersected with the respective group. As in Section 7.5, I^natural=I^sharp Z^natural, where Z^natural is the image of Z'(k)^0 and Z' is the inverse image of Z in G_sc."
      ],
      "conclusion": "The two tuples (G(k)^0,I,N(k) intersect G(k)^0,R) and (G(k)^natural,I^natural,N(k) intersect G(k)^natural,R) are saturated Tits systems. Their Weyl groups identify with the affine Weyl group of Psi through the apartment action. Choices of torus and chamber give systems conjugate under G(k)^natural. This statement does not replace either ambient group by full G(k).",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Chapter 6 affine roots, valuation and normalizer action; corrected AS5 assumption",
        "Theorem 7.5.1, Lemma 7.5.2 and Lemma 1.4.12; Section 7.4 parahoric construction and Corollary 7.4.9",
        "For the general perfect-residue construction: Proposition 9.4.35, Theorem 9.6.5 and the every-point comparison in 9.6.6"
      ],
      "consumer_or_regression": "Restricted building construction 7.6.1 and the affine part of later double-coset decompositions. A nontrivial length-zero/component example must retain the full Iwahori–Weyl data separately.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 9.2.7",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.329 / PDF p.360; construction 9.2.1–9.2.6 at PDF pp.354–360; assembly 9.5 at printed pp.363–364 / PDF pp.394–395"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.27 (corrected Definition 4.1.26), pp.39–41 (Section 9.2 and Section 9.3); Chapter 7 AS5 addition at p.33",
        "change": "Read availability against the corrected ten-axiom definition, rather than the shorter printed theorem list. The corrected finite-Gamma-orbit argument uses a finite Galois unramified splitting extension; the added bounded-Gamma-stable-subgroup fixed-point argument uses Theorem 1.1.15. Proposition 9.3.12 uses a bounded subset contained in an apartment. The replacement 9.3.25 proof distinguishes restricted from full Tits buildings."
      },
      "hypotheses": [
        "k is discretely valued with omega(k^times)=Z and Henselian valuation ring o; its residue field is perfect. G is any connected reductive k-group. No global splitness, quasi-splitness, tame splitting or finite-residue hypothesis is imposed.",
        "K is the maximal unramified extension in a fixed separable closure, O its valuation ring, and Gamma=Gal(K/k). Corollary 2.3.8 makes G_K quasi-split; its building and models are the actual Chapter 6–8 constructions, not assumed general existence data.",
        "B is B(G_K)^Gamma with the restricted metric. Apartments are Gamma-fixed apartments attached to special k-tori of 9.2.2. Facets are intersections with Gamma-stable K-facets as in 9.2.4. Models are the smooth affine o-models descended in 9.2.5, with their relative identity components."
      ],
      "conclusion": "B with these apartments and polysimplices is a building whose apartments correspond bijectively to maximal k-split tori. Chambers and facets are fixed parts of Gamma-chambers and Gamma-facets, and G(k) acts by polysimplicial isometries. For the program's certificate, the constructed geometry and descended models must satisfy every axiom of corrected Definition 4.1.26 and Axiom 4.1.27, using the source assembly and the explicitly derived completion routes below.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Quasi-split Chapter 6–8 building and actual integral models; Corollary 2.3.8; descent Fact 2.10.16; special k-tori Proposition 9.3.4",
        "Complete NPC fixed-point theory (Theorem 1.1.15), corrected 9.2.1; geometry and restricted-building arguments of Sections 9.3–9.4, including corrected 9.3.25 and AS5 Proposition 9.4.35",
        "Axiom-by-axiom source map in Section 9.5, expanded below; for 4.1.16 use Sections 9.6 and 7.3–7.4 with corrected every-point Corollary 4.4.5",
        "For 4.1.17, Proposition 7.9.5 and transport of the descended construction under all covering field/group isomorphisms; a Gamma action alone is not the full axiom",
        "G(k)^0=G(K)^0 intersect G(k) (9.3.24) and the G(k)^1 intersection identity; model base change and root compatibility for Axiom 4.1.27"
      ],
      "consumer_or_regression": "Release 1 general-instance certificate, then actual parahoric reduction, inflation and compact induction. Check anisotropic and torus reduced/enlarged factors, a multipliable root and a nontrivial component example. A Gamma-chamber or Gamma-vertex need not be a K-chamber or K-vertex.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Definition 6.6.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.230–231 / PDF pp.261–262"
      },
      "erratum": null,
      "hypotheses": [
        "G is a connected reductive group over the discretely valued Henselian field k. S is a maximal k-split torus, N=N_G(S), Z=Z_G(S); Z(k)^0 and Z(k)^1 are the source subgroups, not arbitrary choices.",
        "For comparisons with affine actions, use the Chapter 6 root-valuation apartment and affine root system. Constructing this data for general G is a separate obligation."
      ],
      "conclusion": "The Iwahori–Weyl group is Wtilde^0=N(k)/Z(k)^0. Keep the distinct quotient Wtilde^1=N(k)/Z(k)^1 and the affine Weyl group W_aff generated by affine root reflections. The maps Wtilde^0→Wtilde^1→Wtilde_ad need not be injective; the affine action can lose component or central data.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Definitions 2.6.15 and 2.6.23 and the torus/centralizer subgroup comparisons",
        "Chapter 6 affine roots and normalizer action for the comparison maps; 6.6.2 in the quasi-split case and corrected 7.5.1 with AS5 for the general Wtilde_sc≃W_aff comparison"
      ],
      "consumer_or_regression": "Theorem 7.8.1 and Hecke indexing beyond simply connected split groups. Regression must distinguish the actual quotient from its affine image.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 5.2.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.187–188 / PDF pp.218–219, including (5.2.1) and corrected (5.2.2)"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.30, Section 5.2; valuation signs at PDF pp.24–25",
        "change": "Reverse the inequality in (5.2.2). In the apartment step of the proof remove appeals to 1.5.13(1) and 4.1.9, retaining Proposition 4.2.24. The corrections also remove the minus signs from omega_T and omega_G."
      },
      "hypotheses": [
        "k is discretely valued with Henselian valuation ring and perfect residue field; G is connected reductive over k. S is a maximal k-split torus, A its apartment in the actual Bruhat–Tits building, N=N_G(S) and Z=Z_G(S). These are the Chapter 5 ambient hypotheses.",
        "Fix a positive system Phi^+ and a special vertex x∈A, with parahoric P_x. Define Z_dom⊆Z(k) by a(omega_Z(z))≥0 for every a∈Phi^+. Use the corrected positive valuation homomorphism of Sections 2.5–2.6."
      ],
      "conclusion": "G(k)=P_x Z_dom P_x, and for all z,z'∈Z_dom, P_x z P_x=P_x z' P_x if and only if z' z^(-1)∈Z(k)^0. Corrected (5.2.2) expresses dominance as omega(a(z))≥0. This indexes dominant centralizer elements modulo Z(k)^0; a universal dominant-cocharacter parametrization is not asserted.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Special-vertex geometry, affine Bruhat decomposition, Axiom 4.1.2, Proposition 4.2.24 and Corollary 2.6.28",
        "Corrected valuation signs in Sections 2.5–2.6; for a relative character a, evaluate a(z) by extending a positive multiple to Z and dividing its valuation by that multiple"
      ],
      "consumer_or_regression": "General special-parahoric Hecke double cosets, with a proved GL_n Cartan comparison and distinctness of the associated compactly supported functions.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 5.3.3",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.188–190 / PDF pp.219–221"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.30, Section 5.3",
        "change": "Replace the argument in the proof identifying the relevant open-cell intersections: M_a is a cocharacter centralizer and its open-cell factors are cocharacter-stable; apply 4.1.16 through those factors."
      },
      "hypotheses": [
        "k is discretely valued with Henselian valuation ring and perfect residue field; G is connected reductive over k. S is a maximal k-split torus, A its apartment in the actual Bruhat–Tits building, N=N_G(S) and Z=Z_G(S). These are the Chapter 5 ambient hypotheses.",
        "Choose positive relative roots and let U be the unipotent radical of the corresponding minimal parabolic, with Levi Z. C is any chamber of A and P_C its Iwahori subgroup."
      ],
      "conclusion": "G(k)=U(k) N(k) P_C. No special-vertex condition is imposed on C. This product equality supplies the surjectivity part of the later U\\G/I indexing theorem; injectivity uses replaced Lemma 5.3.5.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Rank-one groups M_a and Lemmas 5.3.1–5.3.2; Iwahori decomposition Axiom 4.1.16; algebraic Bruhat decomposition",
        "Corrected cocharacter-centralizer and stable open-cell argument, rather than the printed closed-subgroup compatibility shortcut"
      ],
      "consumer_or_regression": "Corrected Theorem 7.8.1(4), followed by actual double-coset and compact induction computations.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 5.3.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.190–191 / PDF pp.221–222"
      },
      "erratum": null,
      "hypotheses": [
        "k is discretely valued with Henselian valuation ring and perfect residue field; G is connected reductive over k. S is a maximal k-split torus, A its apartment in the actual Bruhat–Tits building, N=N_G(S) and Z=Z_G(S). These are the Chapter 5 ambient hypotheses.",
        "x is any special vertex in B(G), P_x its parahoric, and P is any parabolic k-subgroup of G. P and P_x denote different kinds of objects."
      ],
      "conclusion": "G(k)=P(k) P_x=P_x P(k). The vertex must be special; the parabolic need not be the initially chosen minimal one.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Theorem 5.3.3 with its corrected proof",
        "Specialness and the normalizer-to-finite-Weyl surjection; conjugacy of minimal parabolics; inversion for the second product equality"
      ],
      "consumer_or_regression": "Parabolic induction and Jacquet structural bridges, retaining the special-parahoric and parabolic hypotheses.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Lemma 5.3.5",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.191 / PDF p.222; statement and proof replaced by corrections PDF p.30"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.30, Section 5.3",
        "change": "Replace the entire printed statement and proof by the Iwahori normalizer criterion n∈U(k)n'P_C iff n'n^(-1)∈Z(k)^0."
      },
      "hypotheses": [
        "k is discretely valued with Henselian valuation ring and perfect residue field; G is connected reductive over k. S is a maximal k-split torus, A its apartment in the actual Bruhat–Tits building, N=N_G(S) and Z=Z_G(S). These are the Chapter 5 ambient hypotheses.",
        "Use the notation of Theorem 5.3.3: U is the chosen minimal-parabolic unipotent radical, C is any chamber of A and P_C its Iwahori. n,n' range over all elements of N(k)."
      ],
      "conclusion": "n∈U(k) n' P_C if and only if n' n^(-1)∈Z(k)^0. The printed statement with an arbitrary bounded subgroup P is replaced and is not the target.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Iwahori decomposition for the translated chamber C'=nC",
        "Algebraic Bruhat/open-cell uniqueness forces n' n^(-1) into Z(k), then the Iwahori intersection identifies Z(k)^0"
      ],
      "consumer_or_regression": "Actual injectivity of the map in corrected Theorem 7.8.1(4); a surjective Iwasawa product alone cannot establish this conclusion.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Corollary 7.4.9",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.257 / PDF p.288; sharp/parahoric definitions at PDF pp.286–287"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.33, opening Chapter 7 hypothesis addition",
        "change": "The Chapter 7 setup additionally assumes AS5 of Axiom 4.1.6. There is no direct replacement of the Corollary 7.4.9 formula."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z and Henselian valuation ring. G is connected reductive. The Chapter 7 root-datum valuations, equipollent apartments, normalizer actions and Axiom 4.1.4 equivariance are supplied, together with AS5 of Axiom 4.1.6 added by corrections PDF p.33. Perfect residue is not assumed for this conditional Chapter 7 setup.",
        "C⊂A is a chamber, x∈C and Phi^+ is any positive relative-root system. Products use non-divisible roots. For the first product take r=0 or r=0+.",
        "For the facet form, F lies in the closure of C and Phi^+ contains Phi_F(C)^+ from Proposition 1.3.35."
      ],
      "conclusion": "N_x^sharp=Z_x^sharp and G(k)_C^sharp=(product over Phi^-,nd of U_{a,x,r}) Z_x^sharp (product over Phi^+,nd of U_{a,x,r}). In the facet form replace the negative factors by U_{a,F,0+} and positive factors by U_{a,F,0}. This is the sharp subgroup; the full parahoric is Z(k)^0 G(k)_C^sharp by 7.4.1.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Lemma 7.4.7; triviality of the affine-Weyl stabilizer of an interior chamber point; Proposition 7.3.12 and 6.3.21",
        "Arbitrary-order fixed-sign root-factor bijections are in 7.3.12(3),(5). Full-parahoric ordered bijections additionally use the central Z(k)^0 factor and algebraic open-cell injectivity; the added mixed all-root 7.3.12(6), requiring f(0)>0, is not the depth-zero argument"
      ],
      "consumer_or_regression": "Iwahori factorization with order and intersection laws; compare the Library GL_n factorization and a multipliable-root example.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 7.8.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.272–273 / PDF pp.303–304; part (4) added at corrections PDF pp.35–36"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.33 and 35–36, Chapter 7 and Theorem 7.8.1",
        "change": "Add AS5 to the chapter hypotheses. Replace the insufficient injectivity proof of (2) by component cancellation followed by Bruhat injectivity. Add assertion (4) and its 5.3.3/5.3.5 proof."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z and Henselian valuation ring. G is connected reductive. The Chapter 7 root-datum valuations, equipollent apartments, normalizer actions and Axiom 4.1.4 equivariance are supplied, together with AS5 of Axiom 4.1.6 added by corrections PDF p.33. Perfect residue is not assumed for this conditional Chapter 7 setup.",
        "S is a maximal k-split torus, N and Z its normalizer and centralizer, Wtilde^0=N(k)/Z(k)^0, and W_aff is the affine Weyl group. C⊂A is a chamber and I=G(k)^0_C. For part (3), F_1,F_2 lie in the closure of a common chamber and W_aff_Fi is the affine-Weyl facet stabilizer.",
        "For the source route to added part (4), also retain the Chapter 5 perfect-residue building hypotheses used by 5.3.3 and replaced 5.3.5. U is the unipotent radical of a minimal parabolic containing S, with Levi Z. Any broader residue-field version needs a separate proof."
      ],
      "conclusion": "(1) Exact sequence 1→W_aff→Wtilde^0→G(k)/G(k)^0→1. (2) Inclusion induces a bijection Wtilde^0→I\\G(k)/I. (3) Inclusion induces a bijection W_aff_F1\\Wtilde^0/W_aff_F2 →G(k)^0_F1\\G(k)/G(k)^0_F2. (4) Inclusion induces a bijection Wtilde^0→U(k)\\G(k)/I=U(k)Z(k)^0\\G(k)/I. These are actual quotient bijections, including the component contribution beyond W_aff.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Fact 4.1.25, corrected Theorem 7.5.3 and Proposition 7.5.5",
        "Corrected (2) injectivity: use 7.8.2 and Lemma 1.3.17 to write w_i rho_i, use (1) and I⊂G(k)^0 to identify the rho_i, cancel their normalizing action, then apply actual affine Bruhat injectivity in G(k)^0 (Proposition 1.4.5). I∩N(k)=Z(k)^0 alone is insufficient",
        "Part (4): Theorem 5.3.3 for surjectivity and replaced Lemma 5.3.5 for injectivity, with their source hypotheses",
        "7.8.2 gives Wtilde^0=W_aff semidirect Stab(C,Wtilde^0) after choosing C; 7.7.12 identifies that stabilizer with the Iwahori normalizer modulo I"
      ],
      "consumer_or_regression": "Distinct Hecke functions and finite-support convolution beyond simply connected split groups. Preserve length-zero data and the chamber dependence of the splitting; no Iwahori–Matsumoto presentation is claimed.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Lemma 11.5.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.430–431 / PDF pp.461–462; Chapter 11 ambient hypotheses at PDF p.451"
      },
      "erratum": null,
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian valuation ring and perfect residue field f; G is connected reductive. In a fixed separable closure k_s let K be the maximal unramified extension, I=Gal(k_s/K) and Gamma=Gal(K/k). Put A=pi_1(G)_I. kappa_G:G(k)→A^Gamma is the restriction of the actual Kottwitz homomorphism constructed over K in 11.5.1.",
        "G(k)^1 is the subgroup of Definition 2.6.15, and A_tor is the torsion subgroup of A. No dim(f)≤1 assumption is imposed."
      ],
      "conclusion": "G(k)^1=kappa_G^(-1)((A_tor)^Gamma). This is the preimage of invariant torsion, distinct from the zero kernel identifying G(k)^0.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Actual Kottwitz construction and functoriality, Lemma 11.5.1",
        "Abelianization G→G_ab, its finite-kernel map on fundamental groups and inertia coinvariants; Lemma 11.1.3 and Definition 2.6.15"
      ],
      "consumer_or_regression": "The second and third quotient identifications of 11.7.6 and retention of the G(k)^0/G(k)^1 distinction in Hecke and stabilizer interfaces.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 11.5.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.431 / PDF p.462; Chapter 11 ambient hypotheses at PDF p.451"
      },
      "erratum": null,
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian valuation ring and perfect residue field f; G is connected reductive. In a fixed separable closure k_s let K be the maximal unramified extension, I=Gal(k_s/K) and Gamma=Gal(K/k). Put A=pi_1(G)_I. kappa_G:G(k)→A^Gamma is the restriction of the actual Kottwitz homomorphism constructed over K in 11.5.1.",
        "G(k)^0 is the subgroup of Definition 2.6.23. Neither finiteness of f nor dim(f)≤1 is assumed in this kernel identity."
      ],
      "conclusion": "G(k)^0=ker(kappa_G). The homomorphism is the actual Kottwitz map, not an arbitrary map postulated to have this kernel.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 9.3.24, G(k)^0=G(K)^0 intersect G(k), reduces to k=K",
        "Quasi-splitness Corollary 2.3.8, torus kernel Proposition 11.1.5, induced-torus lifting Lemma 2.5.20 and z-extension surjectivity Proposition 11.5.3"
      ],
      "consumer_or_regression": "Identify the component quotient in Theorem 7.8.1(1), while keeping surjectivity and the Section 11.7 residue hypothesis separate.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Corollary 11.7.5",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.433–434 / PDF pp.464–465"
      },
      "erratum": null,
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian valuation ring and perfect residue field f; G is connected reductive. In a fixed separable closure k_s let K be the maximal unramified extension, I=Gal(k_s/K) and Gamma=Gal(K/k). Put A=pi_1(G)_I. kappa_G:G(k)→A^Gamma is the restriction of the actual Kottwitz homomorphism constructed over K in 11.5.1.",
        "In addition, dim(f)≤1 in the field-dimension sense of Section 11.7; this holds for finite residue fields. This is not a Krull-dimension condition.",
        "For the chamber quotient choose a Gamma-stable K-chamber C in B(G_K), as in the source proof. G(k)_C is its stabilizer and G(k)^0_C=G(k)_C intersect G(k)^0."
      ],
      "conclusion": "kappa_G:G(k)→A^Gamma is surjective and induces an isomorphism G(k)_C/G(k)^0_C≃A^Gamma. The chosen chamber is over K; do not silently replace it by an arbitrary k-chamber.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Existence of a Gamma-stable K-chamber, Proposition 9.10.4",
        "Proposition 11.6.1 exact sequence over K, Theorem 8.3.13 smooth connected-fibre chamber model, and Lemma 8.1.4 cohomology vanishing"
      ],
      "consumer_or_regression": "Length-zero/component representatives for the Iwahori–Weyl and Hecke interfaces over local fields.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Corollary 11.7.6",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.434 / PDF p.465"
      },
      "erratum": null,
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian valuation ring and perfect residue field f; G is connected reductive. In a fixed separable closure k_s let K be the maximal unramified extension, I=Gal(k_s/K) and Gamma=Gal(K/k). Put A=pi_1(G)_I. kappa_G:G(k)→A^Gamma is the restriction of the actual Kottwitz homomorphism constructed over K in 11.5.1.",
        "In addition, dim(f)≤1 in the field-dimension sense of Section 11.7; this holds for finite residue fields. This is not a Krull-dimension condition.",
        "A_tor is the torsion subgroup of A=pi_1(G)_I. Form invariants before the torsion-free quotient in the third identification."
      ],
      "conclusion": "Kottwitz induces G(k)/G(k)^0≃A^Gamma, G(k)^1/G(k)^0≃(A_tor)^Gamma, and G(k)/G(k)^1≃A^Gamma/(A_tor)^Gamma=(A^Gamma)_free. The explicit third quotient unpacks the source notation using torsion(A^Gamma)=(A_tor)^Gamma; no identification with (A/A_tor)^Gamma is asserted.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Lemma 11.5.2, Proposition 11.5.4 and Corollary 11.7.5",
        "First isomorphism theorem and the elementary fact that the torsion subgroup of an invariant subgroup is the invariant torsion subgroup"
      ],
      "consumer_or_regression": "Combine with Theorem 7.8.1(1) and its chamber-dependent splitting without discarding invariant torsion or length-zero representatives.",
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

## Bundle B: the complete certificate and its source map

The corrected Definition 4.1.26 is the ten-axiom target. The following table
records the source assembly of §9.5 and the extra routes needed to retain its
full corrected scope. It is a source-derived proof plan, not a Lean proof,
axiom report or claim of acceptance. In particular, the shorter printed list
in Theorem 9.2.7 does not reduce the program's certificate.

| Certificate item | Source route and boundary |
| --- | --- |
| 4.1.1 | Theorem 9.3.21, with apartments and facets constructed in §9.2. |
| 4.1.2 | The corresponding assertion for the constructed quasi-split group G_K. |
| 4.1.4 | Proposition 9.3.16. |
| 4.1.6 | AS1: 9.4.9; AS2–3: 9.4.19; AS4: 9.4.18; AS5: 9.4.35 and its preceding paragraph; AS6: 9.4.31. Apply the corrected inclusion of the identity in AS3. |
| 4.1.8 | Proposition 9.4.3 and Lemmas 9.4.6, 9.4.21. Part (2) retains a nonempty bounded subset. |
| 4.1.9 | Propositions 9.3.24–9.3.25, with the corrected restricted-building argument for 9.3.25. |
| 4.1.16 | The derived route through 9.6.5–9.6.6, corrected 4.4.5, 7.3.12 and 7.4.9, explained below; no separate paragraph for this axiom appears in the printed §9.5. |
| 4.1.17 | Proposition 7.9.5 has the scope of all covering field/group isomorphisms. Section 9.5 invokes it for the Gamma action. The full certificate must also transport the descended fixed loci, apartments and models under every such pair, not merely construct that one action. |
| 4.1.20 | Actual model descent in 9.2.5 and the integral-point identities in §9.5. Use 9.3.24 for the G(k)^0 intersection law; G(k)^1 has its own law. |
| 4.1.22 | Parts (1), (2), (7) descend geometrically; (7) uses perfect residue to descend the unipotent radical. Parts (3), (5) use facet correspondence and 9.4.31; (4) is 9.3.3; (6) is 9.4.23. |
| 4.1.27 | Fixed-locus and base-change constructions in §9.2, special tori from 9.3.4, and affine-root compatibility from 9.4.28. Retain all four clauses, including both integral-model intersection identities. |

Chapter 7 cannot supply a general existence theorem merely from a valuation
hypothesis. The corrections at PDF page 33 add **AS5 of Axiom 4.1.6** to its
ambient assumptions; PDF page 35 replaces the Weyl-identification arguments in
7.5.1 by this assumption. In the perfect-residue case, Proposition 9.4.35
establishes AS5 from the descended geometry before §9.6 constructs valuations.
The Iwahori–Tits systems of 7.5.3 are systems in G(k)^0 and G(k)^natural.
They do not erase the component or length-zero data of the full G(k) theory.

For the derived 4.1.16 route, Theorem 9.6.5 constructs root-datum valuations
compatible with the field valuation. Section 9.6.6 compares the descended
building with the Chapter 7 building made from those valuations. It identifies
affine roots and proves equality of the G(k)^0 stabilizers at **every** pair
of corresponding apartment points, using 9.4.21 and 7.6.4 and, for multipliable
roots, 6.3.8. This is the universal hypothesis required by corrected Corollary
4.4.5. The comparison needs Axioms 4.1.1, 4.1.4 and 4.1.9, already supplied
in the source assembly; it does not assume the missing Iwahori decomposition.

In the Chapter 7 construction, Corollary 7.4.9 gives the sharp-subgroup
factorization. The full bijections in Axiom 4.1.16 additionally use the
Z(k)^0 factor in 7.4.1, the root-factor bijections of 7.3.12(3), (5), and
injectivity of multiplication in the algebraic open cell. Transport these
factorizations through the comparison. For each fixed positive or negative
system, nondivisible root factors may be ordered arbitrarily. The three
unipotent/central/unipotent factors may also be permuted: switch the positive
system and use normalization by Z(k)^0. The added mixed-all-roots assertion
7.3.12(6) has the extra hypothesis f(0)>0; it is not needed for these
fixed-sign arbitrary orders and must not be applied at depth zero without
that hypothesis.

The descended models in 9.2.5 are actual smooth affine models obtained from
Fact 2.10.16; their coordinate rings are invariant rings, equivalently the
intersections of the O-coordinate rings with k[G]. Their relative identity
components, special fibres and maximal reductive quotients are separate
objects. For a point x the parahoric is G_x^0(o), which fixes its facet
pointwise and has finite index in the corresponding G(k)^1 facet stabilizer;
it is not identified with the full fixer. The naive G(k)^b intersection law
is false (Example 2.6.31). Likewise, a Gamma-chamber or Gamma-vertex need not
be a chamber or vertex over K. The reduced fixed-locus building remains
distinct from the enlarged building and its invariant central translation
factor.

The correction at PDF page 39 adds a further genuine metric dependency:
a bounded Gamma-stable subgroup of G(K) has a Gamma-fixed fixed point.
The argument uses closed convex fixed loci, the bounded closed convex hull
and Theorem 1.1.15. This does not permit a fixed point to be included as
input in place of constructing it. No formal certificate or general-instance
acceptance is recorded here.

## Bundle C: indexing, signs and component boundaries

The Cartan row uses the actual dominant subset of the centralizer Z(k),
modulo Z(k)^0, at a special vertex. It does not assume a dominant-cocharacter
parametrization for every reductive group. Corrected (5.2.2) has the
nonnegative valuation inequality. The same corrections remove the minus
signs from the valuation homomorphisms in Sections 2.5–2.6, so the corrected
dominance condition agrees with (5.2.1).

The Iwasawa product of Theorem 5.3.3 is a surjectivity statement. Injectivity
for the added Theorem 7.8.1(4) uses the replacement of Lemma 5.3.5, with a
chamber Iwahori P_C and every pair n,n' in N(k). The printed lemma with an
arbitrary bounded subgroup is not the corrected target. Theorem 5.3.4
separately retains a special vertex and an arbitrary parabolic k-subgroup.

The conditional Chapter 7 setup includes the added AS5 assumption and does
not impose perfect residue. For the stated source route to Theorem 7.8.1(4),
the ledger also retains the Chapter 5 perfect-residue building hypotheses
used by Theorem 5.3.3 and replaced Lemma 5.3.5. A proof under broader residue
hypotheses remains a separate obligation. Corollary 7.4.9 factors the sharp
subgroup; full parahoric bijections additionally need the central Z(k)^0
factor, the fixed-sign root-factor bijections and open-cell injectivity.

The Iwahori–Weyl quotient N(k)/Z(k)^0 retains component information that its
affine action may lose. Corrected injectivity in Theorem 7.8.1(2) cancels the
chamber-stabilizer component before applying affine Bruhat injectivity in
G(k)^0. The identity I intersect N(k)=Z(k)^0 alone does not prove this
injectivity. The splitting in 7.8.2 depends on the chosen chamber; length-zero
data must remain visible in the Hecke consumer.

For the actual Kottwitz map, Proposition 11.5.4 identifies G(k)^0 with the
zero kernel, while Lemma 11.5.2 identifies G(k)^1 with the preimage of
invariant torsion. Neither kernel description requires dim(f) <= 1. That
additional field-dimension hypothesis, which holds for finite residue
fields, belongs to the surjectivity and quotient statements in 11.7.5–6.
The chamber in 11.7.5 is a Gamma-stable K-chamber in B(G_K), as chosen in
the source proof; it is not replaced by an arbitrary k-chamber.

Writing A=pi_1(G)_I, the third quotient in 11.7.6 is recorded explicitly as
A^Gamma/(A_tor)^Gamma. This unpacks the torsion-free quotient of A^Gamma,
using torsion(A^Gamma)=(A_tor)^Gamma. It does not identify it with
(A/A_tor)^Gamma without a separate exactness argument. All of these are
source targets and dependency descriptions; no Kottwitz construction,
quotient bijection, Hecke distinctness or finite-support theorem is proved
by this note.

## Initial interfaces and the next mathematical gates

Metric definition child `bd4b31f8-44f8-447c-b747-e26d93a271d1` supplied the
published module `Langlands.Geometry.Metric.KPDefinitions`, namespace
`Langlands.Geometry.Metric.KP`, authored by Worker 1221. Its definition
candidate `3baeb443-a6c3-4cdf-9ef8-cce5431d3585` was independently accepted
and published in Library commit `6fd0709bd33fa6c33b4d74b4b638cfc51428b8f1`.
The module uses a primitive midpoint inequality and separates geodesic
existence, completeness, convexity and barycenters. Its radius and joint
diameter take values in the extended nonnegative reals; finite real readings
require explicit boundedness and nonemptiness. It does not prove the
fixed-point theorem. This definition publication therefore leaves the
formal status of the complete Theorem 1.1.15 target empty.

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
