# KP Bundles A–F: source ledger and construction boundaries

This source ledger covers Bundle A, initial Bundle B targets and Bundles C–F of the standing KP program
`f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703`. It records mathematical source targets,
not completed formalization. Every formal-status field below is empty: no
accepted, published Lean result for these complete targets has been verified in
this ledger. The remaining Bundle B targets still require public ledger entries. Private source audits and unsubmitted drafts are not publication evidence.

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

The Bundle D extension adds six source-only rows for Theorems 8.3.2,
8.3.13 and 8.4.10, Corollary 8.4.12, Theorem 8.4.19 and Section 13.2.6.
Its original-source audit covered book PDF pages 112–115, 314–316,
326–331, 333–341, 358–363, 394–395 and 497–502, and corrections PDF
pages 37–41 and 49–50. A further check of book PDF pages 327–328,
335 and 337–340, including visual inspection of pages 328, 335, 338 and
340, establishes the source discrepancy in the restricted kernel index of
Theorem 8.4.19(1) described below. The kernel target instead uses the
general product in Proposition 8.4.15. This extends the ledger to
twenty-nine rows. All six added formal-status fields and evidence arrays
remain empty; the source dependencies below supply no formal construction.

The Bundle E extension adds nine source-only rows for Proposition 13.2.5,
Sections 13.3.1–4, Theorem 13.5.1, corrected Proposition 13.5.2 and
the later Propositions 13.6.7 and 13.7.4. Its original-source audit
covered book PDF pages 97–98, 230, 274–282, 497–515 and corrections PDF
pages 49–50. Book PDF pages 281 and 500 were visually checked for
the printed root indices. The discrepancy in Proposition 13.2.5(3)
remains an explicit independent formal-resolution obligation. The
optimal-point clauses in Definition 13.4.2, Lemma 13.4.4 and Proposition
13.6.7 were checked at book PDF pages 503–504 and 512: the empty-root
case has no literal optimal point, as the G_m/Q_2 zero-coset regression
below shows. Its separate instability target is retained, and the
general program scope is unchanged. The 2024 corrections do not supply
an empty-root extension; none is proved here. Section
1.6 and Corollary 7.3.14 independently justify restricting openness to
finite augmented depths; the separated infinite term is recorded
separately and need not be open. This clarification is absent from the
2024 corrections. The
Remark 13.6.6 example at book PDF page 512 was also visually checked;
the explicit contracting cocharacter below invalidates its claimed
role as a witness. This is an independent source discrepancy, absent
from the 2024 corrections, with no Lean proof recorded here. This
extends the ledger to thirty-eight rows with all new formal-status
fields and evidence arrays empty. Positive-depth implementation
and the later instability targets retain their separate release gates.

The Bundle F extension adds five source-only rows for corrected
Proposition 12.4.1, Theorem 12.9.2, Proposition 12.9.4 and
Propositions 14.6.1 and 14.8.4. Its original-source audit covered
book PDF pages 467–473, 476–479, 488–496 and 521–540, together
with corrections PDF pages 47–50. Book PDF page 539 was visually
checked for the enlarged-building and full-stabilizer notation;
PDF pages 495–496 and 523 were rechecked for the actual-model
identity and the simple-factor lift condition. The nearest-point
dependency was checked at book PDF pages 38–40 and corrections PDF
pages 1–3, including visual inspection of corrections page 2.
The proof repairs below are independently derived obligations,
separate from the authors' corrections. All forty-three rows retain
null formal status and empty formal-evidence arrays. This source
extension leaves the release order and construction gates open.

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
  "coverage": "Bundle A named targets, initial Bundle B targets (corrected Definition 4.1.26, Theorem 7.5.3 and Theorem 9.2.7), Bundle C decompositions and narrow component/Kottwitz interfaces, Bundle D parahoric models, maximal reductive quotients and depth-zero reduction with Chapter 9 descent, Bundle E group/Lie/dual filtrations, all three comparison alternatives, corrected pro-p ambient group and later degeneracy/instability targets, and Bundle F corrected finite-action fixed loci, tame building and integral-model descent, and embeddings from adapted data with their strict-Henselian and general-k existence boundaries. Remaining Bundle B items still need public rows. All rows are source-only; every formal construction, proof and release gate remains separate.",
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
    },
    {
      "source_item": "Theorem 8.3.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.296 / PDF p.327; schematic models in Sections 2.8 and 2.10"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.37, Chapter 8 opening, Section 8.3 and Remark 8.3.4",
        "change": "Replace the opening of Section 8.3 by the perfect-residue hypothesis. Change 'first three sections' to 'first two sections'. In Remark 8.3.4 the full-fixer model is evaluated on O, not K."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "S is a maximal K-split torus, T=Z_{G_K}(S), and Omega is a nonempty bounded subset of its apartment in the actual building B(G_K). The models in Chapter 8 are over O; their descent over o is a separate construction."
      ],
      "conclusion": "G(K)^1_Omega and G(K)^dagger_Omega are schematic: they are the O-points of actual smooth affine O-group schemes with generic fibre G_K. Their models have the same relative identity component. This does not assert connectedness of the entire models or identify either subgroup with the full fixer.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 8.3.1: faithful representations, stable lattices, schematic closure and smoothening (A.6.5–A.6.6) construct vertex models",
        "Enlarge Omega to the facets meeting it; Proposition 7.7.1 gives the finite-index inclusions, and A.7.1 propagates schematicity and identifies relative identity components",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent."
      ],
      "consumer_or_regression": "Actual integral-model input for the connected model, its reduction and compact/open integral points. The generally nonaffine full-fixer model of Remark 8.3.4 remains a different object.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 8.3.13",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.299 / PDF p.330; corrected proof at corrections PDF p.37"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.37, Section 8.3 and Theorem 8.3.13",
        "change": "Apply perfect residue and replace the proof's final two sentences. Connected fibres first force factorization through G^0_Omega; only then apply the open finite-index argument and A.4.26."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "S is a maximal K-split torus, T=Z_{G_K}(S), and Omega is a nonempty bounded subset of its apartment in the actual building B(G_K). The models in Chapter 8 are over O; their descent over o is a separate construction."
      ],
      "conclusion": "The common relative identity component G^0_Omega of the schematic models in 8.3.2 has G^0_Omega(O)=G(K)^0_Omega. It is the actual smooth affine connected-fibre parahoric model with generic fibre G_K. Its connectedness does not identify the parahoric with a full pointwise or setwise fixer.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Theorem 8.3.2; T is a maximal torus since G_K is quasi-split by 2.3.8. The connected Neron model has T^0(O)=T(K)^0 by B.8.7",
        "Sections 8.3.7–8.3.12 construct root models with prescribed integral points and connected fibres. Sections 2.10.10 and 2.10.19 extend the genuine generic-fibre inclusions",
        "Corrected connected-fibre argument: torus and root model maps factor through G^0_Omega; hence the generated G(K)^0_Omega lies in G^0_Omega(O). Proposition 7.7.1 gives openness and finite index there, and Lemma A.4.26 proves equality",
        "Proposition 8.3.14 gives the actual root-product open immersion",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent."
      ],
      "consumer_or_regression": "Connected parahoric construction for reduction, inflation and compact induction. Proving compactness and openness further uses the actual scheme-point topology from its owning task.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 8.4.10",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.305 / PDF p.336; notation at Sections 8.4.2–8.4.8"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.37, opening of Section 8.4",
        "change": "Retain perfect residue from corrected Section 8.3 and replace both occurrences of o by O in the second paragraph."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "S is a maximal K-split torus, T=Z_{G_K}(S), and Omega is a nonempty bounded subset of its apartment in the actual building B(G_K). The models in Chapter 8 are over O; their descent over o is a separate construction.",
        "Write H_Omega for the connected special fibre of the connected parahoric model G^0_Omega, and Gred_Omega=H_Omega/R_u(H_Omega) for its maximal reductive quotient. Sbar is the special fibre of the standard O-model of S and is identified with its image in Gred_Omega."
      ],
      "conclusion": "For every choice of positive relative roots, open-cell multiplication is an isomorphism of schemes from the negative nondivisible U^+_{a,Omega,0} factors, T^+, and the positive nondivisible factors onto R_u(H_Omega). These plus groups are special-fibre images of the corresponding 0+ model maps. This is not a direct-product group decomposition. The root datum of Gred_Omega relative to Sbar is (X^*(S),Phi_Omega,X_*(S),Phi_Omega^vee), where Phi_Omega consists of gradients of affine roots vanishing identically on Omega. For a in Phi_Omega, Ubar_{a,Omega,0}/U^+_{a,Omega,0} maps isomorphically to its a-root group. Phi_Omega is reduced even when the ambient relative root system has multipliable roots.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 8.3.14, Corollary 8.4.5 and Proposition 8.4.8; Lemma 8.4.7 keeps the a-versus-2a alternatives",
        "Dynamic root groups and multiplication, Proposition 2.11.9 and Theorem 2.11.15; torus unipotent radical B.10.12",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.5 uses perfectness to descend the geometric unipotent radical; the displayed split root datum is a geometric description over fbar, not an assertion of splitness over f"
      ],
      "consumer_or_regression": "Maximal reductive quotient for depth zero. Preserve the special-fibre distinction; the ramified SU_3 example of Remark 8.4.11 has quotient SO(3)=PGL_2 although the ambient group is simply connected.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Corollary 8.4.12",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.306 / PDF p.337"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.37, corrected Sections 8.3–8.4 ambient setup",
        "change": "Perfect residue applies throughout; Section 8.4 models are over O. No direct replacement of Corollary 8.4.12 is listed."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "S is a maximal K-split torus, T=Z_{G_K}(S), and Omega is a nonempty bounded subset of its apartment in the actual building B(G_K). The models in Chapter 8 are over O; their descent over o is a separate construction.",
        "Write H_Omega for the connected special fibre of the connected parahoric model G^0_Omega, and Gred_Omega=H_Omega/R_u(H_Omega) for its maximal reductive quotient. Sbar is the special fibre of the standard O-model of S and is identified with its image in Gred_Omega."
      ],
      "conclusion": "Under the natural surjective reduction G(K)^0_Omega=G^0_Omega(O)→H_Omega(fbar), the inverse image of R_u(H_Omega)(fbar) is G(K)_{Omega,0+}. Thus 0+ is the kernel of the composite to Gred_Omega(fbar); it is generally larger than the kernel of reduction to the whole special fibre.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Smooth Henselian reduction is surjective by 8.1.3; the integral-point identification is Theorem 8.3.13",
        "Theorem 8.4.10, Corollary 8.4.5(2), Lemma B.10.11 and Proposition 7.3.12 identify the inverse image",
        "Proposition 2.4.3 makes projection from smooth connected special-fibre rational points to the reductive quotient surjective; Lemma 2.4.2 supplies unipotent H^1 vanishing",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.5 uses G(k)^0=G(K)^0 intersect G(k) from 9.3.24, descends the unipotent radical over perfect f and gives G(k)^0+_F=G(K)^0+_F intersect G(k), hence the kernel over k"
      ],
      "consumer_or_regression": "Use the actual reduction composite in the depth-zero quotient and inflation; neither an arbitrary map with an assumed kernel nor reduction to the entire special fibre meets the target.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 8.4.19",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.308–310 / PDF pp.339–341; valid general kernel product in Proposition 8.4.15, printed pp.306–307 / PDF pp.337–338; counterexample from Example 8.3.5, printed pp.296–297 / PDF pp.327–328, and Section 8.4.6, printed p.304 / PDF p.335"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.37–38, Sections 8.3–8.4 and the setup of Proposition 8.4.15",
        "change": "Apply perfect residue and O-model conventions. Move the nonempty bounded Omega≺Omega' hypothesis before 8.4.15, define both model and special-fibre morphisms there, and delete that proposition's former first sentence. These authors' corrections contain no repair of the restricted index printed in 8.4.19(1); the source discrepancy recorded here is a separate derived check from 8.3.5 and 8.4.6."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "F and F' are facets in an apartment A with F contained in the closure of F'. The generic-fibre identity induces the actual model morphism G^0_{F'}→G^0_F and its special-fibre morphism rhobar:H_{F'}→H_F. The full bijection ranges over all facets in B(G_K) whose closures contain F, not just those in A."
      ],
      "conclusion": "By Proposition 8.4.15 specialized to these facets, the schematic kernel of rhobar is smooth connected unipotent, and open-cell multiplication identifies it as a scheme with the product of ker(Ubar_{a,F',0}→Ubar_{a,F,0}) over all nondivisible roots a in Phi(S,G_K). The restriction to Phi'_{F'} minus Psi_F(F') printed in Theorem 8.4.19(1) is false and is excluded as a formalization target: Example 8.3.5 gives a split SL_2 open chamber F' incident to a hyperspecial vertex F for which Phi'_{F'} is empty by 8.4.6, but ker(rhobar) is G_a. Theorem 8.4.19(2)–(4) supplies the remaining conclusions. The image p_F(F') is the parabolic of H_F associated to Psi_F(F') and contains R_u(H_F). The inverse image of p_F(F')(fbar) in G^0_F(O) is G^0_{F'}(O). The map F'↦p_F(F') is a bijection from all incident facets onto all parabolics of H_F, equivalently of Gred_F. Facets in A alone correspond to parabolics containing the chosen maximal torus. The kernel product is a scheme isomorphism, not a direct-product group decomposition.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Corrected general morphism setup preceding Proposition 8.4.15; that proposition supplies the smooth connected unipotent kernel and the product over all nondivisible ambient roots, without the false restriction in 8.4.19(1)",
        "Derived source-discrepancy check from Example 8.3.5 and Section 8.4.6: the chamber model maps to the hyperspecial SL_2 model by c=pi*c'; on special fibres its kernel has a=d=1, b=0 and c' free, hence is G_a, whereas Phi'_{F'} and the printed product index are empty",
        "Root-filtration comparisons 6.3.21; Theorem 8.4.10, Proposition 8.4.8(2), Proposition 1.3.35 and Corollary 8.4.12; independence from the apartment and the use of all apartments through F",
        "For nonempty bounded Gamma-stable subsets, Section 9.2.5 constructs the descended smooth affine o-models using invariant coordinate rings and relative identity components; 9.2.6 identifies the parahoric o-points. Chapter 8 models alone do not give this descent.",
        "Section 9.3.2 descends the facet morphisms and identifies Gamma-facets through F with parabolic f-subgroups; Proposition 2.4.5 transfers these to the maximal reductive quotient",
        "Proposition 9.3.3 proves the exact inverse-image equality over o, using 8.1.3 smooth Henselian reduction and Lemma 2.4.2 for the smooth connected unipotent kernel. This does not assert that every geometric parabolic descends"
      ],
      "consumer_or_regression": "Residue/facet correspondence and change-of-parahoric tests for depth-zero induction and double cosets; retain rational parabolics after Chapter 9 descent. The split SL_2 chamber-to-vertex kernel is a regression against the erroneous printed restricted index.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Section 13.2.6",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.470 / PDF p.501; Chapter 13 hypotheses at PDF p.497"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.37–41 and 49–50",
        "change": "Use corrected perfect-residue Chapter 8–9 constructions. The Chapter 13 corrections affect 13.5.2, 13.6.2 and 13.8.5, not 13.2.6; the Appendix B correction on minimal congruent torus filtration does not replace the depth-zero model proof."
      },
      "hypotheses": [
        "k has a normalized discrete valuation, Henselian integer ring o and perfect residue field f; G is connected reductive over k. K is a maximal unramified extension, O its integer ring, fbar its algebraically closed residue field, and Gamma=Gal(K/k)=Gal(fbar/f). Perfect residue is the corrected hypothesis of Section 8.3 and subsequent sections, not merely quasi-splitness of G_K.",
        "x is a point of the actual descended building over k, with connected parahoric model G^0_x over o, special fibre H_x and maximal reductive quotient Gred_x. Put P_{x,0}=G^0_x(o). The Chapter 13 torus filtration is functorial and admissible with 7.2(1),(2). No finite-residue assumption is required for this depth-zero assertion."
      ],
      "conclusion": "The natural composite P_{x,0}=G^0_x(o)→H_x(f)→Gred_x(f) is surjective with kernel P_{x,0+}, and hence induces P_{x,0}/P_{x,0+}≃Gred_x(f). The analogous assertion holds over K. As an f-group scheme, Gred_x is also the cokernel of the special-fibre map G_{x,0+}→G_{x,0}. The rational-point quotient uses both surjectivity steps and the descended kernel; it does not follow merely from a group-scheme cokernel.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Theorems 8.3.2 and 8.3.13 construct the actual models; Sections 9.2.5–9.2.6 descend them and identify integral points",
        "The first reduction arrow is surjective by 8.1.3. The second is surjective by Proposition 2.4.3 over perfect f, proved using Lemma 2.4.2 on split unipotent groups and H^1",
        "Corollary 8.4.12 and Section 9.5 identify the actual kernel over k; apply the group first isomorphism theorem",
        "The congruence models and their morphism come from Theorem 8.5.2 and Section 8.5.17, with Chapter 9 descent",
        "Section 13.2.2 separates facet-dependent 0 and 0+ from positive-depth variation, and 13.2.3 uses 9.8.3(2) for the Gamma-invariant group comparison"
      ],
      "consumer_or_regression": "For a nonarchimedean local field, separately prove finiteness of Gred_x(f) from finite residue and finite type, and compactness/openness from the actual model topology. Inflate a finite-quotient representation through this map and prove the quotient factorization, then compactly induce and prove a double-coset or intertwining theorem. This source row supplies no positive-depth acceptance.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 13.2.5",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.469 / PDF p.500; definitions at PDF pp.497-499; finite-depth clarification from Section 1.6, PDF pp.97-98, and Corollary 7.3.14, PDF p.282"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.49-50; independent boundary check at book PDF pp.97-98,282,498,500; root-index cross-check at book PDF pp.230,278,281,500,506",
        "change": "No replacement of 13.2.5 is listed. The finite-depth restriction on openness is an independently justified clarification, not an authors' erratum. Preserve the separate confirmed printed root-index discrepancy explicitly; the possible indivisible-root/concave-block formulation is source-derived and requires an independent proof, not attribution as an author correction."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "For the bounded-open and Iwahori-decomposition assertions, depths are finite nonnegative augmented depths: r or r+ with r a nonnegative real number, excluding infinity. The covariance, commutator and Levi assertions below are also stated at finite nonnegative depths r,s; the infinite-depth term is recorded separately. For the Levi assertions, P=MN is a parabolic k-subgroup, x is in B(G)_M as in Section 9.7, and x_M is its image in B(M) under (9.7.1)."
      ],
      "conclusion": "At finite nonnegative augmented depths, the actual P_{x,r} form a decreasing family of bounded open subgroups, independent of the apartment used to define them. Its separated extension has P_{x,infinity}=intersection_{t>=0, t real} P_{x,t}={1}; this term need not be open. For g in G(k), g P_{x,r} g^-1=P_{gx,r}; hence P_{x,r} is normal in the full point stabilizer. The commutator is contained in P_{x,r+s}. At finite r>0, P_{x,r} has the Iwahori decomposition of 13.2.4 relative to P, including a homeomorphism of the three factors, rather than a group direct product. At every finite nonnegative augmented depth, its intersection with M(k) is P^M_{x_M,r}. The finite-depth restriction on openness independently clarifies the printed wording; it is not an authors' correction. Printed part (3), at positive finite depth, claims an arbitrarily ordered root/centralizer product bijection with products over all positive and negative roots. This indexing conflicts with its cited 7.3.12(5), which uses indivisible roots and concave-function blocks. The discrepancy is recorded, and that printed clause has an outstanding formal-resolution obligation; no corrected theorem or author erratum is claimed here.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Section 1.6 at PDF pp.97-98 includes infinity in the augmented index set and defines the separated infinite term as the intersection, equal to {1}. Corollary 7.3.14 at PDF p.282 asserts boundedness generally, but openness only if the concave function never takes infinity. Thus openness is retained only at finite r/r+",
        "Concrete boundary check from (13.1.1), PDF p.498: for G_m over Q_2, the standard and minimal congruent filtrations agree, and P_{x,n}=1+2^n Z_2 for integers n>=1. Their intersection is {1}, which is not open because the distinct elements 1+2^n converge to 1",
        "Propositions 7.3.17 and 7.6.4 give apartment independence; 7.7.8(1) gives conjugation covariance. Root-valuation Axiom V3, 7.1.2, 7.1.3 and commutator-friendliness give the commutator bound. Corollary 9.7.3 gives the depth-zero Levi intersection",
        "The original PDF p.500 was visually checked: the all-root indexing is printed, not lost during extraction. PDF p.281 prints indivisible-root indexing in 7.3.12(5). Root-valuation V4 at PDF p.230 makes scalar factors for a and 2a overlap when U_{2a,x,2r} is nontrivial; taking both as independent coordinates cannot then be injective",
        "Source-derived route to investigate and prove independently: use indivisible roots with the 7.3.3(1) blocks U_{a,x,f}=U_{a,x,f(a)} U_{2a,x,f(2a)}, at constant f=r, together with the full Z(k)_r central factor, 7.3.12(4),(5) and open-cell injectivity. Merely adding indivisible-root indexing to scalar-depth factors need not recover all 2a-depth-r elements in a nonreduced system",
        "Sections 13.2.2-3 retain facet dependence only for 0 and 0+, and the equality P_{x,r}(k)=P_{x,r}(K)^Gamma from 9.8.3(2)",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Regression: a nonsplit group with a multipliable root must detect overlapping a/2a scalar factors and test the separately proved block formulation. Check finite r/r+ openness separately from the non-open infinite term for G_m(Q_2), point variation inside a facet, full-stabilizer normality and the actual Levi embedding. Boundedness alone is not compactness over general Henselian k.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Section 13.3.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.470 / PDF p.501"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.49-50, Chapter 13 and Appendix B.10",
        "change": "No direct replacement of 13.3.1 is listed. If the minimal congruent torus filtration is used, include its corrected Gamma-invariance and descent from Appendix B.10."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction."
      ],
      "conclusion": "For r>=0, g_{x,r}=Lie(G_{x,r}) is an o-lattice in g(k). The identity g_{x,r+n}=m^n g_{x,r} for nonnegative integers n extends the definition consistently to every real depth. The resulting open additive subgroups form a separated descending filtration, with g_{x,r+}=union_{s>r} g_{x,s}. The dual lattice is exactly g^*_{x,r}={X in g^* : X(Y) in m for every Y in g_{x,(-r)+}}. The maximal ideal m, the minus sign and the strict plus in this annihilator convention are retained.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Section 8.5 constructs the actual constant-concave-function models; Proposition 8.5.16 proves their Lie-lattice periodicity",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction.",
        "Section 1.6 supplies the real-depth-plus convention; well-defined extension to negative depths is a proof obligation, not a separately assumed lattice family",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Check positive and negative integer shifts and the exact dual annihilator pairing in equal and mixed characteristic. The general lattice construction requires no quasi-splitness of G.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Section 13.3.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.470 / PDF p.501"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13",
        "change": "No direct replacement of 13.3.2 is listed; the corrected Chapter 8-9 constructions remain part of its dependency closure."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction.",
        "Gred_x is the maximal reductive quotient of H_x, the special fibre of the connected parahoric model. The Lie lattices and their 0+ term are the constructions of 13.3.1."
      ],
      "conclusion": "There is an identification of f-Lie algebras Lie(Gred_x)=cok(g_{x,0+} tensor_o f to g_{x,0} tensor_o f)=g_{x,0}/g_{x,0+}. It uses m g_{x,0} contained in g_{x,0+} contained in g_{x,0}; it identifies the maximal reductive quotient's Lie algebra, rather than the Lie algebra of the whole special fibre.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Section 13.2.6 identifies Gred_x with the group-scheme cokernel of the special-fibre morphism G_{x,0+} to G_{x,0}",
        "Proposition 8.5.18 proves smoothness of that morphism's kernel; Section 2.4(a) then supplies exactness on Lie algebras",
        "Use the actual descended models and Lie maps, not an arbitrary quotient equipped with an assumed identification",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Depth-zero Lie comparison and graded-action tests. Keep distinct the rational-point quotient of 13.2.6 and this Lie-algebra cokernel calculation; neither alone proves the other.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Section 13.3.3",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.470-471 / PDF pp.501-502; Section 8.5.20 for the basis formula"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13; corrected Chapter 9 setup at PDF pp.39-41",
        "change": "No direct replacement of 13.3.3 is listed. Use corrected Chapter 9 descent rather than treating a K-basis calculation as a general formula over k."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction.",
        "r is real."
      ],
      "conclusion": "Let g(K)_{x,r} be the O-Lie lattice of the base-changed actual model. Then g_{x,r}=g(K)_{x,r}^Gamma. The Chevalley-Steinberg basis formula of 8.5.20 describes the O-lattice over K and works over o when G is quasi-split. There is also an intrinsic description over o: choose a maximal k-split S with x in its apartment; let z_r be the Lie lattice of the S-fixed subgroup scheme of G_{x,r}, with generic fibre Z_G(S). For an affine root psi, let u_psi=Lie(U_psi)=g_z intersect u_a(k), for any z on H_psi and a the derivative of psi. Then g_{x,r} is the o-span of z_r and the u_psi for psi(x)>=r. The quasi-split hypothesis belongs to the explicit basis formula over o, not to the general lattice or its intrinsic span description.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Section 8.5.20 gives the explicit Chevalley-Steinberg lattice over O; the actual model descent gives the invariant lattice",
        "Section 9.4.5 constructs U_psi; Proposition 9.8.3 supplies the standard integral S-model action and its centralizer filtration. Section 13.2.1 defines Psi_{x,r} by psi(x)>=r",
        "The model construction and the root-space span formula must be proved for the constructed objects; a chosen basis or an assumed Gamma-invariant lattice is insufficient",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Compare split basis calculations with a non-quasi-split descended lattice and a multipliable-root case. Retain the actual maximal split torus, centralizer and affine-root valuation conventions.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Section 13.3.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.471 / PDF p.502"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13",
        "change": "No direct replacement of 13.3.4 is listed. Keep the action over the residue field f and the special-fibre/reductive-quotient distinction explicit."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "The smooth congruence models and their morphisms come from Section 8.5, with the actual Chapter 9 descent over o. Parahorics, full stabilizers, the whole special fibre H_x and its maximal reductive quotient Gred_x retain distinct meanings. Chapter 8 models over O alone do not supply the descended construction.",
        "r is real. Gred_x is the actual maximal reductive quotient of the parahoric special fibre; both Lie and dual lattices use Section 13.3.1's conventions."
      ],
      "conclusion": "Conjugation by the connected parahoric model induces actions on the Lie and dual lattices. On their strict graded pieces g_{x,r}/g_{x,r+} and g^*_{x,r}/g^*_{x,r+}, these induce genuine f-rational representations of Gred_x. Factorization through the reductive quotient and preservation of the lattices are part of the conclusion, not structure fields to assume.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 13.2.5 gives normality over K; Corollary 2.10.10 extends the actual conjugation action to integral models",
        "Apply the Lie functor, dual action and reduction, with periodicity for all real depths, then prove the action factors through Gred_x on both strict graded pieces",
        "Sections 13.3.1-3 and the actual Chapter 9 model descent",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Graded adjoint/coadjoint action and pairing-equivariance tests; this rational reductive-quotient action is the one used for later algebraic instability, not a valuation-topology orbit action.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 13.5.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.474-476 / PDF pp.505-507"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.50, Appendix B.10: Definition B.10.8, Corollary B.10.14 and added Remark B.10.15",
        "change": "No direct replacement of 13.5.1 is listed. Clarify that R in B.10.8(2) is an induced K-torus; add T(k)^mc_r=T(K)^mc_r intersect T(k); repair the recall in B.10.14; add Gamma-stability and smooth O-model descent in Remark B.10.15. These affect the torus dependency boundary."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Equip the category of tori specifically with the minimal congruent filtration. Fix real 0<r<=s and x in B(G). At least one of the following three alternatives holds.",
        "(1) A maximally split maximal torus of G_K becomes induced after a tame base change (weakly induced, B.6.2), and s<=2r.",
        "(2) r=r0+n with 0<=r0<1, n a positive integer and s<=r0+2n.",
        "(3) 0<r<=s<=2r<=r+1."
      ],
      "conclusion": "There exists an isomorphism of abstract abelian groups MP_{x,r,s}:P_{x,r}/P_{x,s} to g_{x,r}/g_{x,s}, compatible with unramified algebraic extensions of k. Under alternative (1) or (2), it can be chosen so that, for every k-rational automorphism theta of G, dtheta composed with MP_{x,r,s} composed with theta^-1 equals MP_{theta(x),r,s}. The theorem does not assert this general automorphism equivariance under (3) alone. When (1) and (2) both hold, their constructions coincide. This is not an unconditional exponential map or a k-linear group map.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Alternative (2): Proposition A.5.19 on the actual congruence models and its functoriality for their morphisms",
        "Alternatives (1)/(3) over K: indivisible-root quotient products, C.5.1 root-model congruence and A.5.19; torus comparison B.6.9 under (1), and possibly nonfunctorial B.10.17 under (3). Resolve 13.2.5's indexing against its cited 7.3.3/7.3.12 construction before relying on it",
        "Descent: Lemma 8.1.4, smooth connected unipotent special fibres from 8.5.14 and perfect-residue H^1 vanishing from 2.4.2, for both group and Lie lattices",
        "Agreement under (1)/(2): A.5.19 functoriality and B.10.16 compatibility of the torus comparisons",
        "Corrected B.10.8 and added B.10.15 establish the minimal congruent torus filtration over k, Gamma-stability and smooth model descent. Functoriality of the filtration does not imply unrestricted functoriality of its Moy-Prasad isomorphisms at every positive depth",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Positive-depth acceptance requires actual finite abelian graded quotients over local fields, character transport through this proved map and a nontrivial calculation. Test each applicable alternative separately and the (1)/(2) overlap; do not impose a global tame or large-residue-characteristic hypothesis.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 13.5.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.476-477 / PDF pp.507-508; corrections PDF p.49"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13, Proposition 13.5.2(1)",
        "change": "Replace G(k) with G(k)^0 in part (1); retain the same ambient group already present in part (2)."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Additionally k is a local field: complete with finite residue field f of characteristic p. Use the actual parahoric subgroups, positive-depth filtrations and the point topology of G(k). Maximality and the normalizer below are taken in G(k)^0."
      ],
      "conclusion": "For every x, P_{x,0+} is an open pro-p subgroup of G(k)^0. It is maximal among open pro-p subgroups there exactly when x lies in a chamber, equivalently P_{x,0} is Iwahori. Every maximal open pro-p subgroup of G(k)^0 is P_{x,0+} for an Iwahori P_{x,0}, and its normalizer in G(k)^0 is P_{x,0}. Neither the maximality claim nor the normalizer identity is extended to the full G(k).",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Actual model point topology and local compactness turn bounded open subgroups into compact ones. Realize P_{x,0+} as the inverse limit of its finite p-group filtration quotients, using 13.5.1 for their steps",
        "Fixed points 4.2.14, type preservation 1.5.13(3), the actual reduction and incident-facet/parabolic correspondence 8.4.19 with Chapter 9 descent; finite-field p-subgroup structure and the Iwahori-Tits system in G(k)^0",
        "The normalizer argument uses 2.2.16 and 6.3.21",
        "Release 1 constructions, the corrected Theorem 9.2.7 certificate and the inflation/compact-induction consumer remain prerequisites for positive-depth implementation. A source row supplies no release or formal acceptance."
      ],
      "consumer_or_regression": "Check the exact ambient group in both maximality and normalization, including a case with nontrivial component or length-zero data. An abstract pro-p predicate does not supply the compactness, inverse limit or building fixed-point proof.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 13.6.7",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.481 / PDF p.512; definitions and prerequisites at PDF pp.509-511; optimal-point boundary: Definition 13.4.2 and Lemma 13.4.4, printed pp.472-473 / PDF pp.503-504; torus formula (13.1.2), printed p.467 / PDF p.498"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13, end of Section 13.6.2",
        "change": "Replace the reference 1.3.35 with 8.4.8(3). No direct replacement of 13.6.7 is listed."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "r is real and Xi is a Lie coset in g_{x,r}/g_{x,r+}. Nilpotent means algebraically contracted to zero by a k-defined cocharacter G_m to G, as in 13.6.5. Degenerate means containing such an element. Instability refers to the algebraic Gred_x-orbit closure in the f-rational graded representation of 13.3.4. This is distinct from valuation-topology closure of a G(k)-orbit in g.",
        "Xi=X+g_{x,r+} is degenerate, with X nilpotent in the k-cocharacter sense. Definition 13.4.2 requires a nonempty finite subset of the affine-root set Sigma for an optimal point. A target retaining optimality must explicitly assume nonempty relative roots; this is no restriction on the ambient connected-reductive program. No convention extending optimality to empty roots is supplied or proved here."
      ],
      "conclusion": "The printed first clause asserts an optimal point y and real s>r with the entire coset Xi contained in g_{y,s}. As a universal connected-reductive assertion this is false: G_m over Q_2 has empty affine roots and no optimal point under 13.4.2, although 0+g_{x,1+} is degenerate. Retain the nonempty-relative-root optimal-point version as a proof target. General whole-coset depth raising without optimality and any separately derived empty-root convention or extension need their own statements and proofs. The separate instability clause remains a target: Xi in g_{x,r}/g_{x,r+} is unstable under Gred_x, meaning zero belongs to its algebraic orbit closure. These are Lie-coset targets; the broader dual-coset degeneracy definition does not extend them to dual cosets.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "13.6.3 constructs a contracting k-cocharacter compatible with x, using Iwasawa 5.3.4, actual models, perfect-residue unipotent H^1 vanishing and 8.4.19/9.3.2",
        "13.6.4 conjugates it by an element of P_x into the chosen maximal split torus with the chamber inequalities. A small apartment translation raises the finite set of root depths. The subsequent optimal-point reduction 13.4.4 uses a nonempty affine-root subset in its proof and fails for empty roots as stated. Use this reduction only in the nonempty-relative-root target; a general depth-raising proof must handle the empty-root case separately",
        "For instability the compatible cocharacter extends to the actual integral model and reduces to an f-cocharacter contracting the graded vector; use the action of 13.3.4. This is a separate clause and does not require the existence of a literal optimal point",
        "Independent empty-root boundary, not an authors' erratum: for G_m/Q_2, the reduced building has one point x (4.1.4(A0), PDF p.189), Sigma is empty, and (13.1.2) gives g_{x,1}=2 Z_2 and g_{x,1+}=4 Z_2. Zero is contracted by the identity cocharacter, so Xi=0+g_{x,1+} is degenerate by 13.6.5. There is no optimal y under 13.4.2, yet Xi is already contained in g_{x,2} and its zero graded vector is unstable. Thus the optimality requirement and 13.4.4 need resolution; this example does not refute depth raising or instability. The 1 November 2024 corrections, PDF pp.49-50, do not repair 13.4.2, 13.4.4 or this clause of 13.6.7",
        "The printed Remark 13.6.6 example is not a witness separating cocharacter nilpotence from Jordan nilpotence. In characteristic two, for x nonzero, X=[[1,x],[x^(-1),1]], B=[[x,1],[1,0]] and B^(-1)=[[0,1],[1,x]] satisfy det(B)=1, X^2=0 and B^(-1) X B=x^(-1) E_12. The k-defined cocharacter lambda(u)=B diag(u,u^(-1)) B^(-1) has lambda(u) X lambda(u)^(-1)=u^2 X, so it contracts X to zero. Nonconjugacy to E_12 does not imply absence of a contracting cocharacter. This is an independently demonstrated source discrepancy, not an authors' erratum or a Lean result; the 1 November 2024 corrections do not repair 13.6.6. Any broader non-equivalence claim needs a separately checked witness",
        "Later target: implement only after positive-depth acceptance has constructed finite abelian graded quotients, transported characters through the proved comparison and verified a nontrivial filtration calculation. No minimal K-type or supercuspidality theorem follows from this source row."
      ],
      "consumer_or_regression": "After positive-depth acceptance, test full-coset containment, the strict s>r inequality, the G_m/Q_2 zero coset at r=1 (degenerate, no literal optimal point, contained at depth 2, unstable), and the explicit contraction of the printed characteristic-two matrix. Use the k-cocharacter definition; any comparison with Jordan nilpotence needs a separate proof.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 13.7.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.483-484 / PDF pp.514-515; topology comparison at PDF p.513"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.49, Chapter 13",
        "change": "No direct replacement of 13.7.4 is listed; apply the corrected 13.6.2 reference in its 13.6.7 dependency."
      },
      "hypotheses": [
        "k has a normalized discrete valuation omega(k^times)=Z, Henselian integer ring o, maximal ideal m and perfect residue field f. G is a connected reductive k-group. K is a maximal unramified extension, O its integer ring and Gamma=Gal(K/k). x belongs to the actual descended building B(G). No splitness, tameness, finite-residue or perfect-k hypothesis is imposed unless separately stated.",
        "Until Section 13.5, choose any functorial admissible filtration on tori satisfying Section 7.2(1),(2), hence commutator-friendly by 7.2.3; Section 9.8 supplies the centralizer filtration. P_{x,r}=G(k)_{x,r} is generated by the actual root and centralizer filtrations as in 13.2.1 and 7.3.3. The strict-depth convention is X_{r+}=union_{s>r} X_s.",
        "r is real and Xi is a Lie coset in g_{x,r}/g_{x,r+}. Nilpotent means algebraically contracted to zero by a k-defined cocharacter G_m to G, as in 13.6.5. Degenerate means containing such an element. Instability refers to the algebraic Gred_x-orbit closure in the f-rational graded representation of 13.3.4. This is distinct from valuation-topology closure of a G(k)-orbit in g."
      ],
      "conclusion": "If there exist y in B(G) and real s>r with Xi intersect g_{y,s} nonempty, then Xi is degenerate. Also, Xi is unstable under the algebraic Gred_x-action if and only if Xi is degenerate. The first implication needs only an intersection, whereas the depth-raising clause printed in 13.6.7 asks for whole-coset containment and has the separate empty-root optimality obstruction recorded in its row. No local compactness or perfect-k hypothesis is added to this result; the perfect-residue/Henselian Chapter 13 setup is retained.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Lemma 13.7.3 proves g_{y,s} contained in g_{x,s}+N using an apartment displacement and its root-space decomposition, with N the cocharacter-defined nilpotent set",
        "Use only the separate instability clause of Proposition 13.6.7 for degenerate implies unstable, not its optimal-point assertion or an empty-root use of 13.4.4",
        "For unstable implies degenerate, Kempf's rational cocharacter theorem over perfect f gives a contracting f-cocharacter. Conjugacy of maximal f-split tori and the actual surjection P_x to Gred_x(f) lift it through a split o-torus. A small apartment translation raises the depth, and part (1) applies",
        "The additional perfect-k or locally compact hypotheses of nearby 13.7.2 concern the valuation-topology set N' and N=N', not the algebraic instability equivalence of 13.7.4. Register and read Kempf's original before a proof relies on that theorem directly",
        "Later target: implement only after positive-depth acceptance has constructed finite abelian graded quotients, transported characters through the proved comparison and verified a nontrivial filtration calculation. No minimal K-type or supercuspidality theorem follows from this source row."
      ],
      "consumer_or_regression": "After positive-depth acceptance, test intersection versus containment and distinguish algebraic residue-field orbit closure from valuation-topology G(k)-orbit closure. Preserve the actual reduction surjectivity used in lifting cocharacters.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 12.4.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed p.446 / PDF p.477; replaced in corrections PDF p.47"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.47-48, Section 12.4 and proof of 12.7.1",
        "change": "Replace Proposition 12.4.1 and its proof in full. Delete the Corollary 4.4.5 citation in the first paragraph of 12.4 and the last sentence of its second paragraph; use the corrected intersection and boundedness in 12.4.2 and the corrected facet argument in 12.7.1."
      },
      "hypotheses": [
        "O is a Henselian discrete valuation ring with fraction field K and algebraically closed residue field. H is connected reductive over K; Theta is a finite group of K-automorphisms whose order is prime to the residue characteristic, with no restriction when it is zero. G=(H^Theta)^0 and the enlarged buildings retain their central translation factors.",
        "Use the Section 12.4 reduction in which the maximal K-split central torus of G is central in H. Put H'=H_der and G'=(H'^Theta)^0. Let S be a maximal K-split torus of G and S' its maximal subtorus contained in G'.",
        "x is a Theta-fixed point of enlargedB(Z_{H'}(S)). A is any apartment of that building containing x."
      ],
      "conclusion": "For every such apartment A, its Theta-fixed locus is A^Theta=V(S')+x=enlargedB(Z_{H'}(S))^Theta. This describes the entire fixed locus as an affine translation space and retains the specified fixed point and the universal apartment quantifier. It does not replace an enlarged building by a reduced one.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Corrected Section 12.4 setup and 12.3.2; retain the distinction between S and S'. For the apartment argument choose a maximal split torus of Z_{H'}(S), containing S'; the correction's proof phrase about a torus of H' containing S needs interpretation against this distinction",
        "The maximal split central torus Z of Z_{H'}(S) and its derived group are Theta-stable, with (Z^Theta)^0=S'. Parahoric transitivity on apartments through x glues their V(Z) translation actions; use V(Z)^Theta=V(S') and the union of apartments through x",
        "The adjacent corrected 12.4.2 uses a nonempty bounded subset of the intersection of the two fixed loci; 12.7.1 also needs the corrected vertex-to-facet argument",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Compare reduced and enlarged buildings for tori and groups with a central split factor; test two apartments through x. This fixed-locus calculation is an input to tame descent, not a general unramified-descent certificate.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Theorem 12.9.2",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.463-464 / PDF pp.494-495; metric convention at PDF p.490"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.47-48, corrected Chapter 12 dependencies",
        "change": "No direct replacement of 12.9.2 is listed. Apply the replaced 12.4.1, corrected 12.4.2 and corrected 12.7.1 facet argument in its finite-action dependency."
      },
      "hypotheses": [
        "k is discretely valued and Henselian with perfect residue field. The valuation omega extends uniquely to algebraic extensions and the same extension is used throughout; do not renormalize the extension field independently. Connected reductive groups and their actual buildings are used, without a global split, quasi-split, tame, finite-residue or large-residue-characteristic hypothesis.",
        "G is connected reductive over k and l/k is a finite tamely ramified Galois extension. Tameness means that the residue characteristic does not divide the ramification index, not necessarily [l:k].",
        "Use the reduced building of the theorem and compatible invariant Euclidean metrics: 12.7.2 permits rescaling on simple factors to agree with the fixed-locus metric."
      ],
      "conclusion": "The constructed reduced building B(G) has a natural identification with B(G_l)^Gal(l/k) as a metric space, using the inherited valuation and compatible metrics. No assumption that G/k itself is quasi-split or split is added.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Let k' be the maximal unramified subextension of l/k, and K,L the maximal unramified extensions of k,l in one separable closure. Then L=K tensor_{k'} l and Gal(L/k')=Gamma times Theta, where Gamma=Gal(K/k') and Theta=Gal(l/k')=Gal(L/K)",
        "Apply 12.7.1 to H=Res_{l/k'}(G_l), whose base change is Res_{L/K}(G_L), using the corrected 12.4.1 and 12.7.1 arguments. The totally ramified Theta part has order prime to the residue characteristic; the unramified degree can be divisible by it",
        "Apply actual Chapter 9 unramified descent in both orders to Gamma and Theta, and then to k'/k; the corrected 9.2.7 certificate remains required. The enlarged finite-automorphism construction is an intermediate step rather than a change of target",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Test a tame ramified extension together with an unramified degree divisible by the residue characteristic, inherited valuation scales, and anisotropic or nonsplit groups. No arbitrary wild-extension fixed-locus identity follows.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 12.9.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.464-465 / PDF pp.495-496; 12.8.5 at PDF pp.493-494"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF p.48, Proposition 12.8.5",
        "change": "Move the last sentence of the first paragraph after the first sentence of the second paragraph: the separate torus-filtration assumption at r=f(0) is placed after the sentence defining f and its pullback F. No direct replacement of 12.9.4 is listed; retain f(0)>0 and all torus-filtration hypotheses of its dependency."
      },
      "hypotheses": [
        "Use the Section 12.9 maximal-unramified K setting: K is Henselian discretely valued with algebraically closed residue field, and G is connected reductive over K, hence quasi-split there. Let L/K be finite tamely ramified Galois with Theta=Gal(L/K).",
        "S is a maximal K-split torus of G. T is the K-torus containing S for which T_L is a maximal L-split torus of G_L. Use the same extended valuation on L.",
        "f on the roots plus zero of (S,G) is concave with f(0)>0 in the source extended-depth convention. F is its pullback by restriction from (T,G). The point x lies in A(S) inside A(T_L). Use the actual admissible torus/root filtrations and smooth concave-function models."
      ],
      "conclusion": "G(L)_{x,F} is Theta-stable, G(K)_{x,f}=(G(L)_{x,F})^Theta, and G_{x,f}=(H_{x,F})^Theta for H=Res_{L/K}(G_L). The last identity is for actual smooth integral group schemes, not merely their integral points. No extension to arbitrary depth-zero concave functions is asserted.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Proposition 12.8.5 requires a cyclic prime-to-residue-characteristic action, surjective root restriction with each fibre one Theta-orbit, and the separate torus equality (Z_H(T_H)(K)_r)^Theta=Z_G(S)(K)_r at r=f(0). In the Weil-restriction application use the corresponding maximal split torus T_H of H; do not confuse it with the K-torus T of G",
        "The 12.9.4 proof checks the root fibres using Z_G(S), a maximal torus over K, and the successive Galois orbits of its absolute roots. A future proof must also discharge the torus-filtration equality for restriction of scalars rather than silently assuming it",
        "The 12.8.5 proof uses ordered root products, root-orbit cases, translation to depth zero, the 12.7.1 parahoric comparison and 2.10.11 uniqueness of smooth models. Audit multipliable-root indexing against 7.3.3/7.3.12 before using product coordinates",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Test a nontrivial tame ramified extension, the torus comparison, a multipliable-root case and equality of actual models. Keep the f(0)>0 boundary visible in every downstream filtration statement.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 14.6.1",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.502-504 / PDF pp.533-535; definitions at PDF pp.529-532"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.1-2,27-29,47-50; Chapter 14 has no listed correction",
        "change": "No direct replacement of 14.6.1 is listed. Preserve the corrected Chapter 4 geometric/quotient dependencies. In any use of 14.5.6 and 14.7 retain corrected nonempty convexity and prove nonemptiness independently."
      },
      "hypotheses": [
        "k is discretely valued and Henselian with perfect residue field. The valuation omega extends uniquely to algebraic extensions and the same extension is used throughout; do not renormalize the extension field independently. Connected reductive groups and their actual buildings are used, without a global split, quasi-split, tame, finite-residue or large-residue-characteristic hypothesis.",
        "G is a connected reductive k-subgroup of the connected reductive k-group H. For a maximal split torus S of G, A_G is the maximal split central torus of G and M=Z_H(A_G). Enlarged and reduced buildings, full point stabilizers, G(k)^1 and parahorics remain distinct.",
        "Choose an adapted pair (x_tilde,y_tilde) in the enlarged buildings of G and H.",
        "Adapted data are Definition 14.5.1 and Remark 14.5.2, not just a single-point stabilizer inclusion: retain the normalizer-fixed orbit, the apartment map taking x to y, and the stabilizer inclusion at every translate. In reduced coordinates this is G(k)^1_{x+v} contained in M(k)^1_{y+v} for every v in V(S/A_G); in enlarged coordinates use the equivalent full-stabilizer condition for every v in V(S).",
        "Admissible means equivariant on k-points and affine on apartments with the induced cocharacter translation map (14.0.1). For a closed immersion, the metric is induced from H on the cocharacter spaces before claiming isometry (14.2.2). No isometry between unrelated simple-factor metric normalizations is asserted."
      ],
      "conclusion": "There is a unique admissible embedding of enlargedB(G) into enlargedB(H) taking the chosen x_tilde to the chosen y_tilde. For the pair (phi,psi) of 14.3.1, the reduced map phi:B(G)->B(M) restricts on A(S,G) to the normalizer-fixed-orbit apartment map phi_{S,y_bar} of 14.4.1. Uniqueness is relative to the adapted pair, not a canonical embedding independent of choices. Equivariance, affine apartment behaviour and all-translate point-stabilizer inclusion do not assert a general positive-depth filtration identity.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Descend (g,z) mapped to g phi_{S,y_bar}(z) through the 4.4.4 quotient using normalizer equivariance and G(k)^1_z contained in M(k)^1_{phi(z)} for every apartment point z. Keep both the normalizer and stabilizer terms of that quotient relation",
        "Point-stabilizer conjugacy of maximal split tori through x gives independence of S. The central translation coordinates and the Levi embeddings of 9.7.5 determine psi. Uniqueness uses the 14.3.1 factorization and 14.4.1 affine uniqueness",
        "14.6.2 describes when different adapted pairs give the same embedding. 14.0.3 gives a reduced map obstruction for a split torus in SL2; 14.0.5 gives enlarged-map nonuniqueness by central translations",
        "Passing from a subgroup to a general homomorphism requires the 14.0 simple-factor lift condition: on every relevant simple factor the lift from G_sc to the simply connected cover of the image is trivial or an isomorphism onto its image. Use the faithfully flat quotient step of 14.1.1 and then the subgroup embedding. This does not give an injective or canonical map for every homomorphism.",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Test choice dependence and central translations, the split torus/SL2 reduced-building obstruction, equivariance, apartment derivatives and all-translate stabilizers. A separate source and proof are required for any later positive-depth or integral-model morphism compatibility.",
      "formal_status": null,
      "owner_task": "f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703",
      "acceptance_artifact_ids": [],
      "publication_commits": [],
      "axiom_reports": [],
      "external_code": []
    },
    {
      "source_item": "Proposition 14.8.4",
      "source": {
        "literature_id": "kaletha-prasad-2023-bruhat-tits-new-approach",
        "content_sha256": "05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732",
        "locator": "printed pp.505-508 / PDF pp.536-539; descent at PDF pp.535-536"
      },
      "erratum": {
        "literature_id": "kaletha-prasad-2024-corrections",
        "content_sha256": "23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed",
        "locator": "PDF pp.1-2, Section 1.1; no Chapter 14 correction is listed",
        "change": "Apply nonempty convexity and the corrected nearest-point proof. The printed corrected coefficient2 and zero-distance continuity case need the explicitly recorded independent repairs in the dependencies and private audit. No change to the 1.1.20 theorem statement is needed."
      },
      "hypotheses": [
        "The section assumes strictly Henselian k. Retain the Chapter 14 discretely valued perfect-residue context and the actual enlarged buildings.",
        "G is a connected reductive k-subgroup of the connected reductive k-group H. For a maximal split torus S of G, A_G is the maximal split central torus of G and M=Z_H(A_G). Enlarged and reduced buildings, full point stabilizers, G(k)^1 and parahorics remain distinct.",
        "l/k is a finite Galois extension splitting G and H; no tame hypothesis is imposed. x_tilde in enlargedB(G) is absolutely special. Choose y1_tilde in enlargedB(H_l) with the full stabilizer inclusion G(l)_{x_tilde} contained in H(l)_{y1_tilde}. Let y_tilde be its unique closest point in the embedded enlargedB(H).",
        "Admissible means equivariant on k-points and affine on apartments with the induced cocharacter translation map (14.0.1). For a closed immersion, the metric is induced from H on the cocharacter spaces before claiming isometry (14.2.2). No isometry between unrelated simple-factor metric normalizations is asserted."
      ],
      "conclusion": "The pair (x_tilde,y_tilde) is adapted in the full sense of 14.5.1/14.5.2. In particular adapted pairs exist under the section hypotheses. The target of the closest-point projection is the enlarged base building, confirmed visually at PDF p.539; it is not identified with the entire Galois fixed locus for an arbitrary ramified splitting extension. General-k existence uses the separate 14.7 descent step.",
      "lean_declarations": [],
      "modules": [],
      "dependencies": [
        "Adapted data are Definition 14.5.1 and Remark 14.5.2, not just a single-point stabilizer inclusion: retain the normalizer-fixed orbit, the apartment map taking x to y, and the stabilizer inclusion at every translate. In reduced coordinates this is G(k)^1_{x+v} contained in M(k)^1_{y+v} for every v in V(S/A_G); in enlarged coordinates use the equivalent full-stabilizer condition for every v in V(S).",
        "7.11.4 supplies an absolutely special point staying special over l. Existence of y1 uses boundedness of the full stabilizer and the building fixed-point theorem; it must be proved, not supplied as the entire existence argument",
        "14.8.2 proves the split case using root-group lattices and homogeneous polynomial coordinate maps. Strict Henselianity makes G quasi-split (2.3.8), so Z_G(S) is a maximal torus. 14.8.3 projects the split adapted point using 1.1.20; projection equivariance for group actions and translations gives the all-translate condition",
        "Proposition 1.1.20 needs a complete NPC geodesic space and a nonempty closed convex base building. Its projection is unique, continuous and equivariant for isometries preserving that subset setwise. Corrections PDF p.2 prints the insufficient minimizing-sequence estimate d(y1,y2)^2<=2 epsilon(2r+epsilon), contradicted already by X=Y=R, x=0, r=0, epsilon=1 and y1,y2=+-3/4. Independently derive the sufficient bound with coefficient4 from the midpoint inequality. The added continuity proof needs the zero-distance case separately; the division-free bound d(pi(x_n),pi(x))^2<=2(q_n^2-r^2), with q_n=d(x,pi(x_n))->r=d(x,pi(x)), covers that case. These are source-derived proof repairs to prove, not author errata or established Lean results.",
        "For general k, 14.5.6 proves closedness and segment containment of the adapted-y locus. 14.7.1 makes the space of embeddings complete and NPC with evaluation-independent metric; 14.7.2 obtains an equivariant embedding assuming nonemptiness; 14.7.3 applies this to the maximal unramified extension and Chapter 9 descent. Neither convexity alone nor an assumed fixed point proves the needed nonemptiness",
        "Passing from a subgroup to a general homomorphism requires the 14.0 simple-factor lift condition: on every relevant simple factor the lift from G_sc to the simply connected cover of the image is trivial or an isomorphism onto its image. Use the faithfully flat quotient step of 14.1.1 and then the subgroup embedding. This does not give an injective or canonical map for every homomorphism.",
        "Release 1 constructions and its representation consumer, then positive-depth acceptance, precede Bundle F implementation. A source-only row is no formal or release acceptance."
      ],
      "consumer_or_regression": "Test all-translate full stabilizers after projection and after unramified descent, the induced metric choice and central-translation nonuniqueness. No arbitrary positive-depth filtration compatibility or canonical functor on all homomorphisms is claimed.",
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

## Bundle D: models, descent and the actual reduction map

The corrected opening of Section 8.3 requires perfect residue, which applies
to that section and those following it. The Chapter 8 models are over the
integer ring O of the maximal unramified extension K. Theorems 8.3.2 and
8.3.13 distinguish the schematic models with a common relative identity
component from the connected parahoric model itself. The corrected proof of
8.3.13 first factors the torus and root model maps through that identity
component, using connected fibres; only then does the open finite-index
argument apply. The generally nonaffine full-fixer model of Remark 8.3.4
is a separate object, and the corrected evaluation there is on O.

The special fibre H_Omega of the connected parahoric model and its maximal
reductive quotient Gred_Omega=H_Omega/R_u(H_Omega) are distinct. Theorem
8.4.10 identifies the root datum of the latter. Its product description of
the unipotent radical is an isomorphism of schemes supplied by open-cell
multiplication; it is not a direct-product decomposition as groups.

For incident facets F contained in the closure of F', the kernel of the
actual special-fibre map rhobar:H_{F'} → H_F is smooth connected unipotent.
Proposition 8.4.15 (printed pp. 306–307 / PDF pp. 337–338), specialized to
these facets with the corrected morphism setup on corrections PDF p. 38,
gives the valid scheme isomorphism by open-cell multiplication:

`product over all nondivisible a in Phi(S,G_K) of
ker(Ubar_{a,F',0} → Ubar_{a,F,0}) ≃ ker(rhobar)`.

The smaller index `Phi'_{F'} minus Psi_F(F')` printed in Theorem
8.4.19(1) (printed p. 309 / PDF p. 340), and repeated in its proof, is
false. It is recorded as a source discrepancy and excluded from future Lean
targets. The authors' corrections on PDF pp. 37–38 repair the ambient
hypotheses and morphism setup but contain no repair of this index.

Here is a derived counterexample using the book's own Example 8.3.5
(printed pp. 296–297 / PDF pp. 327–328) and Section 8.4.6 (printed p. 304 /
PDF p. 335). Take k=Q_3, its maximal unramified extension K, and G=SL_2.
Let F be the hyperspecial vertex x and F' the adjacent open chamber (x,z)
of that example. The connected models have coordinate rings

`O[G^0_F] = O[a,b,c,d]/(ad-bc-1)`,

`O[G^0_{F'}] = O[a,b,c',d]/(ad-pi*b*c'-1)`.

The generic-identity model morphism sends `(a,b,c',d)` to
`(a,b,pi*c',d)`. On special fibres it sends these coordinates to
`(a,b,0,d)`. Its scheme-theoretic kernel is defined by `a=d=1, b=0`,
leaving `c'` free. Its coordinate ring is therefore `fbar[c']`, and the
group law displayed in Example 8.3.5 restricts to addition of `c'`.
Thus the kernel is G_a. But 8.4.6 defines Phi'_{F'} from the affine roots
vanishing identically on F'. None vanishes on this open chamber, so
Phi'_{F'} is empty. The printed restricted product would be the one-point
scheme, contradicting this kernel computation. The general product over
all nondivisible ambient roots retains the nontrivial negative-root
kernel and has no such contradiction. This calculation diagnoses the
source formula; no Lean construction or proof is supplied here.

Theorem 8.4.19(2)–(4) gives the parabolic image, the inverse-image equality
on integral points and the full facet/parabolic bijection. That bijection
ranges over all incident facets in the building; restricting to one
apartment yields only the parabolics containing the chosen maximal torus.

Section 9.2.5 descends the actual smooth affine models to o by invariant
coordinate rings and relative identity components. Section 9.2.6 identifies
the parahoric integral points. The geometric unipotent radical descends
over the perfect residue field f in Section 9.5. The equalities
G(k)^0=G(K)^0 intersect G(k) and
G(k)^0+_F=G(K)^0+_F intersect G(k) then give the descended kernel in the
reduction map. The geometric Chapter 8 construction alone does not prove
these statements over k.

The homomorphism in Section 13.2.6 is the natural composite

`P_{x,0}=G^0_x(o) → H_x(f) → Gred_x(f)`.

The first arrow is surjective by smooth Henselian reduction, Section 8.1.3.
The second is surjective by Proposition 2.4.3 over perfect f, whose proof
uses Lemma 2.4.2 on split unipotent groups and Galois H^1. Corollary 8.4.12
and Section 9.5 identify the composite's kernel with P_{x,0+}. The first
isomorphism theorem then gives P_{x,0}/P_{x,0+} isomorphic to Gred_x(f).
Reduction to the whole special fibre has a generally smaller kernel. A
scheme-theoretic cokernel by itself does not supply this rational-point
quotient or its two surjectivity steps.

For the residue correspondence, Section 9.3.2 and Proposition 2.4.5 give
parabolic f-subgroups after descent. Proposition 9.3.3 proves the exact
inverse-image equality on o-points, using Section 8.1.3 and Lemma 2.4.2
for the smooth connected unipotent kernel. This preserves the rational
parabolic condition; it does not say every geometric parabolic descends.

No finite-residue hypothesis is needed for Section 13.2.6. For the
local-field consumer, finiteness of Gred_x(f) requires finite residue and
finite type, and compactness and openness require the actual topology on
integral points. These remain proof obligations. The representation test
must inflate a representation through this actual reduction map, prove
factorization through its quotient, and construct compact induction with
a basic intertwining or double-coset theorem. No irreducibility,
supercuspidality or positive-depth theorem follows from these source rows.

## Bundle E: filtrations, comparison alternatives and later instability

These nine source-only rows cover Proposition 13.2.5, Sections 13.3.1–4,
Theorem 13.5.1, corrected Proposition 13.5.2, and the later Propositions
13.6.7 and 13.7.4. Positive-depth implementation remains behind the depth-zero
release and its inflation/compact-induction consumer. The two instability
targets remain behind the separate positive-depth acceptance test.

### Ambient fields and torus filtrations

Chapter 13 starts with a normalized discretely valued Henselian field k,
integer ring o, maximal ideal m and perfect residue field f. It does not
assume k perfect or locally compact. Let K be a maximal unramified
extension, O its integer ring, and Gamma its Galois group over k.
The source convention is `X_{r+}=union_{s>r} X_s`.

Before Section 13.5, the torus filtration may be any functorial admissible
one satisfying Section 7.2(1),(2); Lemma 7.2.3 makes it
commutator-friendly. The standard filtration and the minimal congruent
filtration remain distinct. The standard filtration on all tori need not
be connected or congruent and need not have the Moy–Prasad comparison.
For weakly induced tori, its comparison is supplied by B.6.9. Theorem
13.5.1 specifically chooses the minimal congruent filtration. Functoriality
of that filtration does not imply that its comparison isomorphisms are
functorial at every positive depth.

### The printed root-index discrepancy in Proposition 13.2.5

The original Proposition 13.2.5(3), printed p.469 / PDF p.500, takes
products over all positive and negative roots, without an indivisible-root
superscript. Visual inspection confirms that this is printed, rather than
an extraction omission. Its cited Proposition 7.3.12(5), printed p.250 /
PDF p.281, instead uses the indivisible-root subsets.

This matters in a nonreduced root system. Root-valuation Axiom V4,
printed p.199 / PDF p.230, gives

`U_{a,x,r} intersect U_{2a}(k) = U_{2a,x,2r}`.

Whenever the group on the right is nontrivial, scalar-depth coordinates
for both a and 2a overlap. Multiplication with both as independent
coordinates cannot then be injective. If the factors are read in the
concave-function notation of Section 7.3.3(1), printed p.247 / PDF p.278,
the a-block already incorporates its 2a factor, causing the same overlap.
The proof of Proposition 13.2.5(5) and the quotient products used in the
proof of Theorem 13.5.1 also use indivisible-root subsets.

The source-derived route to investigate is the product over indivisible
roots of the blocks

`U_{a,x,f}=U_{a,x,f(a)} U_{2a,x,f(2a)}`,

with the second factor trivial when 2a is not a root, at constant
`f=r`, together with the full centralizer factor `Z(k)_r`. Propositions
7.3.12(4),(5) and algebraic open-cell injectivity provide the intended
route. Merely changing the index while retaining scalar-depth root groups
need not recover the missing depth-r elements of a divisible root group.
This note records a discrepancy and an outstanding independent proof
obligation. The corrections on PDF p.49 give no replacement of
Proposition 13.2.5; the proposed route is not an authors' erratum or an
already proved corrected theorem.

### Finite depths and the infinite term in Proposition 13.2.5

The bounded-open assertion is restricted to finite nonnegative augmented
depths: `r` or `r+` for a nonnegative real r, excluding infinity.
Section 1.6, printed pp.66–67 / PDF pp.97–98, includes infinity in the
augmented index set and defines

`P_{x,infinity}=intersection_{t>=0, t real} P_{x,t}={1}`

for a separated filtration. This term need not be open. Corollary 7.3.14,
printed p.251 / PDF p.282, gives boundedness generally but asserts
openness only when the concave function never takes infinity. For a
concrete check, take `G=G_m` over `Q_2`. Formula (13.1.1), printed p.467 /
PDF p.498, gives `P_{x,n}=1+2^n Z_2` for integers `n>=1`; the standard
and minimal congruent filtrations agree for this induced torus. Their
intersection is `{1}`, which is not open: the distinct elements `1+2^n`
converge to 1.

The printed wording of Proposition 13.2.5 includes the whole extended
index set in its bounded-open assertion. The finite-depth restriction
here is an independently justified clarification of that wording,
separate from the root-index issue above. The corrections of 1 November
2024, PDF pp.49–50, do not supply this clarification.

At finite nonnegative augmented depths, the remaining assertions retain
apartment independence, conjugation covariance, normality in the full
point stabilizer, and the commutator bound. The Iwahori decomposition is
asserted at finite positive augmented depths. Its product map is a
homeomorphism of the three factors as in Definition 13.2.4, rather than
a group direct product. Levi compatibility at finite nonnegative
augmented depths requires x in the actual subbuilding `B(G)_M` and the
point `x_M` from (9.7.1). Over a general Henselian field the finite-depth
subgroups are bounded and open; compactness needs the local-field
topology.

### Lie and dual lattices

Section 13.3.1 defines the Lie lattice for nonnegative r from the actual
smooth congruence model, and uses Proposition 8.5.16's integer-shift
periodicity to extend it consistently to every real r. The dual convention is

`g^*_{x,r}={X in g^* | X(Y) in m for every Y in g_{x,(-r)+}}`.

The maximal ideal, negative depth and strict plus all belong to the
pairing convention. Section 13.3.2 identifies
`Lie(Gred_x)=g_{x,0}/g_{x,0+}` using the actual special-fibre maps and
the smooth kernel of Proposition 8.5.18. It does not identify the
maximal reductive quotient with the whole special fibre.

Section 13.3.3 gives the invariant lattice over k from the O-lattice
over K, and an intrinsic span using the centralizer lattice and affine-root
lattices with `psi(x)>=r`. Its explicit Chevalley–Steinberg basis formula
over o requires G quasi-split; the general model/lattice and intrinsic
span constructions have no such extra hypothesis. Section 13.3.4 obtains
actual f-rational representations of Gred_x on the Lie and dual strict
graded pieces from model conjugation. Descent, lattice preservation and
factorization through Gred_x all remain construction and proof obligations.

### All three alternatives of Theorem 13.5.1

With the minimal congruent torus filtration, x in the constructed building
and real `0<r<=s`, retain the three alternatives separately:

1. A maximally split maximal torus of G_K becomes induced after a tame
   base change, and `s<=2r`.
2. `r=r0+n` with `0<=r0<1`, n a positive integer, and `s<=r0+2n`.
3. `0<r<=s<=2r<=r+1`.

At least one alternative gives an isomorphism of abstract abelian groups
`P_{x,r}/P_{x,s}` with `g_{x,r}/g_{x,s}`, compatible with unramified
algebraic extensions. Automorphism equivariance is asserted under (1) or
(2). It is not asserted under (3) alone. The constructions from (1) and
(2) agree when both apply. This is neither an unconditional exponential
map nor a claim of a k-linear group map.

Alternative (2) uses A.5.19 on the actual congruence models. Over K,
(1) and (3) use indivisible-root quotient products, root-model congruence,
A.5.19, and the torus comparisons B.6.9 and B.10.17 respectively.
Descent uses the smooth connected unipotent special fibres and the
corresponding group and Lie-lattice cohomology vanishing. Corrections
PDF p.50 repair B.10.8 and B.10.14 and add B.10.15; Gamma-stability
and smooth model descent of the minimal congruent filtration belong to
this dependency boundary.

### The ambient group in corrected Proposition 13.5.2

This proposition additionally assumes that k is a local field with finite
residue of characteristic p. The authors' correction changes the ambient
group in part (1) to `G(k)^0`. Each `P_{x,0+}` is an open pro-p subgroup
there, maximal exactly for chamber points. Every maximal open pro-p
subgroup of `G(k)^0` is the positive-depth subgroup of an Iwahori, which
is its normalizer in `G(k)^0`. Neither assertion extends here to the
full `G(k)`. Actual compactness, finite filtration quotients, fixed points,
type preservation, reduction and the rational parabolic correspondence
remain part of its proof boundary.

### Later degeneracy and instability

Propositions 13.6.7 and 13.7.4 concern Lie cosets. The nilpotence notion in
Definition 13.6.5 is contraction to zero by a k-defined cocharacter.
The printed example in Remark 13.6.6 over `F_2((t))` does not distinguish
this notion from Jordan nilpotence. For a nonzero x in characteristic two,
put

```text
X = [[1, x], [x^(-1), 1]],
B = [[x, 1], [1, 0]],
B^(-1) = [[0, 1], [1, x]].
```

Then `det(B)=1`, `X^2=0` and `B^(-1) X B=x^(-1) E_12`. Consequently
the k-defined cocharacter
`lambda(u)=B diag(u,u^(-1)) B^(-1)` satisfies
`lambda(u) X lambda(u)^(-1)=u^2 X`. This orbit map extends to u=0
with value zero, including when x is the nonsquare uniformizer of
`F_2((t))`. Thus the displayed matrix is nilpotent in Definition 13.6.5's
sense as well. For nonsquare x, the matrix `x^(-1) E_12` is not
SL_2(k)-conjugate to E_12: any conjugating matrix preserves their common
kernel k e_1, so it is upper triangular with determinant one and scales
E_12 by a square. Thus nonconjugacy to the single matrix E_12 does not
establish the absence of a contracting cocharacter.

This calculation diagnoses an independent source discrepancy in the
printed example and its assertion that every contracted element is
conjugate to E_12. The corrections of 1 November 2024 do not repair
Remark 13.6.6. No Lean proof of this calculation is recorded here, and
any broader claim that the two nilpotence notions differ needs a
separately checked witness. The targets continue to use the
k-defined contraction convention of Definition 13.6.5.

The perfect residue field does not imply that k is perfect. A degenerate
coset contains an element nilpotent in this cocharacter sense.

### The empty-root boundary in optimal-point reduction

The first clause printed in Proposition 13.6.7, printed p.481 /
PDF p.512, asks for an optimal point y and a real s>r such that the
entire degenerate coset is contained in `g_{y,s}`. Definition 13.4.2,
printed p.472 / PDF p.503, requires a nonempty finite subset of the
affine-root set Sigma to define an optimal point. Consequently the
printed universal assertion fails for groups with empty relative roots.
Lemma 13.4.4, printed p.473 / PDF p.504, also asserts an optimal-point
replacement and explicitly uses a nonempty root subset in its proof.
Its unrestricted formulation has the same boundary.

For a concrete regression, let `G=G_m` over `Q_2` and take `r=1`.
The reduced building is the singleton x, by the reduced-apartment
convention of 4.1.4(A0), printed p.158 / PDF p.189. Both the relative
and affine root sets are empty, so Definition 13.4.2 supplies no optimal
point. Formula (13.1.2), printed p.467 / PDF p.498, gives
`g_{x,1}=2 Z_2` and `g_{x,1+}=4 Z_2`; standard and minimal congruent
filtrations agree for this induced torus. The coset `Xi=0+g_{x,1+}`
contains zero, which is contracted by the identity cocharacter. It is
therefore degenerate by Definition 13.6.5. It is already contained in
`g_{x,2}`, and its graded vector is zero and hence unstable. There is
nevertheless no literal optimal point. This example isolates the
optimality defect and does not refute deeper containment or instability.

The general connected-reductive scope of the program remains in force.
An optimal-point target under a nonempty-relative-root hypothesis must
be distinguished from a general depth-raising target omitting optimality
and from any separately derived convention or extension covering empty
roots. These remain statement and proof obligations; no extension of
Definition 13.4.2 is adopted or proved here. The corrections of
1 November 2024, PDF pp.49–50, supply no repair of Definition 13.4.2,
Lemma 13.4.4 or this clause of Proposition 13.6.7. This is an
independently identified source boundary, not an authors' erratum.

The separate clause of Proposition 13.6.7 gives the algebraic
instability target under Gred_x. Its route extends the compatible
contracting cocharacter to the integral model and reduces it to the
graded representation; it does not require a literal optimal point.
Proposition 13.7.4 needs only that the coset meets a lattice at some
greater depth to imply degeneracy, and its equivalence between degeneracy
and algebraic instability invokes this separate instability clause,
without inferring empty-root optimality from Lemma 13.4.4.
The local compactness or perfect-k
hypotheses in nearby Lemma 13.7.2 concern comparison with
valuation-topology orbit closure; they are not added to Proposition
13.7.4. The relevant instability uses algebraic orbit closure over f.
Lifting a contracting residue-field cocharacter uses the actual
surjection `P_x → Gred_x(f)`.

These later rows do not extend the propositions to dual cosets, supply
minimal K-types, or prove supercuspidality. Their implementation remains
after the finite abelian graded quotients, character transport and
nontrivial filtration calculation required for positive-depth acceptance.

## Bundle F: tame descent and embeddings from adapted data

The five added source rows cover corrected Proposition 12.4.1, Theorem
12.9.2, Proposition 12.9.4 and Propositions 14.6.1 and 14.8.4. These
source targets retain the general connected-reductive program. Their
implementation follows the depth-zero release with its representation
consumer, and then positive-depth acceptance. No construction, formal
statement or proof of these targets is recorded by this extension.

### The corrected finite-action fixed locus

Chapter 12 initially works over a Henselian discrete valuation ring O
with fraction field K and algebraically closed residue field. A finite
group Theta acts by K-automorphisms on a connected reductive H, and
`G=(H^Theta)^0`. Its order is prime to the residue characteristic,
with no restriction in residue characteristic zero.

The replacement of Proposition 12.4.1 on corrections PDF p.47 uses
the Section 12.4 reduction making the maximal K-split central torus
of G central in H. Put `H'=H_der`, `G'=(H'^Theta)^0`, take S maximal
K-split in G, and let S' be its maximal subtorus contained in G'.
For a Theta-fixed point x in the enlarged building of `Z_{H'}(S)`
and **every** apartment A of that building containing x, the conclusion is

`A^Theta = V(S') + x = enlargedB(Z_{H'}(S))^Theta`.

The point x, the apartment quantifier and the central translation
space belong to the statement. The proof glues the central V(Z) actions
on apartments through x using parahoric transitivity, and identifies
`V(Z)^Theta=V(S')`. Its torus step needs a maximal split torus of
`Z_{H'}(S)` containing S'; the correction's phrase about a torus of
H' containing S must be interpreted with S and S' distinguished.
This records a proof obligation, without claiming its formal resolution.
The surrounding corrections also delete the indicated sentences in
Section 12.4, require a nonempty bounded subset of the **intersection**
of the two fixed loci in 12.4.2, and replace the vertex-to-facet argument
in 12.7.1 (corrections PDF pp.47–48).

### Tame descent uses the inherited valuation and compatible metrics

Section 12.9 returns to a discretely valued Henselian k with perfect
residue field. The uniquely extended valuation omega is used on every
algebraic extension. Renormalizing an extension valuation independently
would change the apartment and filtration comparisons.

For connected reductive G/k and a finite tamely ramified Galois
extension l/k, Theorem 12.9.2 identifies the **reduced** building
`B(G)` with `B(G_l)^Gal(l/k)` as a metric space (book PDF pp.494–495).
Tameness concerns the ramification index. The unramified degree can
be divisible by the residue characteristic. Remark 12.7.2, PDF p.490,
chooses compatible metrics by allowing rescaling on simple factors.
The identification uses these metrics.

The proof separates the maximal unramified subextension k' of l/k
from the totally ramified part. For maximal unramified extensions K
and L of k and l in one separable closure,
`L=K tensor_{k'} l` and `Gal(L/k')=Gamma times Theta`, with
`Gamma=Gal(K/k')` and `Theta=Gal(l/k')=Gal(L/K)`. Apply the corrected
finite-action theorem to `Res_{l/k'}(G_l)` over K and apply actual
Chapter 9 unramified descent in both orders, then over k'/k.
The corrected 9.2.7 certificate remains necessary. The intermediate
enlarged-building construction does not change the theorem's reduced
target. The result imposes no split or quasi-split hypothesis on G/k.

### Positive-depth subgroup and integral-model descent

Proposition 12.9.4, book PDF pp.495–496, is in the maximal-unramified
K context, with algebraically closed residue field. G is quasi-split
over this K. Let L/K be finite tame Galois, `Theta=Gal(L/K)`, S maximal
K-split in G, and T the K-torus containing S whose base change T_L
is maximal L-split in G_L. For concave f on the roots plus zero of
`(S,G)`, retain **f(0)>0**. Let F be its pullback by root restriction,
and take `x in A(S) subset A(T_L)`. The conclusions are

`G(L)_{x,F}` is Theta-stable,
`G(K)_{x,f}=(G(L)_{x,F})^Theta`, and
`G_{x,f}=(H_{x,F})^Theta`, where `H=Res_{L/K}(G_L)`.

The last equality is an equality of actual smooth integral group
schemes. Proposition 12.8.5 separately requires the torus-filtration
equality at `r=f(0)`, along with surjective root restriction and
Theta-orbit fibres. In the Weil-restriction application its maximal
split torus T_H must be distinguished from the K-torus T of G.
The 12.9.4 proof checks root fibres through the quasi-split centralizer
`Z_G(S)` and its absolute roots. A formal proof must also discharge
the torus-filtration comparison. The correction on PDF p.48 moves
the torus-filtration assumption at `r=f(0)` after the sentence
defining f and its pullback F. Both definitions already occur
together in that sentence.

The source route uses ordered root products, translation to depth
zero, the parahoric comparison in 12.7.1 and uniqueness of smooth
models in 2.10.11. Multipliable-root indexing needs checking against
7.3.3 and 7.3.12, in light of the Bundle E diagnosis. This note makes
no new discrepancy claim about 12.8.5 and supplies no extension to
arbitrary depth-zero concave functions.

### Embeddings depend on adapted data

Chapter 14 uses discretely valued Henselian k with perfect residue
field. Admissibility means equivariance on k-points and affine
apartment maps with the induced cocharacter translation map
(14.0.1). For a closed immersion `G <= H`, isometry uses the metric
induced from H on cocharacter spaces (14.2.2).

Definition 14.5.1 and Remark 14.5.2 require the normalizer-fixed
orbit, the apartment map taking x to y, and stabilizer inclusion at
**every** translate. With `M=Z_H(A_G)`, the reduced condition is
`G(k)^1_{x+v} <= M(k)^1_{y+v}` for every `v in V(S/A_G)`;
the enlarged condition uses full point stabilizers for every
`v in V(S)`. The pointwise and parahoric conditions remain distinct.

Proposition 14.6.1, PDF pp.533–534, constructs a unique admissible
embedding of the enlarged buildings taking a specified adapted
pair `(x_tilde,y_tilde)` to one another. Uniqueness is relative to
that pair. The associated reduced map `phi:B(G)->B(M)` restricts
to the normalizer-fixed-orbit apartment map of 14.4.1; its partner
psi is the chosen Levi-building embedding into the enlarged
H-building. The quotient construction of 4.4.4 uses normalizer
equivariance and stabilizer compatibility at every apartment point.
Both terms of its equivalence relation must survive formalization.

Proposition 14.6.2 describes when different adapted pairs give the
same map. Example 14.0.3 obstructs a reduced admissible map from
the diagonal split torus into SL_2: its reduced building is a point,
but the torus fixes no point in the SL_2 tree. Its enlarged apartment
does embed after choosing an origin. Lemma 14.0.5 also permits
central translations for enlarged maps of isomorphic groups.
These remain source-backed regression targets.

For a general homomorphism f, the condition at book PDF p.523
requires the lift `f':G_sc -> f(G)_sc` on each k_s-simple factor
(equivalently each k-simple factor) to be trivial or an isomorphism
onto its image. The source first treats the faithfully flat quotient
onto f(G), then the closed immersion. Characteristic zero satisfies
the lift condition automatically; Frobenius in positive characteristic
need not. The resulting maps need not be injective or canonical.
These propositions supply equivariance, apartment derivatives and
stabilizer compatibility. Positive-depth Moy–Prasad comparisons
or morphisms of integral models require separate sources and proofs.

### Strict-Henselian existence and the separate general-k descent

Section 14.8 explicitly assumes strictly Henselian k. Proposition
14.8.4, PDF p.539, uses an absolutely special x_tilde in enlargedB(G)
and a finite Galois splitting extension l/k for both G and H,
without a tame hypothesis. Choose y1_tilde in enlargedB(H_l) with
`G(l)_{x_tilde} <= H(l)_{y1_tilde}`. Its closest point y_tilde in the
embedded **enlargedB(H)** gives an adapted pair. The rendered
proposition confirms the enlarged notation and full stabilizers.
This base building is not identified with the full Galois fixed
locus for an arbitrary ramified splitting extension.

Existence requires the absolutely special point from 7.11.4,
boundedness of its full stabilizer and the building fixed-point
theorem to obtain y1_tilde. The split construction in 14.8.2 uses
root lattices and homogeneous polynomial coordinates. Projection
in 14.8.3 then uses equivariance under group actions and translations
to establish the stabilizer condition at every translate.

For general k, 14.5.6 gives closedness and segment containment of
the adapted-y locus. Proposition 14.7.1 gives the space of embeddings
an evaluation-independent complete NPC metric. Proposition 14.7.2
uses nonemptiness to obtain an equivariant embedding by 1.1.19.
Proposition 14.7.3 applies this over the maximal unramified extension
and descends by Chapter 9. Corrected nonempty convexity does not
prove the needed nonemptiness; that comes from the existence
argument. This descent remains separate from tame descent in 12.9.2.

### Independent repairs in the nearest-point proof

Proposition 1.1.20, book PDF pp.38–40 and corrections PDF pp.1–3,
uses a complete NPC geodesic space and a nonempty closed convex
subset Y. Its projection exists uniquely, is continuous, and is
equivariant under isometries preserving Y setwise. These theorem
conclusions remain the target.

The corrected proof on corrections PDF p.2 prints the estimate
`d(y1,y2)^2 <= 2 epsilon (2r+epsilon)`, for points at distance less
than `r+epsilon` from x, where `r=inf_{y in Y} d(x,y)`.
This estimate fails for `X=Y=R`, `x=0`, `r=0`, `epsilon=1`,
`y1=-3/4`, `y2=3/4`: its left side is 9/4 and right side is 2.
It also fails with positive r: in the Euclidean plane, take Y the
line of height 1, `x=(0,0)`, `r=1`, `epsilon=1/2`, and
`y1=(-1,1)`, `y2=(1,1)`. Their distances are `sqrt(2)<3/2`,
but the squared separation is 4, greater than the proposed 5/2.

For their midpoint m in Y, the NPC inequality instead gives

`2r^2 + (1/2)d(y1,y2)^2 <= d(x,y1)^2+d(x,y2)^2 < 2(r+epsilon)^2`,

hence `d(y1,y2)^2 < 4 epsilon (2r+epsilon)`. This suffices for
the minimizing-sequence argument. The coefficient 4 is an
independently derived repair, separate from the authors' printed
coefficient 2.

The correction's continuity proof also uses a multiplicative error
relative to `r=d(x,pi(x))`, requiring the case r=0 separately.
For `x_n -> x`, put `q_n=d(x,pi(x_n))`. The squeeze
`r<=q_n<=d(x,x_n)+d(x_n,pi(x))` gives `q_n -> r`.
Applying the midpoint inequality to the two projections gives

`d(pi(x_n),pi(x))^2 <= 2(q_n^2-r^2)`.

This proves continuity also when r=0 without division by r.
Equivariance follows from uniqueness and the inverse isometry.
These are independent mathematical proof repairs to implement and
verify in Lean. They do not change the theorem statement, and this
source ledger records no formal proof or authors' erratum for them.

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
