# Hasse–Arf evidence: complete closure reading

Supporting evidence for the [audit note](../anthropic-hasse-arf-audit.md). These records are development evidence, not mathematical acceptance.

The following is the audit’s contemporaneous reading record. Private path references identify the original experiment and are reconstructed by the reproduction procedure; they are not public module imports.

<!-- evidence-file: reading-notes.md -->

## reading-notes.md

SHA256 of the exact UTF-8 block: `48a51c0fed8da4becd336379c2ee03d33b67e021489323da548cf0e25b087eea`.

````markdown
# Reading notes, Worker 25

Closure ordinals refer to closure.json. Fully read: ALL 1–53. Ordinal 17's initially truncated lines 125–180 were subsequently read at lines 115–190. All 8,170 original source lines have now been read across the two activations.

1–5 (previous activation): ideal-inertia lower groups; rational phi and upper indexing; fixed subring locality and maximal ideal comap; Nat.card divisibility HasseArfChain; P2M utility elaboration aliases. No new axiom/native proof escape found in initial whole-closure textual scan.

6: rational phi segment interpolation, surjectivity and inverse/ceiling characterization. All hypotheses on finite group and local ring stated. The section Gates contains proved sanity examples and expected axiom outputs.
7: subgroup restriction is comap, membership definitional, subtype image is intersection. Helpful for later quotient adapters, not needed in our direct Hasse-Arf host bridge.
8–11: from assumed lower quotient compatibility, prove rational tower law by segment slopes, cardinal quotient/kernel formula and induction; then upper quotient compatibility via natural values of psi and ceiling index. These assumptions are subsequently supplied inside source closure. The host tower/quotient targets are not inputs to the direct bridge.
12: additive depth is infimum of valuations of sigma(x)-x; lower membership is i+1 <= depth; faithful action gives depth=top iff identity and finite eventual triviality.
13: faithful action on a ring realizes G as IsGaloisGroup over its fixed subring (invariance and scalar compatibility proved).
14: monogenic generator displacement divides all displacements, hence controls depth. Polynomial divisibility is the key; includes counterexamples for non-generators.
15–16: monogenic coset-depth lemma via orbit product polynomial. Its coefficients are H-fixed; opposite divisibilities compare displacement of a fixed-ring generator with product of coset displacements; addVal(product)=sum depths. Wrapper disables fixed-ring local instances globally.
17–18: counts lower memberships as truncated depth sums, chooses representative of maximum coset depth, and translates coset-depth and valuation-scaling identities to lower quotient equality at ceil(phi). Handles identity, depth zero and finite positive depth separately; not an assumed quotient theorem.
19–20: combine monogenic coset-depth and quotient comparison.
21: DifferentEqPowFiltrationSum statement and finite cutoff invariance; included at import boundary despite no need for different formula in our bridge.
22: full compatibility shim read, including Finsupp representations, AddAut multiplicative instances and action, old elliptic-sequence predicates, fixed-point notation, four primed ramification/inertia cardinality lemmas. Only block G is relevant to the cardinality route; bulk imports include irrelevant declarations. Preserve notices; later extraction should select only needed declarations, with independent review. Our patch changes only Finsupp injective map application to support compiling the whole source file.
52–53: abelian root reduces via cyclic quotients, establishes fixed-ring DVR and quotient faithful/residue hypotheses, then invokes cyclic root. Public wrapper keeps exact two-universe type.

## Private successful bridge

HasseArfAudit.lean in .private/drafts/hasse-arf-adapted passes as a complete private experiment. Source root and final adapter both have only propext, Classical.choice, Quot.sound. Source root check 4fe27a02-ebbe-447c-9d2a-43b91b2b8117; adapter a6772f3b-634c-4fad-92ec-3c7760dc0f24. The latter supplies #check @ types with pp.universes and #print axioms, retained in 08-bridge-check-output.txt. Its checker did not perform exact-target receipt validation: target_matches false is the no-statement-inspection default, not evidence of mismatched type. No publication or semantic acceptance yet.

The faithful action proof adapts Worker 40's private Galois.lean argument using fraction-ring hom extensionality. No need to identify the fixed subring with K's integers: the source theorem only requires its intrinsic fixed ring. FixedPoints.maximalIdeal_subring_eq_comap directly gives LiesOver. A finite target residue field, injective map from the fixed residue field and explicit Ideal.Quotient.field instances supply both field perfectness and separability. The raw quotient and IsLocalRing.ResidueField alias require explicit types in typeclass inference; terminal failed checks 05–07 record this. groups_eq is ext/rfl for every natural index. Both source and host use Nat.card, so Fintype.card conversion is unnecessary at this boundary. Source proof internals use Nat.card_eq_fintype_card where appropriate. phi_nat converts shifted range to Icc by induction, floor at natural i is i and the fractional term vanishes; i=0 is included without an extra hypothesis. Final cancellation uses lowerGroupOrder_pos 0 and produces n:Nat cast to Int.

## Current upstream errata check

2026-10-25 live GitHub API files saved under upstream-current/: root, head, all 11 issue/PR bodies (state=all, per_page=100), comments for 2/6/8/10/11 and checked-at. Main still 6e837e75355538c7f80bab5b956861e86c4eacc2. No root errata file or Hasse-Arf-specific report in this bounded current-source check. #2 has no substantive bug description or comments; #6 is definition import/build structure; #8/#10 report full build failures resolved after memory-map limit change (author/reporter comments); #11 is a proposed verification wrapper stale-WORK fix, explicitly not a defect in FLT, closed without source update. Our Lean service did not use the upstream comparator wrapper. Do not generalize to absence of all defects. Web sources: https://github.com/anthropics/fermats-last-theorem, /issues/10, /pull/11 (body via issues endpoint). Search results/root inspected using web tool too.


## Remaining closure reading completed

23–26: zeroth lower group equals inertia; its order equals ramification index via Compat block G. Finite fixed-ring extension is proved through faithful Galois action on fraction fields and finiteness of integral closure. Uniformizer valuation equals ramification index, then every element's valuation scales by its unit-times-uniformizer decomposition. Global fixed-ring local-instance resets in wrappers remain unchanged.
27–28: finite local DVR extension with separable residue extension is monogenic. Lift a primitive residue element and minimal polynomial; if its evaluation is not a uniformizer, perturb by a uniformizer and use derivative being a unit. A subalgebra containing a uniformizer and surjecting on residue is top via approximation and Nakayama (map_mkQ_eq_top). No completeness premise is smuggled in.
29–30: fixed subring DVR proved directly by choosing a least positive valuation, using the orbit product of a uniformizer to show existence; every nonzero invariant factors into its powers times a fixed unit. This avoids assuming a fixed-ring DVR.
31–32: instantiate monogenic coset identity and valuation scaling; intermediate fixed-ring residue separability descends through actual scalar towers. Proves lower quotient formula at ceil rational phi.
33–34: finite abelian character into complex units separates an element outside the next lower group; its kernel gives cyclic quotient. Upper compatibility makes the chosen break the last nontrivial quotient break; cyclic integrality transfers back. i=0 handled separately by empty sum. No local reciprocity or class-field assumption.
35–38: p-th power raises positive lower depth, by ideal-power induction/telescoping. Iteration plus eventual triviality proves wild inertia is a p-group.
39: uniformizer unit quotient cocycle, ideal-power membership, independence modulo next ideal power, and divisibility-based membership converses.
40–41: tame character from G0 to residue units; kernel G1. Perfect residue permits inertia-invariant representatives (orbit characteristic polynomial and Frobenius inverse); displacement of uniformizer divides every displacement. Finite subgroup of field units gives cyclic tame quotient and order prime to residual characteristic.
42–43: tame index divides each positive break when inertia elements commute. Repeats invariant representative lemma; commuting uniformizer cocycles force tame character values raised to break index to be one. Cyclic tame quotient generator yields divisibility.
44–45 (878+18 lines, read in 3 untruncated chunks): wild depth congruence (Sen-style). Frobenius lifts produce approximately invariant digits, uniformizer orbit products have controlled displacement, strong induction in n compares p-power depths. Assuming failure of the next congruence, a trace sum and finite digit expansion have unique lowest valuation distinct from the prescribed value, contradiction. All nonidentity and toNat finiteness hypotheses explicitly controlled; no finite G assumption needed for this local lemma. P2M namespace aliases extensively used but not modified.
46–47 (474+24 lines, read in 2 chunks): cyclic counting and Abel summation combine tame-index divisibility and wild p-power congruences. Count elements by orders in the cyclic wild group (totient prime-power counts), rewrite sum of group orders as filtered-depth counts. Coprime tame and wild factors multiply to card G0. Handles zero break separately; no division by possibly zero card.
48–49: cyclic source root dispatches characteristic zero (positive filtration has no jumps) and positive prime residue characteristic. Supplies all tame/wild prerequisites above. Repeats invariant-representative lemma; potential extraction/deduplication later requires separate review.
50–51: quotient faithful action on fixed subring via fraction fields (invariant numerator/denominator from orbit norm), Galois fixed-field correspondence. Double-fixed ring maps to global fixed ring; quotient residue maps prove separability and perfectness transfer. These satisfy the root's cyclic quotient hypotheses without additional arithmetic axioms.

No mathematical flaw was identified in this source reading and bridge audit, but it is not independent semantic acceptance. Proposed focused port route should separate base filtration/depth/fixed-ring definitions, source statement targets, quotient/monogenic and cyclic-wild proof blocks, abelian root, then exact host adapter. Do not bulk-port unrelated Compat blocks or assume a 53-file import closure is a declaration-minimal dependency proof.
````
