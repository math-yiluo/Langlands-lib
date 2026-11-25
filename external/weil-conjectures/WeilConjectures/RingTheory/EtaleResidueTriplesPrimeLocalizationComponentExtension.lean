/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionExists
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationExtensionUnique

/-! # Extension of a single pointed étale cocone leg

Source: Stacks Project, Tags 00CR, 01ZM, 07RP, 01Z6 and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-component-extension)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A global cocone determines a unique compatible ring map on each local triple.
Source: Stacks Project, Tags 00CR, 01ZM, 07RP, 01Z6 and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-component-extension)

Proof: By the principal-localization colimit theorem (00CR), R_p is the filtered
colimit of R_s for s outside p. Finite-data descent (01ZM, 07RP) gives an étale
R_s-model of Spec t.B. On its upper tail the base changes form a qcqs inverse
system with affine transitions and affine limit Spec t.B. The affine-limit
lemma Scheme.exists_isAffine_of_isLimit (01Z6) makes the model affine at a
later stage. Write it as Spec C, so C ⊗[R_s] R_p is isomorphic to t.B.
As R_s is étale over R,
C is étale over R. Restrict the pointing t.B → K to C. Its kernel is prime;
factorization through its residue field produces a global triple c. The base
compatibilities hψ and hK show that its prime lies over p.
For every r outside p, its image in C is outside the pointing's kernel:
the base pointing has kernel p, since χ is an injective field map. Apply
etaleResidueTriple_unit_refinement to obtain a global morphism c → c' taking
that image to a unit. Naturality identifies the leg on C with the composite
C → c'.B → V; ring maps preserve units, so the leg sends that image to a unit.
The localization universal property extends that leg uniquely to C ⊗[R_s] R_p = t.B.
For any pointed global map β : s.B → t.B, descend β to some later principal
stage: s.B is finitely presented over R. Refine c and s by that denominator.
Global-cocone naturality at the descended arrow identifies their legs.
Restriction of the extended map to β is thus exactly η.app s, proving the
asserted compatibility for all s and β. Finally every compatible ring map
restricts on the chosen model C to η.app c. Localization uniqueness implies
equality of the maps on t.B. No cocone on local triples, nor its naturality,
is assumed or constructed in this lemma. -/
theorem etaleResidueTriples_primeLocalization_component_extension
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (V : CommRingCat.{u})
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ) :
    ∃! b : t.B ⟶ V,
      ∀ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
        s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
          t.α →
        β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
        β ≫ b = η.app s := by
  obtain ⟨b, hb⟩ :=
    etaleResidueTriples_primeLocalization_component_extension_exists
      R p K χ q ψ hψ hK V η t
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  exact (etaleResidueTriples_primeLocalization_component_extension_unique
    R p K χ q ψ hψ hK V η t b b' hb hb').symm

end AlgebraicGeometry.Scheme
