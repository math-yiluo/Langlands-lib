/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRelation
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCompatibleMapExists

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Uniqueness of a compatible global cocone across prime localization.
Source: Stacks Project, Tag 04GW (pointed triples), Section 10.9 (localization
universal property), and Tag 00U2 (3) (etale base change).
(blueprint: new-lem-sbc-etale-triples-prime-localization-cocone-restriction-unique)

Proof: Fix a global triple s. Localize B_s at the images of R outside p to obtain
C_s with canonical map i_s. This is A tensor_R B_s for A = R_p, so it is etale
over A. The pointing B_s to K sends these denominators to nonzero elements:
its restriction to R is evaluation at p followed by χ, whose kernel is p.
It therefore extends by the fraction formula to C_s to K. Take its prime kernel
and the induced embedding of its residue field into K. The resulting pointing
on A equals the specified A-algebra map, since by hK they agree on R and A is
a localization. Its kernel on A equals q by hψ and injectivity of ψ. This makes
C_s a local triple t_s, and i_s satisfies the structural-map and pointing
equations required by the cocone relation. Apply hη and hη' to this same i_s.
They give η.app s = i_s followed by θ.app t_s = η'.app s. Since this holds for
every s, extensionality of natural transformations yields η = η'. No cancellation
of i_s or assumption that B_s to C_s is injective is needed. -/
theorem etaleResidueTriples_primeLocalization_cocone_restriction_unique
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
    (θ : etaleResidueTriplesRingDiagram
      (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
        (Functor.const _).obj V)
    (η η' : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (hη : etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η θ)
    (hη' : etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η' θ) :
    η = η' := by
  apply NatTrans.ext
  funext s
  obtain ⟨t, β, hα, hφ⟩ :=
    etaleResidueTriples_primeLocalization_compatible_map_exists
      R p K χ q ψ hψ hK s
  have eη := hη s t β hα hφ
  have eη' := hη' s t β hα hφ
  rw [← eη, ← eη']

end AlgebraicGeometry.Scheme
