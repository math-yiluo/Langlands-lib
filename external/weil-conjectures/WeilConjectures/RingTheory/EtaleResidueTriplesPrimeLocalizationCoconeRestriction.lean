/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRelation
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRestrictionExists
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRestrictionUnique

/-! # Compatible cocone legs across prime localization -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Every local cocone has a unique global cocone with compatible pointed legs.
Source: Stacks Project, Tags 00CR and 04GW.
(blueprint: new-lem-sbc-etale-triples-prime-localization-cocone-restriction)

Proof: Localize each pointed R-triple B at the images of R outside p. This is an
etale R_p-algebra by base change. The pointing extends to K because denominators
are nonzero there; its kernel has inverse image q, by injectivity of the residue
field maps and the compatibility of the two base pointings. Factor it uniquely
through its residue field. Restrict the local cocone leg along B to this localized
triple. Every morphism of global triples localizes, so the restricted legs are
natural. Every compatible map B to any local triple extends uniquely from this
localization, and local-cocone naturality proves compatibility. Finally the
canonical maps into the localized triples force every compatible global cocone
leg to be this restriction, proving uniqueness. -/
theorem etaleResidueTriples_primeLocalization_cocone_restriction
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
        (Functor.const _).obj V) :
    ∃! η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V,
      etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η θ := by
  obtain ⟨η, hη⟩ := etaleResidueTriples_primeLocalization_cocone_restriction_exists
    R p K χ q ψ hψ hK V θ
  refine ⟨η, hη, ?_⟩
  intro η' hη'
  exact (etaleResidueTriples_primeLocalization_cocone_restriction_unique
    R p K χ q ψ hψ hK V θ η η' hη hη').symm

end AlgebraicGeometry.Scheme
