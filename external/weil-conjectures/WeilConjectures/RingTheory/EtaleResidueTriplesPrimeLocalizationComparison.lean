/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeEquiv

/-! # Comparison of residue-triple colimits across prime localization

Source: Stacks Project, Tags 04GW, 00CR, 01ZM and 07RP.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Localization of the base preserves the ring colimit of pointed etale triples.
Source: Stacks Project, Tag 04GW, localization argument, with Tags 00CR, 01ZM and 07RP.
(blueprint: new-lem-sbc-etale-triples-prime-localization-comparison)

Proof: Put A = R_p. Apply `CommRingCat.localization_colimit_principalLocalizations`
to the complement of p. This expresses A as the filtered colimit of R_s, s outside p.
Apply the objects, morphisms and equalities clauses of `etale_finite_data_descent`
to the corresponding affine inverse system. Every finitely presented etale A-algebra
B descends to an etale R_s-algebra B_s. Its pointing to K restricts to B_s, since
R_s to K is forced by the given R to A to K compatibility and invertibility of s.
The kernel and unique residue-field factorization of this pointing make B_s an
R-triple. Composition with the etale principal localization R to R_s remains etale.
Morphisms between two descended objects descend at a common later principal stage;
the compatibility with their pointings holds by evaluating the given A-morphism in K.
Two descents of the same object are identified after refining: descend the comparison
isomorphism and its inverse, then descend their two inverse relations. Likewise any
equality of descended morphisms holds after a further refinement. Thus a cocone over
the R-triples determines, independently of every descent choice, a cocone over the
A-triples, and conversely localization of each R-triple B at R outside p determines
an A-triple. The map B to this localization is the filtered colimit of the pointed
principal refinements B_s, all of which are R-triples; their primes and pointings
extend because the denominators map to units in K. Naturality gives the inverse
cocone identifications. They preserve the underlying vertex and maps between vertices.
Transport the universal cocone c through this correspondence and through e. Its
local legs respect the prescribed A-map: they agree with it on R by naturality
from the identity triple, and uniqueness of localization extends the equality to A.
Consequently the transported natural transformation iota has vertex C and satisfies
both the ring-colimit universal property and the asserted structural-map equations.
This comparison requires no separable-closure hypothesis and constructs no strict
henselization; the supplied algebra map on C is kept fixed throughout. -/
theorem etaleResidueTriples_primeLocalization_comparison
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (c : Cocone (etaleResidueTriplesRingDiagram R p K χ)) (hc : IsColimit c)
    (C : CommRingCat.{u}) (e : c.pt ≅ C)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    [Algebra (Localization.AtPrime p.asIdeal) C]
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (hC : ∀ r : R, algebraMap (Localization.AtPrime p.asIdeal) C
      (algebraMap R (Localization.AtPrime p.asIdeal) r) =
        (c.ι.app ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩ ≫ e.hom).hom r) :
    ∃ (ι : etaleResidueTriplesRingDiagram
        (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
        (Functor.const _).obj C),
      Nonempty (IsColimit (Cocone.mk C ι)) ∧
      ∀ t, t.α ≫ ι.app t =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) C) := by
  classical
  obtain ⟨E, hE, hR⟩ :=
    etaleResidueTriples_primeLocalization_coconeEquiv R p K χ q ψ hψ hK
  let η := c.ι ≫ (Functor.const _).map e.hom
  let ι := E C η
  have hη : IsColimit (Cocone.mk C η) := IsColimit.extendIso e.hom hc
  have hι : IsColimit (Cocone.mk C ι) :=
    { desc := fun s ↦ hη.desc (Cocone.mk s.pt ((E s.pt).symm s.ι))
      fac := fun s t ↦ by
        have h : η ≫ (Functor.const _).map
            (hη.desc (Cocone.mk s.pt ((E s.pt).symm s.ι))) = (E s.pt).symm s.ι := by
          apply NatTrans.ext
          funext j
          exact hη.fac _ j
        have h' := congrArg (E s.pt) h
        rw [hE, (E s.pt).apply_symm_apply] at h'
        exact congrArg (fun x ↦ x.app t) h'
      uniq := fun s m hm ↦ by
        apply hη.uniq (Cocone.mk s.pt ((E s.pt).symm s.ι)) m
        have h : ι ≫ (Functor.const _).map m = s.ι := by
          apply NatTrans.ext
          funext t
          exact hm t
        have h' : η ≫ (Functor.const _).map m = (E s.pt).symm s.ι := by
          apply (E s.pt).injective
          rw [hE, (E s.pt).apply_symm_apply]
          exact h
        intro t
        exact congrArg (fun x ↦ x.app t) h' }
  refine ⟨ι, ⟨hι⟩, ?_⟩
  intro t
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (p.asIdeal.primeCompl)
  ext r
  exact (hR C η t r).trans (hC r).symm

end AlgebraicGeometry.Scheme
