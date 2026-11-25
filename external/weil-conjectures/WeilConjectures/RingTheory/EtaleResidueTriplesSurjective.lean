/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.RingTheory.EtaleResidueTriplesPolynomialLift

/-!
# The residue map of the pointed etale colimit is surjective

Source: Stacks Project, Algebra, Tag 04GW (lemma-strict-henselization-different),
last paragraph, and Tag 00UH (lemma-make-etale-map-prescribed-residue-field).
(blueprint: lem-weil-pbc-etale-triples-colimit-surjective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tag 04GW (lemma-strict-henselization-different),
last paragraph, and Tag 00UH (lemma-make-etale-map-prescribed-residue-field).

Proof: The image of ψ is a field: if ψ(x) is nonzero, x is a unit by the hypothesis,
so its inverse has image ψ(x)⁻¹. The image contains the image of R in K by cocone
compatibility and the compatibility defining each triple. It therefore contains the
image of κ(p), the fraction field of R/p. For any α in K its minimal polynomial over
κ(p) is monic and separable. Lift its coefficients from the image field to the colimit,
choosing leading coefficient 1. The resulting monic polynomial has α as a simple root
under ψ, since the minimal polynomial is separable. The root-lifting hypothesis gives
a root a in the colimit with ψ(a)=α. Thus ψ is surjective. No injectivity of R → C is
used; the argument applies to every prime p, including nonmaximal primes.
(blueprint: lem-weil-pbc-etale-triples-colimit-surjective). -/
theorem etaleResidueTriples_colimit_surjective
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c)
    (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom)
    (hunit : ∀ x : c.pt, ψ x ≠ 0 → IsUnit x)
    (hroot : ∀ f : Polynomial c.pt, f.Monic → ∀ a₀ : K,
      f.eval₂ ψ a₀ = 0 → f.derivative.eval₂ ψ a₀ ≠ 0 →
        ∃ a : c.pt, f.IsRoot a ∧ ψ a = a₀) :
    Function.Surjective ψ := by
  intro a₀
  obtain ⟨f, hf, hfa, hfd⟩ :=
    etaleResidueTriples_polynomial_lift R p K c hc ψ hψ hunit a₀
  obtain ⟨a, ha, hₐ⟩ := hroot f hf a₀ hfa hfd
  exact ⟨a, hₐ⟩

end AlgebraicGeometry.Scheme
