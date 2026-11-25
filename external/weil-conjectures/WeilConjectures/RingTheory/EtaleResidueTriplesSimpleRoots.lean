/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.RingTheory.EtaleResidueTriplesSimpleRootsConstruction

/-!
# Simple roots lift in the pointed etale colimit

Source: Stacks Project, Algebra, Tag 04GN (lemma-henselization), last paragraph,
with triples as prescribed by Tag 04GP (lemma-strict-henselization).
(blueprint: lem-weil-pbc-etale-triples-colimit-simple-roots).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tag 04GN (lemma-henselization), last paragraph,
with triples as prescribed by Tag 04GP (lemma-strict-henselization).

Proof: Filteredness lets all coefficients of the monic polynomial f descend to one
triple t, with the leading coefficient chosen to be 1. Write the resulting monic
polynomial as Q over its ring S. The standard etale S-algebra S[T,1/Q']/(Q) has its
universal root x. The simple root a₀ in K defines a map of this algebra to K because
Q(a₀)=0 and Q'(a₀) is invertible. Its kernel and residue embedding give a later triple,
and its structure map is a morphism from t. Map x into the colimit: compatibility
shows f(x)=0 there and ψ(x)=a₀. This also covers constant monic polynomials, whose
root hypothesis is impossible.
(blueprint: lem-weil-pbc-etale-triples-colimit-simple-roots). -/
theorem etaleResidueTriples_colimit_simple_roots
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c)
    (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) :
    ∀ f : Polynomial c.pt, f.Monic → ∀ a₀ : K,
      f.eval₂ ψ a₀ = 0 → f.derivative.eval₂ ψ a₀ ≠ 0 →
        ∃ a : c.pt, f.IsRoot a ∧ ψ a = a₀ := by
  intro f hf a₀ hfa hdfa
  obtain ⟨t, x, hx, hψx⟩ :=
    etaleResidueTriples_simple_root_stage R p K c hc ψ hψ f hf a₀ hfa hdfa
  exact ⟨c.ι.app t x, hx, hψx⟩

end AlgebraicGeometry.Scheme
