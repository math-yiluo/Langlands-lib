/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Coprime.Basic
import WeilConjectures.RingTheory.EtaleSectionIdempotentSplitting
import WeilConjectures.RingTheory.LiftMonicCoprimeFactorizationEtaleCore

/-!
# Lifting monic coprime factorizations after an étale extension

Source: Stacks Project, More on Algebra, Lemma Tag 0ALH
(blueprint: lem-weil-pbc-lift-monic-coprime-factorization-etale).
-/

@[expose] public section

universe u

namespace Polynomial

/-- A monic coprime factorization modulo an ideal lifts after an étale ring extension
whose canonical map on quotients is an isomorphism.
Source: Stacks Project, More on Algebra, Lemma Tag 0ALH
(blueprint: lem-weil-pbc-lift-monic-coprime-factorization-etale).

Proof (the six steps of the DAG node):
1. Choose the degrees of the two reduced factors. If `A/I` is zero, use the degree of
`f` and zero instead. Apply `lem-weil-pbc-universal-coprime-factorization-ring` to obtain
an étale universal algebra `B`, with monic coprime factors `G,H` of the image of `f`.
This algebra is already localized at the resultant, replacing the localization of
Stacks Tag 07M0 in the original proof.
2. Its universal property gives an `A`-algebra map `B → A/I` sending `G,H` to the given
factors. It is surjective because the quotient map `A → A/I` is surjective, and factors
through `B/IB` since it kills `IB`.
3. By `lem-weil-pbc-etale-quotient-base-change`, `B/IB` is étale over `A/I`. Apply
`lem-weil-pbc-etale-section-idempotent-splitting` to its section to obtain an idempotent
`e` whose localization is `A/I`, with the given section as the localization map.
4. Lift `e` to `b` in `B` and set `A' = B_b`. Its spectrum is an open subscheme of
`Spec B` by `lem-weil-pbc-principal-localization-open-immersion`, hence étale over
`Spec A` by `definition-torsion-sheaves--3`.
5. By `lem-weil-pbc-localization-quotient-commute`, `A'/IA'` is `(B/IB)_e`. The resulting
isomorphism to `A/I` is inverse to the canonical map induced by `A → A'`, as can be
checked on every element of `A`.
6. Map `G,H` to `A'`. Their images are monic and multiply to the image of `f`.
Their reductions agree with the prescribed factors under the canonical quotient map,
by the construction of the section and the isomorphism in step 5. -/
theorem exists_etale_lift_monic_coprime_factorization
    {A : Type u} [CommRing A] (I : Ideal A) (f : A[X]) (hf : f.Monic)
    (g₀ h₀ : (A ⧸ I)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀) (hcoprime : IsCoprime g₀ h₀) :
    ∃ (A' : Type u) (_ : CommRing A') (φ : A →+* A'),
      let J : Ideal A' := I.map φ
      let α : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ∧
        Function.Bijective α ∧
        ∃ g' h' : A'[X], g'.Monic ∧ h'.Monic ∧ f.map φ = g' * h' ∧
          g'.map (Ideal.Quotient.mk J) = g₀.map α ∧
          h'.map (Ideal.Quotient.mk J) = h₀.map α := by
  obtain ⟨A', _, φ, hE, hbij, g', h', hg', hh', hfac, hgred⟩ :=
    exists_etale_lift_monic_coprime_factorization_core I f hf g₀ h₀ hg₀ hh₀
      hfactor hcoprime
  let J : Ideal A' := I.map φ
  let α : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
  have hhred := lift_monic_coprime_factorization_h_reduction I f g₀ h₀ hg₀ hh₀ hfactor
    A' φ g' h' hfac hgred
  exact ⟨A', inferInstance, φ, hE, hbij, g', h', hg', hh', hfac, hgred, hhred⟩

end Polynomial
