/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.SmoothAtPrimeConormalData
import WeilConjectures.RingTheory.SmoothAtPrimeDifferentialData

/-!
# Free conormal basis near a smooth prime

Source: literature/stacks-project/smoothing.tex, Lemma Tag 07C6
(blueprint: lem-weil-pbc-smooth-at-prime-free-conormal-basis).
-/

@[expose] public section

universe u

namespace Algebra

/-- Near a smooth prime of a polynomial quotient, selected defining equations form a
basis of the localized conormal module, and the differentials are free of complementary rank.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07C6
(blueprint: lem-weil-pbc-smooth-at-prime-free-conormal-basis).

Proof, following the four steps of the node:
1. Choose a smooth principal neighbourhood using `IsSmoothAtPrime`. The lemma
   `lem-weil-pbc-smooth-localization-conormal-split` makes the conormal module and the
   differential module direct summands of the free module of rank n, hence finite projective.
2. The given relations span the conormal fibre at q. Choose a subset V giving a basis
   of cardinality c. Tensoring the split sequence with the residue field shows c ≤ n
   and differential fibre dimension n-c; the subset condition also gives c ≤ m.
3. Finite projective modules are finitely presented and locally free
   (`lem-weil-pbc-finite-projective-finitely-presented` and
   `lem-weil-pbc-finite-projective-rank-locally-constant`). The conormal rank at q is c.
   Use `lem-weil-pbc-prescribed-residue-basis-spreads` to spread the selected classes
   to a basis outside q. Clear denominators and combine localization elements.
   Smoothness persists by `lem-weil-pbc-smooth-ring-map-principal-localization`.
4. Apply `lem-weil-pbc-finitely-presented-free-at-prime-spreads` to the differential
   module of rank n-c. Clear denominators and take a common shrink, preserving the
   selected conormal basis and smoothness. Identify the resulting differentials using
   `lem-weil-pbc-kahler-differentials-localization`.
-/
theorem exists_smoothAtPrime_free_conormal_basis
    (R : Type u) [CommRing R] (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) R)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (hs : Algebra.IsSmoothAtPrime R q) :
    ∃ (a : MvPolynomial (Fin n) R),
      Ideal.Quotient.mk (Ideal.span (Set.range f)) a ∉ q.asIdeal ∧
      ∃ (V : Finset (Fin m)) (c : ℕ),
        V.card = c ∧ c ≤ min n m ∧
        Algebra.Smooth R
          (Localization.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)) ∧
        (∃ (e : Fin c ≃ V),
          ∃ b : Module.Basis (Fin c)
              (Localization.Away
                (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
              (LocalizedModule.Away
                (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)
                (Ideal.span (Set.range f)).Cotangent),
            ∀ j : Fin c,
              b j =
                LocalizedModule.mkLinearMap
                  (Submonoid.powers
                    (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
                  (Ideal.span (Set.range f)).Cotangent
                  ((Ideal.span (Set.range f)).toCotangent
                    ⟨f (e j).1,
                      Ideal.subset_span ⟨(e j).1, rfl⟩⟩)) ∧
        Nonempty (Module.Basis (Fin (n - c))
          (Localization.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
          (KaehlerDifferential R
            (Localization.Away
              (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)))) := by
  rcases exists_smoothAtPrime_conormal_data R n m f q hs with
    ⟨a, ha, V, c, hcard, hbound, hsm, hb⟩
  obtain ⟨a', ha', hsm', hb', hdiff⟩ :=
    exists_smoothAtPrime_differential_data R n m f a V c q ha hcard hbound hsm hb
  exact ⟨a', ha', V, c, hcard, hbound, hsm', hb', hdiff⟩

end Algebra
