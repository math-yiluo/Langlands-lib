/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.SmoothLocalizationConormalSplit
import WeilConjectures.RingTheory.SmoothSplitComplementShrink
import WeilConjectures.RingTheory.PrescribedBasisFurtherLocalization

/-!
# Differential basis after a common further shrink

Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07C6.
-/

@[expose] public section

universe u

namespace Algebra

/-- After the prescribed conormal basis is obtained, a further shrink makes the
Kähler differentials free of complementary rank, preserving that conormal basis.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07C6, proof.
(blueprint: lem-weil-pbc-smooth-at-prime-free-conormal-basis-differential-data)

The split conormal sequence supplies a finite projective complement. Spread a
basis of that complement of rank n-c near q, and base change the prescribed
conormal basis to the common smaller principal open. Lift its defining element
from the quotient to the polynomial ring.
The previous assertion on the unchanged open was false: stably free complements
of free summands need not be free. -/
theorem exists_smoothAtPrime_differential_data
    (R : Type u) [CommRing R] (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) R)
    (a : MvPolynomial (Fin n) R)
    (V : Finset (Fin m)) (c : ℕ)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (ha : Ideal.Quotient.mk (Ideal.span (Set.range f)) a ∉
      q.asIdeal)
    (_hcard : V.card = c) (hbound : c ≤ min n m)
    (hsm : Algebra.Smooth R (Localization.Away
      (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))) :
    (∃ (e : Fin c ≃ V),
      ∃ b : Module.Basis (Fin c)
          (Localization.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
          (LocalizedModule.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)
            (Ideal.span (Set.range f)).Cotangent),
        ∀ j : Fin c,
          b j = LocalizedModule.mkLinearMap
            (Submonoid.powers
              (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))
            (Ideal.span (Set.range f)).Cotangent
            ((Ideal.span (Set.range f)).toCotangent
              ⟨f (e j).1,
                Ideal.subset_span ⟨(e j).1, rfl⟩⟩)) →
    ∃ a' : MvPolynomial (Fin n) R,
      Ideal.Quotient.mk (Ideal.span (Set.range f)) a' ∉ q.asIdeal ∧
      Algebra.Smooth R (Localization.Away
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) a')) ∧
      (∃ (e : Fin c ≃ V),
      ∃ b : Module.Basis (Fin c)
          (Localization.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) a'))
          (LocalizedModule.Away
            (Ideal.Quotient.mk (Ideal.span (Set.range f)) a')
            (Ideal.span (Set.range f)).Cotangent),
        ∀ j : Fin c,
          b j = LocalizedModule.mkLinearMap
            (Submonoid.powers
              (Ideal.Quotient.mk (Ideal.span (Set.range f)) a'))
            (Ideal.span (Set.range f)).Cotangent
            ((Ideal.span (Set.range f)).toCotangent
              ⟨f (e j).1,
                Ideal.subset_span ⟨(e j).1, rfl⟩⟩)) ∧
      Nonempty (Module.Basis (Fin (n - c))
      (Localization.Away
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) a'))
      (KaehlerDifferential R
        (Localization.Away
          (Ideal.Quotient.mk (Ideal.span (Set.range f)) a')))) := by
  classical
  intro hb
  obtain ⟨e, b, hb⟩ := hb
  let I := Ideal.span (Set.range f)
  let A := MvPolynomial (Fin n) R ⧸ I
  let ā : A := Ideal.Quotient.mk I a
  have : Smooth R (Localization.Away ā) := hsm
  obtain ⟨d, π, hd, hπ, hl, hinj, hsurj, hker, hs, hsplit⟩ :=
    smooth_localization_conormal_split R n I ā
  obtain ⟨t, ht, hsm', hdiff⟩ :=
    exists_smooth_split_complement_shrink R A ā q.asIdeal ha n c
      (le_trans hbound (min_le_left n m))
      (LocalizedModule.Away ā I.Cotangent) b hsm hsplit
  obtain ⟨t', ht'⟩ := Ideal.Quotient.mk_surjective t
  have hmul : Ideal.Quotient.mk I (a * t') = ā * t := by
    rw [map_mul, ht']
  obtain ⟨b', hb'⟩ := Module.Basis.exists_prescribed_basis_away_mul ā t
    (fun j : Fin c ↦ I.toCotangent
      ⟨f (e j).1, Ideal.subset_span ⟨(e j).1, rfl⟩⟩) b hb
  dsimp only [I] at hmul
  refine ⟨a * t', ?_, ?_, ?_, ?_⟩
  · rw [hmul]
    exact q.asIdeal.primeCompl.mul_mem ha ht
  · rw [hmul]
    exact hsm'
  · refine ⟨e, ?_⟩
    rw [hmul]
    exact (show ∃ b', ∀ j : Fin c,
      b' j = LocalizedModule.mkLinearMap (Submonoid.powers (ā * t)) I.Cotangent
        (I.toCotangent ⟨f (e j).1, Ideal.subset_span ⟨(e j).1, rfl⟩⟩) from ⟨b', hb'⟩)
  · rw [hmul]
    exact hdiff

end Algebra
