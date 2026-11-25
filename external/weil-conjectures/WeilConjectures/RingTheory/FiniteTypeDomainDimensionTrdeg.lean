/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRing
import WeilConjectures.Mathlib.RingTheory.NoetherNormalization

/-!
# Dimension of a finite type domain over a field

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00P0
(blueprint: lem-weil-pbc-finite-type-domain-dimension-trdeg).

## Main statement

The Krull dimension of a finite type domain `S` over a field `k` equals the
transcendence degree of its fraction field, and localization at a maximal
ideal has the same dimension.
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u v

/--
Dimension of a finite type domain over a field equals the transcendence degree
of its fraction field, with the same dimension at every maximal localization.
Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00P0
(blueprint: lem-weil-pbc-finite-type-domain-dimension-trdeg).

Proof route: write the finite type domain as a quotient of a polynomial ring;
the finite type domain local-dimension lemma gives a finite common dimension
for all maximal localizations. Noether normalization supplies an injective
finite map from a polynomial ring in `d` variables, and integrality preserves
Krull dimension; the polynomial-ring localization computes this dimension as
`d`. After localizing the finite module at the nonzero elements of the
polynomial subring, the resulting finite-dimensional domain is a field, hence
is the fraction field of the original domain. Thus the fraction field is
algebraic over the rational function field in the normalization variables;
those variables are a transcendence basis, so `Algebra.trdeg` is `d`, equal to
the ring dimension and to every maximal-localization dimension. This follows
the proof dependencies `lem-weil-pbc-finite-type-domain-dimension-local-ring`,
`lem-weil-pbc-noether-normalization-field`,
`lem-weil-pbc-finite-algebra-is-integral`,
`lem-weil-pbc-integral-injective-dimension-equal`,
`lem-weil-pbc-polynomial-ring-maximal-localization-dimension`,
`lem-weil-pbc-finite-dimensional-domain-is-field`,
`def-weil-pbc-transcendence-basis`, and
`def-kun-transcendence-degree`.
-/
theorem finiteType_domain_ringKrullDim_eq_trdeg
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S] :
    ∃ d : ℕ,
      ringKrullDim S = (d : WithBot ℕ∞) ∧
      Algebra.trdeg k (FractionRing S) = (d : Cardinal) ∧
      ∀ (m : Ideal S) [m.IsMaximal],
        ringKrullDim (Localization.AtPrime m) = (d : WithBot ℕ∞) := by
  obtain ⟨hlocal, ⟨d, hd, _⟩⟩ :=
    finiteTypeDomain_ringKrullDim_localizationAtMaximal (k := k) (S := S)
  have htr : Algebra.trdeg k S = (d : Cardinal) := by
    have h := Algebra.trdeg_eq_of_ringKrullDim_eq k S (hB := by simpa using hd)
    exact h
  have hfrac : Algebra.trdeg k (FractionRing S) = Algebra.trdeg k S := by
    letI : SMul k (FractionRing S) :=
      ⟨fun x z ↦ algebraMap S (FractionRing S) (algebraMap k S x) * z⟩
    letI : Algebra k (FractionRing S) :=
      { algebraMap := (algebraMap S (FractionRing S)).comp (algebraMap k S)
        commutes' := by
          intro x z
          change algebraMap S (FractionRing S) (algebraMap k S x) * z =
            z * algebraMap S (FractionRing S) (algebraMap k S x)
          exact mul_comm _ _
        smul_def' := by intro x z; rfl }
    letI : IsScalarTower k S (FractionRing S) :=
      ⟨by
        intro x y z
        simp only [Algebra.smul_def]
        change
          algebraMap S (FractionRing S) (algebraMap k S x * y) * z =
            algebraMap k (FractionRing S) x *
              (algebraMap S (FractionRing S) y * z)
        rw [map_mul]
        rw [show algebraMap k (FractionRing S) x =
          algebraMap S (FractionRing S) (algebraMap k S x) from rfl]
        simp [mul_assoc]⟩
    letI : Algebra.IsAlgebraic S (FractionRing S) :=
      IsLocalization.isAlgebraic (FractionRing S) (nonZeroDivisors S)
    have hz : Algebra.trdeg S (FractionRing S) = 0 :=
      trdeg_eq_zero_iff.mpr inferInstance
    have h := trdeg_add_eq (R := k) (S := S) (A := FractionRing S)
    calc
      Algebra.trdeg k (FractionRing S) = Algebra.trdeg k S +
          Algebra.trdeg S (FractionRing S) := h.symm
      _ = Algebra.trdeg k S := by rw [hz, add_zero]
  refine ⟨d, hd, hfrac.trans htr, ?_⟩
  intro m
  rw [← hd]
  exact hlocal m
