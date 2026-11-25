/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.RingTheory.HomogeneousIndependenceLocalization
import WeilConjectures.RingTheory.HomogeneousIndependenceQuotient
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Height from homogeneous independence at a rational point

Source: the invariant-derivation argument in Waterhouse, *Introduction to Affine Group
Schemes*, §11.4, as recorded in `WeilConjectures.RingTheory.HopfAlgebra.Cartier`, and the
local dimension step of blueprint `lemma-connected-components-images-homomorphisms--3`, clause (2).
(blueprint: lem-wf-height-of-homogeneous-independence).
-/

@[expose] public section

open MvPolynomial

namespace AlgHom

private theorem local_dimension_of_homogeneous_independence
    {k : Type*} [Field k] (n : ℕ) :
    ∀ {R : Type*} [CommRing R] [Algebra k R] [IsNoetherianRing R] [IsLocalRing R]
      (x : Fin n → R),
      (∀ a : R, ∃ c : k, a - algebraMap k R c ∈ IsLocalRing.maximalIdeal R) →
      IsLocalRing.maximalIdeal R = Ideal.span (Set.range x) →
      (∀ (r : ℕ) (f : MvPolynomial (Fin n) k), f.IsHomogeneous r →
        aeval x f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) → f = 0) →
      ringKrullDim R = n := by
  induction n with
  | zero =>
    intro R _ _ _ _ x _ hgen _
    have hm : IsLocalRing.maximalIdeal R = ⊥ := by simpa using hgen
    simpa using ringKrullDim_eq_zero_of_isField
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm)
  | succ n ih =>
    intro R _ _ _ _ x hres hgen hind
    obtain ⟨hreg, hquot⟩ := IsLocalRing.homogeneous_independence_quotient x hres hgen hind
    have hx : x 0 ∈ IsLocalRing.maximalIdeal R := by
      rw [hgen]
      exact Ideal.mem_span_range_self
    let J : Ideal R := Ideal.span {x 0}
    have hJ : J ≠ ⊤ := by
      intro h
      have hle : J ≤ IsLocalRing.maximalIdeal R := Ideal.span_le.mpr
        (Set.singleton_subset_iff.mpr hx)
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hle))
    have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    have : IsLocalRing (R ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    let q : R →+* R ⧸ J := Ideal.Quotient.mk J
    let y : Fin n → R ⧸ J := fun i ↦ q (x i.succ)
    have hm : Ideal.map q (IsLocalRing.maximalIdeal R) =
        IsLocalRing.maximalIdeal (R ⧸ J) :=
      IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
    have hygen : IsLocalRing.maximalIdeal (R ⧸ J) = Ideal.span (Set.range y) := by
      rw [← hm, hgen, Ideal.map_span, ← Set.range_comp]
      apply le_antisymm
      · apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · have hz : q (x 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
            (Ideal.mem_span_singleton_self (x 0))
          change q (x 0) ∈ Ideal.span (Set.range y)
          rw [hz]
          exact Ideal.zero_mem _
        · exact Ideal.mem_span_range_self
      · apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact Ideal.subset_span ⟨i.succ, rfl⟩
    have hyind : ∀ (r : ℕ) (f : MvPolynomial (Fin n) k), f.IsHomogeneous r →
        aeval y f ∈ IsLocalRing.maximalIdeal (R ⧸ J) ^ (r + 1) → f = 0 := by
      intro r f hf hmem
      apply hquot r f hf
      simpa only [← hm] using hmem
    have hyres : ∀ a : R ⧸ J, ∃ c : k,
        a - algebraMap k (R ⧸ J) c ∈ IsLocalRing.maximalIdeal (R ⧸ J) := by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨c, hc⟩ := hres a
      refine ⟨c, ?_⟩
      rw [← hm]
      simpa only [map_sub, q, Ideal.Quotient.mk_algebraMap] using Ideal.mem_map_of_mem q hc
    have hd := ih y hyres hygen hyind
    have hdrop :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        hreg hx
    rw [← hdrop]
    change ringKrullDim (R ⧸ J) + 1 = ↑(n + 1)
    rw [hd]
    simp

/-- A polynomial associated graded ring has local dimension the number of its variables.

Source: the local dimension step of `lemma-connected-components-images-homomorphisms--3`, clause
(2), with regularity obtained from the homogeneous independence argument recorded in
`WeilConjectures.RingTheory.HopfAlgebra.Cartier` (Waterhouse, §11.4).

Proof in words: put `I = ker ε`. The map `ε` is onto, since it is a `k`-algebra map to
`k`, and identifies `A/I` with `k`. The spanning hypothesis implies, by induction on
`r` using products of elements of `I`, that every class in `I^r/I^(r+1)` is the value
of a homogeneous degree-`r` polynomial in the `xᵢ`. Its kernel is zero by the second
hypothesis. Multiplication respects these maps, so they give an isomorphism of graded
`k`-algebras from `k[Xᵢ]` to the associated graded algebra of `I`.

Localize at `I`. Every `I^r/I^(r+1)` is annihilated by `I`, hence is a `k`-vector space;
elements outside `I` act by a nonzero scalar, so localization changes none of these
quotients. Thus the local ring `A_I` has this same polynomial associated graded algebra.
Write `n` for the number of variables. The classes of the `xᵢ` generate the maximal
ideal modulo its square, so Nakayama makes their images generators of the maximal
ideal. Krull intersection makes this local ring separated for that ideal. If `n=0`,
Nakayama makes the maximal ideal zero, so the local ring is a field of dimension zero.
Otherwise choose `x₁`. Every nonzero element has finite adic order, and multiplication
by `x₁` increases its order by exactly one, because multiplication by `X₁` is injective
on the polynomial associated graded ring. Thus `x₁` is a nonzerodivisor and
`(x₁) ∩ m^r = x₁ m^(r-1)` for `r ≥ 1`. This strictness identifies the associated graded
ring of the quotient by `x₁` with `k[Xᵢ]/(X₁)`, a polynomial ring on `n-1` variables.
Induction gives dimension `n-1` for this quotient. The dimension-drop theorem for a
nonzerodivisor in the maximal ideal of a Noetherian local ring gives dimension `n`
for the local ring. This theorem is
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` in Mathlib. Finally the
dimension of `A_I` is the height of `I`, giving the asserted equality.
(blueprint: lem-wf-height-of-homogeneous-independence). -/
theorem height_ker_eq_card_of_homogeneous_independence
    {k A ι : Type*} [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
    [Fintype ι] (ε : A →ₐ[k] k) (x : ι → A)
    (hx : ∀ i, x i ∈ RingHom.ker ε)
    (hspan : ∀ a ∈ RingHom.ker ε, ∃ c : ι → k,
      a - ∑ i, algebraMap k A (c i) * x i ∈ RingHom.ker ε ^ 2)
    (hind : ∀ (r : ℕ) (f : MvPolynomial ι k), f.IsHomogeneous r →
      aeval x f ∈ RingHom.ker ε ^ (r + 1) → f = 0) :
    (RingHom.ker ε).height = Fintype.card ι := by
  classical
  have : (RingHom.ker ε).IsPrime := RingHom.ker_isPrime ε.toRingHom
  let R := Localization.AtPrime (RingHom.ker ε)
  let z : ι → R := fun i ↦ algebraMap A R (x i)
  obtain ⟨hres, hgen, hind'⟩ := ε.homogeneous_independence_localization (R := R) x hx hspan hind
  have hm : Ideal.map (algebraMap A R) (RingHom.ker ε) =
      IsLocalRing.maximalIdeal R := Localization.AtPrime.map_eq_maximalIdeal
  rw [hm] at hres hgen hind'
  let e := Fintype.equivFin ι
  let y : Fin (Fintype.card ι) → R := fun i ↦ z (e.symm i)
  have hygen : IsLocalRing.maximalIdeal R = Ideal.span (Set.range y) := by
    rw [show Set.range y = Set.range z from e.symm.surjective.range_comp z]
    exact hgen
  have hyind : ∀ (r : ℕ) (f : MvPolynomial (Fin (Fintype.card ι)) k),
      f.IsHomogeneous r → aeval y f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) → f = 0 := by
    intro r f hf hmem
    have hf' : (MvPolynomial.rename e.symm f).IsHomogeneous r := hf.rename_isHomogeneous
    change aeval (z ∘ e.symm) f ∈ _ at hmem
    have hzmem : aeval z (MvPolynomial.rename e.symm f) ∈
        IsLocalRing.maximalIdeal R ^ (r + 1) := by
      simpa only [aeval_rename] using hmem
    have hzero := hind' r _ hf' hzmem
    exact (MvPolynomial.rename_injective e.symm e.symm.injective) (hzero.trans (map_zero _).symm)
  have hd := local_dimension_of_homogeneous_independence (Fintype.card ι) y hres hygen hyind
  have hheight := IsLocalization.AtPrime.ringKrullDim_eq_height (RingHom.ker ε) R
  exact WithBot.coe_injective (hheight.symm.trans hd)

end AlgHom
