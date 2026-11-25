/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse
public import WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots
public import WeilConjectures.ZetaLinearAlgebra.WeilNumbers

/-!
# Galois weight strata of an integral polynomial

Let `ℚ̄ = AlgebraicClosure ℚ`. For an integer polynomial `C` with `C(0) = 1`, its reciprocal roots
are the roots in `ℚ̄` of the reversed polynomial `C^# = C.reverse`. For `q ∈ ℕ` and a weight `i`,
the *weight stratum* `R_i(C)` is the submultiset of those reciprocal roots that are `q`-Weil
numbers of weight `i`. This file shows (blueprint `sk-thm-intfactors`):

- `R_i(C)` is stable under `Gal(ℚ̄/ℚ)` (`theorem-weil-conjectures-smooth-proper-schemes--1`);
- the stratum polynomial `Q_i = ∏_{α ∈ R_i} (1 - α T)` has integer coefficients
  (`theorem-weil-conjectures-smooth-proper-schemes--1`), since its coefficients are Galois-invariant
  algebraic integers;
- the reciprocal-root multiset of `Q_i` is exactly `R_i`
  (`theorem-weil-conjectures-smooth-proper-schemes--1`).

It also records the `ℓ`-adic realizations of algebraic numbers (`lemma-reciprocal-roots-zeta--7`):
inside an algebraically closed field `Ω` of characteristic zero (such as `ℚ̄_ℓ`), the elements
algebraic over `ℚ` form an algebraic closure of `ℚ`, which is therefore isomorphic to `ℚ̄`.

In the blueprint, `R_i` is formed from the numerator `A` for odd `i` and from the denominator
`B` for even `i` of a normalized presentation `Z = A / B`; this is `Polynomial.parityWeilStratum`.

## Main declarations

- `AlgebraicRealization`, `algebraicClosure_isAlgClosure_and_nonempty_realization`:
  blueprint `lemma-reciprocal-roots-zeta--7`.
- `Polynomial.weilStratum`, `Polynomial.weilStratumPoly`: the stratum `R_i(C)` and the
  polynomial `∏_{α ∈ R_i} (1 - α T)`.
- `Polynomial.map_weilStratum_algEquiv`: blueprint
`theorem-weil-conjectures-smooth-proper-schemes--1`.
- `Polynomial.exists_map_eq_weilStratumPoly`: blueprint
  `theorem-weil-conjectures-smooth-proper-schemes--1`.
- `Polynomial.roots_reverse_weilStratumPoly`: blueprint
  `theorem-weil-conjectures-smooth-proper-schemes--1`.
-/

@[expose] public section

open Polynomial

/-! ### `ℓ`-adic realizations of algebraic numbers -/

section Realization

variable (Ω : Type*) [Field Ω] [CharZero Ω]

/-- Blueprint `lemma-reciprocal-roots-zeta--7`: an *`ℓ`-adic realization of algebraic numbers* in
a field `Ω` of characteristic zero (in the application `Ω = ℚ̄_ℓ`) is a `ℚ`-isomorphism
`ℚ̄ ≃ ℚ̄^{(ℓ)}` from the fixed algebraic closure `ℚ̄ = AlgebraicClosure ℚ` onto the subfield
`ℚ̄^{(ℓ)} = algebraicClosure ℚ Ω` of elements of `Ω` that are algebraic over `ℚ`. -/
abbrev AlgebraicRealization : Type _ :=
  AlgebraicClosure ℚ ≃ₐ[ℚ] _root_.algebraicClosure ℚ Ω

/-- Blueprint `lemma-reciprocal-roots-zeta--7`: if `Ω` is an algebraically closed field of
characteristic zero (e.g. `PadicAlgCl ℓ`), then the subfield `ℚ̄^{(ℓ)}` of elements of `Ω`
algebraic over `ℚ` is algebraically closed and is an algebraic closure of `ℚ`, and an
`ℓ`-adic realization `ℚ̄ ≃ₐ[ℚ] ℚ̄^{(ℓ)}` exists. -/
theorem algebraicClosure_isAlgClosure_and_nonempty_realization [IsAlgClosed Ω] :
    IsAlgClosed (_root_.algebraicClosure ℚ Ω) ∧
      IsAlgClosure ℚ (_root_.algebraicClosure ℚ Ω) ∧
      Nonempty (AlgebraicRealization Ω) :=
  ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance,
    ⟨IsAlgClosure.equiv ℚ (AlgebraicClosure ℚ) (_root_.algebraicClosure ℚ Ω)⟩⟩

end Realization

/-! ### Weight strata -/

namespace Polynomial

/-- The roots in `ℚ̄` of a polynomial with integer coefficients are permuted by `Gal(ℚ̄/ℚ)`. -/
theorem roots_map_algebraMap_map_algEquiv (D : ℤ[X])
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (D.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots.map σ =
      (D.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots := by
  set D' := D.map (algebraMap ℤ (AlgebraicClosure ℚ))
  have hD : D'.map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) = D' := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have h := roots_map_of_injective_of_card_eq_natDegree
    (f := (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) σ.injective
    ((splits_iff_card_roots).mp (IsAlgClosed.splits D'))
  rw [hD] at h
  exact h

variable (q : ℕ) (i : ℤ)

open scoped Classical in
/-- The *weight-`i` stratum* `R_i(C)` of an integer polynomial `C` (blueprint
`theorem-weil-conjectures-smooth-proper-schemes--1`): the submultiset of the reciprocal roots of `C`
in `ℚ̄ = AlgebraicClosure ℚ`, i.e. of the roots of `C^# = C.reverse`, that are `q`-Weil numbers of
weight `i`, counted with multiplicity. -/
noncomputable def weilStratum (C : ℤ[X]) : Multiset (AlgebraicClosure ℚ) :=
  ((C.reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots).filter (IsWeilNumber q i)

/-- The *stratum polynomial* `Q_i = ∏_{α ∈ R_i(C)} (1 - α T)` over `ℚ̄` (blueprint
`theorem-weil-conjectures-smooth-proper-schemes--1`). -/
noncomputable def weilStratumPoly (C : ℤ[X]) : (AlgebraicClosure ℚ)[X] :=
  ((weilStratum q i C).map fun α ↦ 1 - Polynomial.C α * X).prod

/-- The parity convention of the blueprint (`theorem-weil-conjectures-smooth-proper-schemes--1`):
for a normalized presentation `Z = A / B`, the weight-`i` stratum is taken in the reciprocal roots
of the numerator `A` for odd `i` and of the denominator `B` for even `i`. -/
noncomputable def parityWeilStratum (A B : ℤ[X]) : Multiset (AlgebraicClosure ℚ) :=
  weilStratum q i (if Odd i then A else B)

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes--1`: the weight stratum `R_i(C)` of an
integer polynomial is stable, with multiplicities, under every `σ ∈ Gal(ℚ̄/ℚ)`. Indeed the roots of
the rational polynomial `C^#` are permuted by `σ`, and the `q`-Weil condition of weight `i` is
Galois-invariant (`isWeilNumber_algEquiv_apply_iff`). The same holds for the parity strata
`parityWeilStratum q i A B`, which are instances of `weilStratum`. -/
theorem map_weilStratum_algEquiv (C : ℤ[X]) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (weilStratum q i C).map σ = weilStratum q i C := by
  classical
  unfold weilStratum
  conv_rhs => rw [← roots_map_algebraMap_map_algEquiv C.reverse σ]
  rw [Multiset.filter_map]
  congr 1
  refine Multiset.filter_congr fun α _ ↦ ?_
  exact (isWeilNumber_algEquiv_apply_iff σ).symm

/-- The stratum polynomial is invariant under `Gal(ℚ̄/ℚ)`. -/
theorem map_weilStratumPoly_algEquiv (C : ℤ[X])
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (weilStratumPoly q i C).map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) =
      weilStratumPoly q i C := by
  unfold weilStratumPoly
  rw [map_multiset_prod_one_sub_C_mul_X]
  exact congrArg (fun s ↦ (s.map fun α ↦ 1 - Polynomial.C α * X).prod)
    (map_weilStratum_algEquiv q i C σ)

/-- For `C(0) = 1`, the reciprocal roots of `C` are algebraic integers. -/
theorem isIntegral_of_mem_weilStratum {C : ℤ[X]} (hC : C.coeff 0 = 1) {α : AlgebraicClosure ℚ}
    (hα : α ∈ weilStratum q i C) : IsIntegral ℤ α := by
  classical
  have hα' := (mem_roots'.1 (Multiset.mem_of_mem_filter hα)).2
  refine ⟨C.reverse, monic_reverse_of_coeff_zero_eq_one hC, ?_⟩
  rwa [IsRoot, eval_map] at hα'

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes--1`: for an integer polynomial `C`
with `C(0) = 1` (as for both members of a normalized presentation `Z = A / B`), the stratum
polynomial `Q_i = ∏_{α ∈ R_i(C)} (1 - α T)` has integer coefficients. Its coefficients are
fixed by `Gal(ℚ̄/ℚ)` (`theorem-weil-conjectures-smooth-proper-schemes--1`), hence rational, and are
algebraic integers, being elementary symmetric functions of roots of the monic integer polynomial
`C^#`; so they lie in `ℤ`. -/
theorem exists_map_eq_weilStratumPoly {C : ℤ[X]} (hC : C.coeff 0 = 1) :
    ∃ Q : ℤ[X], Q.map (algebraMap ℤ (AlgebraicClosure ℚ)) = weilStratumPoly q i C := by
  set S := integralClosure ℤ (AlgebraicClosure ℚ)
  -- the coefficients are algebraic integers
  have hint : weilStratumPoly q i C ∈ lifts (algebraMap S (AlgebraicClosure ℚ)) := by
    refine Subsemiring.multiset_prod_mem _ _ fun p hp ↦ ?_
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hp
    refine (mem_lifts _).2 ⟨1 - Polynomial.C ⟨α, isIntegral_of_mem_weilStratum q i hC hα⟩ * X, ?_⟩
    simp
  -- each coefficient is a rational algebraic integer, hence an integer
  refine (mem_lifts _).1 ((lifts_iff_coeff_lifts _).2 fun n ↦ ?_)
  have hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ((weilStratumPoly q i C).coeff n) = (weilStratumPoly q i C).coeff n := fun σ ↦ by
    conv_rhs => rw [← map_weilStratumPoly_algEquiv q i C σ]
    rw [coeff_map]
    rfl
  obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  obtain ⟨s, hs⟩ := (lifts_iff_coeff_lifts _).1 hint n
  have hrint : IsIntegral ℤ r := by
    have h : IsIntegral ℤ (algebraMap ℚ (AlgebraicClosure ℚ) r) := by
      rw [hr, ← hs]
      exact s.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ (AlgebraicClosure ℚ))
      (algebraMap ℚ (AlgebraicClosure ℚ)).injective).1 h
  obtain ⟨m, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hrint
  exact ⟨m, by rw [← hr, ← IsScalarTower.algebraMap_apply]⟩

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes--1`: the reciprocal-root multiset of
the stratum polynomial `Q_i`, i.e. the root multiset of `Q_i^# = Q_i.reverse`, is exactly the
weight stratum `R_i(C)`. The stratum polynomial is normalized: `Q_i(0) = 1`. -/
theorem roots_reverse_weilStratumPoly (C : ℤ[X]) :
    (weilStratumPoly q i C).reverse.roots = weilStratum q i C ∧
      (weilStratumPoly q i C).coeff 0 = 1 := by
  classical
  have h0 : (0 : AlgebraicClosure ℚ) ∉ weilStratum q i C := fun h ↦ by
    have h' := Multiset.mem_of_mem_filter h
    rw [← reverse_map (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int] at h'
    exact ne_zero_of_mem_roots_reverse h' rfl
  refine ⟨?_, ?_⟩
  · rw [weilStratumPoly, reverse_multiset_prod_one_sub_C_mul_X h0, roots_multiset_prod_X_sub_C]
  · rw [weilStratumPoly, coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
    simp

/-- Blueprints `theorem-weil-conjectures-smooth-proper-schemes--1` and
`theorem-weil-conjectures-smooth-proper-schemes--1` combined: for `C ∈ ℤ[X]` with `C(0) = 1` there
is an integer polynomial `Q` with `Q(0) = 1` whose scalar extension to `ℚ̄` is
`∏_{α ∈ R_i(C)} (1 - α T)` and whose reciprocal-root multiset in `ℚ̄` is exactly `R_i(C)`. -/
theorem exists_int_weilStratumPoly {C : ℤ[X]} (hC : C.coeff 0 = 1) :
    ∃ Q : ℤ[X], Q.coeff 0 = 1 ∧
      Q.map (algebraMap ℤ (AlgebraicClosure ℚ)) = weilStratumPoly q i C ∧
      (Q.map (algebraMap ℤ (AlgebraicClosure ℚ))).reverse.roots = weilStratum q i C := by
  obtain ⟨Q, hQ⟩ := exists_map_eq_weilStratumPoly q i hC
  obtain ⟨h1, h2⟩ := roots_reverse_weilStratumPoly q i C
  refine ⟨Q, ?_, hQ, hQ ▸ h1⟩
  apply (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int
  rw [← coeff_map, hQ, h2, map_one]

section Products

variable {q} {ι : Type*} (s : Finset ι) (P : ι → ℤ[X]) (w : ι → ℤ)

/-- **Weight strata of a product.** Let `Pₖ`, `k ∈ s`, be integer polynomials with `Pₖ(0) = 1`
all of whose complex reciprocal roots have absolute value `q^{wₖ/2}`, the weights `wₖ` being
pairwise distinct. Then the weight-`wⱼ` stratum of `∏ₖ Pₖ` is the multiset of reciprocal roots
of `Pⱼ` in `ℚ̄`: the reciprocal roots of `Pₖ` are `q`-Weil numbers of weight `wₖ`
(`isWeilNumber_of_mem_roots`), and a Weil number has only one weight. -/
theorem weilStratum_prod (hq : 1 < q) (hw : Set.InjOn w s) (h0 : ∀ k ∈ s, (P k).coeff 0 = 1)
    (hpure : ∀ k ∈ s, ∀ y ∈ ((P k).reverse.map (Int.castRingHom ℂ)).roots,
      ‖y‖ = (q : ℝ) ^ ((w k : ℝ) / 2)) {j : ι} (hj : j ∈ s) :
    weilStratum q (w j) (∏ k ∈ s, P k) =
      ((P j).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots := by
  classical
  have hne (k : ι) (hk : k ∈ s) : (P k).reverse ≠ 0 :=
    (monic_reverse_of_coeff_zero_eq_one (h0 k hk)).ne_zero
  have hne' (k : ι) (hk : k ∈ s) :
      (P k).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int).2 (hne k hk)
  -- the reciprocal roots of `Pₖ` are Weil numbers of weight `wₖ`
  have hweil (k : ι) (hk : k ∈ s) (α : AlgebraicClosure ℚ)
      (hα : α ∈ ((P k).reverse.map (algebraMap ℤ (AlgebraicClosure ℚ))).roots) :
      IsWeilNumber q (w k) α :=
    isWeilNumber_of_mem_roots (hne k hk) (hpure k hk) hα
  rw [weilStratum, reverse_prod_of_domain, Polynomial.map_prod,
    roots_prod _ _ (Finset.prod_ne_zero_iff.2 hne'), Multiset.filter_bind]
  change ∑ k ∈ s, _ = _
  rw [Finset.sum_eq_single j (fun k hk hkj ↦ Multiset.filter_eq_nil.2 fun α hα hα' ↦
    hkj (hw hk hj (by exact_mod_cast ((hweil k hk α hα).weight_eq hq hα')))) (fun h ↦ (h hj).elim),
    Multiset.filter_eq_self.2 (hweil j hj)]

/-- **Stratum polynomials of a product.** In the situation of `Polynomial.weilStratum_prod`, the
weight-`wⱼ` stratum polynomial of `∏ₖ Pₖ` is `Pⱼ` itself. -/
theorem weilStratumPoly_prod (hq : 1 < q) (hw : Set.InjOn w s) (h0 : ∀ k ∈ s, (P k).coeff 0 = 1)
    (hpure : ∀ k ∈ s, ∀ y ∈ ((P k).reverse.map (Int.castRingHom ℂ)).roots,
      ‖y‖ = (q : ℝ) ^ ((w k : ℝ) / 2)) {j : ι} (hj : j ∈ s) :
    weilStratumPoly q (w j) (∏ k ∈ s, P k) = (P j).map (algebraMap ℤ (AlgebraicClosure ℚ)) := by
  have h0' : ((P j).map (algebraMap ℤ (AlgebraicClosure ℚ))).coeff 0 = 1 := by
    rw [coeff_map, h0 j hj, map_one]
  rw [weilStratumPoly, weilStratum_prod s P w hq hw h0 hpure hj,
    ← reverse_map (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int]
  exact ((ordinary_reciprocal_roots h0').2.2 (IsAlgClosed.splits _)).2.symm

end Products

end Polynomial
