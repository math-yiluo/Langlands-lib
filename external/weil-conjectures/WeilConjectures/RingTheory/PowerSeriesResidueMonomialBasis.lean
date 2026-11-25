/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.Subfield.Basic

import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Lifting a finite coefficient basis through exponent residues

Source: Stacks Project, Tag 07P5, first proof paragraph, with the explicit basis
construction in lem-weil-pbc-power-series-subring-finite-basis, step 2.
(blueprint: lem-weil-pbc-power-series-residue-monomial-basis).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingTheory

private theorem series_prod (k : Type u) [Field k] (n : ℕ) (e : Fin n → ℕ) :
    (∏ i, MvPowerSeries.X i ^ e i : MvPowerSeries (Fin n) k) =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm e) 1 := by
  simp_rw [MvPowerSeries.X_pow_eq]
  rw [MvPowerSeries.prod_monomial]
  have hs : ∑ i, Finsupp.single i (e i) = Finsupp.equivFunOnFinite.symm e := by
    apply Finsupp.ext
    intro i
    simp [Finsupp.single_apply]
  rw [hs]
  simp
private theorem polynomial_prod (R : Type u) [CommRing R] (n : ℕ) (e : Fin n → ℕ) :
    (∏ i, MvPolynomial.X i ^ e i : MvPolynomial (Fin n) R) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) 1 := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul]
  rw [Finsupp.prod_fintype]
  · rfl
  · intro i
    exact pow_zero _
private theorem residue_eq (p a e e' : ℕ) (ha : p ∣ a) (he : e < p) (he' : e' < p)
    (hle : e' ≤ a + e) (hd : p ∣ a + e - e') : e' = e := by
  have h := congrArg (fun x : ℕ ↦ x % p) (Nat.sub_add_cancel hle)
  simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd ha, Nat.mod_eq_zero_of_dvd hd,
    Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt he'] using h
private theorem monomial_coeff (p : ℕ) (k : Type u) [Field k] (n m : ℕ)
    (c : MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))
    (hc : ∀ a g, MvPowerSeries.coeff a (AddMonoidAlgebra.coeff c g) ≠ 0 →
      (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j))
    (a e e' : Fin n →₀ ℕ) (g h h' : Fin m →₀ ℕ) (z : k)
    (ha : ∀ i, p ∣ a i) (hg : ∀ j, p ∣ g j)
    (he : ∀ i, e i < p) (he' : ∀ i, e' i < p)
    (hh : ∀ j, h j < p) (hh' : ∀ j, h' j < p) :
    MvPowerSeries.coeff (a + e) (AddMonoidAlgebra.coeff
      (c * MvPolynomial.monomial h' (MvPowerSeries.monomial e' z)) (g + h)) =
    if e' = e ∧ h' = h then MvPowerSeries.coeff a (AddMonoidAlgebra.coeff c g) * z
      else 0 := by
  classical
  by_cases heq : e' = e ∧ h' = h
  · rcases heq with ⟨rfl, rfl⟩
    simp [MvPowerSeries.coeff_add_mul_monomial]
  · rw [ite_eq_right heq, MvPolynomial.coeff_mul_monomial']
    by_cases hgl : h' ≤ g + h
    · rw [ite_eq_left hgl, MvPowerSeries.coeff_mul_monomial]
      by_cases hel : e' ≤ a + e
      · rw [ite_eq_left hel]
        by_contra hn
        have hn' := left_ne_zero_of_mul hn
        obtain ⟨had, hgd⟩ := hc _ _ hn'
        apply heq
        constructor
        · apply Finsupp.ext
          intro i
          exact residue_eq p (a i) (e i) (e' i) (ha i) (he i) (he' i) (hel i) (had i)
        · apply Finsupp.ext
          intro j
          exact residue_eq p (g j) (h j) (h' j) (hg j) (hh j) (hh' j) (hgl j) (hgd j)
      · simp [hel]
    · simp [hgl]
private theorem residue_injective (n p : ℕ) : Function.Injective
    (fun e : Fin n → Fin p ↦ Finsupp.equivFunOnFinite.symm (fun i ↦ (e i : ℕ))) := by
  intro e f h
  funext i
  apply Fin.ext
  exact congrArg (fun a : Fin n →₀ ℕ ↦ a i) h
private theorem vector_eq (p : ℕ) (k : Type u) [Field k] (Q : Type v)
    (b : Q → k) (n m : ℕ) (q : Q × (Fin n → Fin p) × (Fin m → Fin p)) :
    MvPolynomial.C (MvPowerSeries.C (b q.1) *
      ∏ i : Fin n, MvPowerSeries.X i ^ (q.2.1 i : ℕ)) *
      ∏ j : Fin m, MvPolynomial.X j ^ (q.2.2 j : ℕ) =
    MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (fun j ↦ (q.2.2 j : ℕ)))
      (MvPowerSeries.monomial
        (Finsupp.equivFunOnFinite.symm (fun i ↦ (q.2.1 i : ℕ))) (b q.1)) := by
  rw [series_prod, polynomial_prod, MvPolynomial.C_mul_monomial, mul_one]
  have hs : MvPowerSeries.C (b q.1) * MvPowerSeries.monomial
      (Finsupp.equivFunOnFinite.symm (fun i ↦ (q.2.1 i : ℕ))) 1 =
      MvPowerSeries.monomial
        (Finsupp.equivFunOnFinite.symm (fun i ↦ (q.2.1 i : ℕ))) (b q.1) := by
    change MvPowerSeries.monomial 0 (b q.1) * _ = _
    rw [MvPowerSeries.monomial_mul_monomial, zero_add, mul_one]
  rw [hs]
private theorem exponent_split (p : ℕ) (hp : 0 < p) (n : ℕ) (a : Fin n →₀ ℕ) :
    ∃ (d : Fin n →₀ ℕ) (e : Fin n → Fin p),
      (∀ i, p ∣ d i) ∧ a = d + Finsupp.equivFunOnFinite.symm (fun i ↦ (e i : ℕ)) := by
  let d := a.mapRange (fun x ↦ p * (x / p)) (by simp)
  let e : Fin n → Fin p := fun i ↦ ⟨a i % p, Nat.mod_lt _ hp⟩
  refine ⟨d, e, ?_, ?_⟩
  · intro i
    exact dvd_mul_right _ _
  · apply Finsupp.ext
    intro i
    exact (Nat.div_add_mod (a i) p).symm

private theorem series_monomial_coeff (p : ℕ) (k : Type u) [Field k] (n : ℕ)
    (c : MvPowerSeries (Fin n) k)
    (hc : ∀ a, MvPowerSeries.coeff a c ≠ 0 → ∀ i, p ∣ a i)
    (a e e' : Fin n →₀ ℕ) (z : k)
    (ha : ∀ i, p ∣ a i) (he : ∀ i, e i < p) (he' : ∀ i, e' i < p) :
    MvPowerSeries.coeff (a + e) (c * MvPowerSeries.monomial e' z) =
      if e' = e then MvPowerSeries.coeff a c * z else 0 := by
  classical
  by_cases heq : e' = e
  · subst e'
    simp [MvPowerSeries.coeff_add_mul_monomial]
  · rw [ite_eq_right heq, MvPowerSeries.coeff_mul_monomial]
    by_cases hel : e' ≤ a + e
    · rw [ite_eq_left hel]
      by_contra hn
      have hd := hc _ (left_ne_zero_of_mul hn)
      apply heq
      apply Finsupp.ext
      intro i
      exact residue_eq p (a i) (e i) (e' i) (ha i) (he i) (he' i) (hel i) (hd i)
    · simp [hel]

private theorem series_decomposition (p : ℕ) (hp : 0 < p) (k : Type u) [Field k]
    (K : Subfield k) (Q : Type v) [Fintype Q] (b : Module.Basis Q K k) (n : ℕ)
    (φ : MvPowerSeries (Fin n) k) :
    ∃ D : Q × (Fin n → Fin p) → MvPowerSeries (Fin n) k,
      (∀ r a, MvPowerSeries.coeff a (D r) ∈ K ∧
        (MvPowerSeries.coeff a (D r) ≠ 0 → ∀ i, p ∣ a i)) ∧
      φ = ∑ r, D r * (MvPowerSeries.C (b r.1) *
        ∏ i : Fin n, MvPowerSeries.X i ^ (r.2 i : ℕ)) := by
  classical
  let E := fun e : Fin n → Fin p ↦
    Finsupp.equivFunOnFinite.symm (fun i ↦ (e i : ℕ))
  let D : Q × (Fin n → Fin p) → MvPowerSeries (Fin n) k := fun r a ↦
    if ∀ i, p ∣ a i then ((b.repr (MvPowerSeries.coeff (a + E r.2) φ)) r.1 : k)
      else 0
  have hD (r : Q × (Fin n → Fin p)) (a : Fin n →₀ ℕ) :
      MvPowerSeries.coeff a (D r) ∈ K ∧
        (MvPowerSeries.coeff a (D r) ≠ 0 → ∀ i, p ∣ a i) := by
    change (if ∀ i, p ∣ a i then _ else (0 : k)) ∈ K ∧ _
    by_cases h : ∀ i, p ∣ a i
    · simp only [ite_eq_left h]
      exact ⟨Subtype.mem _, fun _ ↦ h⟩
    · simp [MvPowerSeries.coeff_apply, D, h]
  refine ⟨D, hD, ?_⟩
  apply MvPowerSeries.ext
  intro a
  obtain ⟨d, e, hd, he⟩ := exponent_split p hp n a
  rw [he]
  have hf (r : Q × (Fin n → Fin p)) :
      MvPowerSeries.coeff (d + E e) (D r *
        (MvPowerSeries.C (b r.1) * ∏ i : Fin n, MvPowerSeries.X i ^ (r.2 i : ℕ))) =
      if r.2 = e then
        (((b.repr (MvPowerSeries.coeff (d + E e) φ)) r.1 : K) : k) * b r.1 else 0 := by
    rw [series_prod]
    have hs : MvPowerSeries.C (b r.1) * MvPowerSeries.monomial (E r.2) 1 =
        MvPowerSeries.monomial (E r.2) (b r.1) := by
      change MvPowerSeries.monomial 0 (b r.1) * _ = _
      rw [MvPowerSeries.monomial_mul_monomial, zero_add, mul_one]
    rw [hs]
    have hm := series_monomial_coeff p k n (D r) (fun a hn ↦ (hD r a).2 hn)
      d (E e) (E r.2) (b r.1) hd (fun i ↦ (e i).isLt) (fun i ↦ (r.2 i).isLt)
    have hei : E r.2 = E e ↔ r.2 = e := (residue_injective n p).eq_iff
    simp only [hei] at hm
    rw [hm]
    split_ifs with h
    · subst e
      simp [MvPowerSeries.coeff_apply, D, hd]
    · rfl
  change MvPowerSeries.coeff (d + E e) φ = MvPowerSeries.coeff (d + E e) _
  rw [map_sum]
  simp_rw [hf]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact (b.sum_repr (MvPowerSeries.coeff (d + E e) φ)).symm

private theorem powerSeriesResidueMonomialSpan
    (p : ℕ) (hp : 0 < p)
    (k : Type u) [Field k] (K : Subfield k)
    (Q : Type v) [Finite Q] (b : Module.Basis Q K k)
    (n m : ℕ)
    (S : Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hS : ∀ f, f ∈ S ↔
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ∈ K ∧
        (MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j))) :
    ⊤ ≤ Submodule.span S (Set.range (fun q : Q × (Fin n → Fin p) × (Fin m → Fin p) ↦
      MvPolynomial.C (MvPowerSeries.C (b q.1) *
        ∏ i : Fin n, MvPowerSeries.X i ^ (q.2.1 i : ℕ)) *
      ∏ j : Fin m, MvPolynomial.X j ^ (q.2.2 j : ℕ))) := by
  classical
  let := Fintype.ofFinite Q
  let v : Q × (Fin n → Fin p) × (Fin m → Fin p) →
      MvPolynomial (Fin m) (MvPowerSeries (Fin n) k) :=
    fun q ↦ MvPolynomial.C (MvPowerSeries.C (b q.1) *
      ∏ i : Fin n, MvPowerSeries.X i ^ (q.2.1 i : ℕ)) *
      ∏ j : Fin m, MvPolynomial.X j ^ (q.2.2 j : ℕ)
  have hmon (g : Fin m →₀ ℕ) (φ : MvPowerSeries (Fin n) k) :
      MvPolynomial.monomial g φ ∈ Submodule.span S (Set.range v) := by
    obtain ⟨d, h, hd, hg⟩ := exponent_split p hp m g
    obtain ⟨D, hD, hφ⟩ := series_decomposition p hp k K Q b n φ
    rw [hφ, map_sum]
    apply Submodule.sum_mem
    intro r _
    let c : MvPolynomial (Fin m) (MvPowerSeries (Fin n) k) :=
      MvPolynomial.monomial d (D r)
    have hc : c ∈ S := by
      apply (hS c).mpr
      intro a g'
      by_cases heq : g' = d
      · subst g'
        simp only [c, MvPolynomial.coeff_monomial]
        exact ⟨(hD r a).1, fun hn ↦ ⟨(hD r a).2 hn, hd⟩⟩
      · simp [c, MvPolynomial.coeff_monomial, Ne.symm heq]
    let cs : S := ⟨c, hc⟩
    have heq : MvPolynomial.monomial g
        (D r * (MvPowerSeries.C (b r.1) *
          ∏ i : Fin n, MvPowerSeries.X i ^ (r.2 i : ℕ))) =
        cs • v (r.1, r.2, h) := by
      change _ = c * v (r.1, r.2, h)
      dsimp [c, v]
      rw [vector_eq p k Q b n m (r.1, r.2, h), MvPolynomial.monomial_mul_monomial]
      rw [series_prod]
      have hs : MvPowerSeries.C (b r.1) * MvPowerSeries.monomial
          (Finsupp.equivFunOnFinite.symm (fun i ↦ (r.2 i : ℕ))) 1 =
          MvPowerSeries.monomial
            (Finsupp.equivFunOnFinite.symm (fun i ↦ (r.2 i : ℕ))) (b r.1) := by
        change MvPowerSeries.monomial 0 (b r.1) * _ = _
        rw [MvPowerSeries.monomial_mul_monomial, zero_add, mul_one]
      rw [hs, hg]
    rw [heq]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(r.1, r.2, h), rfl⟩
  intro f _
  rw [f.as_sum]
  apply Submodule.sum_mem
  intro g _
  exact hmon g (AddMonoidAlgebra.coeff f g)



private theorem powerSeriesResidueCoefficientRecovery
    (p : ℕ)
    (k : Type u) [Field k] (K : Subfield k)
    (Q : Type v) [Finite Q] (b : Module.Basis Q K k)
    (n m : ℕ)
    (S : Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hS : ∀ f, f ∈ S →
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ∈ K ∧
        (MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j))) :
    ∀ (l : (Q × (Fin n → Fin p) × (Fin m → Fin p)) →₀ S)
      (q : Q × (Fin n → Fin p) × (Fin m → Fin p))
      (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
      (∀ i, p ∣ a i) → (∀ j, p ∣ g j) →
      (((b.repr (MvPowerSeries.coeff
        (a + Finsupp.equivFunOnFinite.symm (fun i ↦ (q.2.1 i : ℕ)))
        (AddMonoidAlgebra.coeff
          (Finsupp.linearCombination S (fun q : Q × (Fin n → Fin p) × (Fin m → Fin p) ↦
      MvPolynomial.C (MvPowerSeries.C (b q.1) *
        ∏ i : Fin n, MvPowerSeries.X i ^ (q.2.1 i : ℕ)) *
      ∏ j : Fin m, MvPolynomial.X j ^ (q.2.2 j : ℕ)) l)
          (g + Finsupp.equivFunOnFinite.symm (fun j ↦ (q.2.2 j : ℕ)))))) q.1 : K) : k) =
      MvPowerSeries.coeff a (AddMonoidAlgebra.coeff (l q :
        MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) g) := by
  classical
  let := Fintype.ofFinite Q
  intro l q a g ha hg
  let v : Q × (Fin n → Fin p) × (Fin m → Fin p) →
      MvPolynomial (Fin m) (MvPowerSeries (Fin n) k) :=
    fun r ↦ MvPolynomial.C (MvPowerSeries.C (b r.1) *
      ∏ i : Fin n, MvPowerSeries.X i ^ (r.2.1 i : ℕ)) *
      ∏ j : Fin m, MvPolynomial.X j ^ (r.2.2 j : ℕ)
  let E := fun e : Fin n → Fin p ↦
    Finsupp.equivFunOnFinite.symm (fun i ↦ (e i : ℕ))
  let H := fun h : Fin m → Fin p ↦
    Finsupp.equivFunOnFinite.symm (fun j ↦ (h j : ℕ))
  let c := fun r : Q × (Fin n → Fin p) × (Fin m → Fin p) ↦
    MvPowerSeries.coeff a (AddMonoidAlgebra.coeff (l r :
      MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) g)
  have hf (r : Q × (Fin n → Fin p) × (Fin m → Fin p)) :
      MvPowerSeries.coeff (a + E q.2.1) (AddMonoidAlgebra.coeff
        ((l r : MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) * v r) (g + H q.2.2)) =
      if r.2 = q.2 then c r * b r.1 else 0 := by
    dsimp [v]
    rw [vector_eq]
    have hm := monomial_coeff p k n m (l r)
      (fun a g hn ↦ (hS _ (l r).property a g).2 hn)
      a (E q.2.1) (E r.2.1) g (H q.2.2) (H r.2.2) (b r.1) ha hg
      (fun i ↦ (q.2.1 i).isLt) (fun i ↦ (r.2.1 i).isLt)
      (fun j ↦ (q.2.2 j).isLt) (fun j ↦ (r.2.2 j).isLt)
    have hi : (E r.2.1 = E q.2.1 ∧ H r.2.2 = H q.2.2) ↔ r.2 = q.2 := by
      rw [(residue_injective n p).eq_iff, (residue_injective m p).eq_iff]
      exact Prod.ext_iff.symm
    simpa only [hi] using hm
  have hc (r : Q × (Fin n → Fin p) × (Fin m → Fin p)) : c r ∈ K :=
    (hS _ (l r).property a g).1
  have hr (r : Q × (Fin n → Fin p) × (Fin m → Fin p)) :
      (b.repr (c r * b r.1)) q.1 = if r.1 = q.1 then ⟨c r, hc r⟩ else 0 := by
    change (b.repr ((⟨c r, hc r⟩ : K) • b r.1)) q.1 = _
    rw [map_smul, b.repr_self]
    simp [Finsupp.single_apply]
  change (((b.repr (MvPowerSeries.coeff (a + E q.2.1)
    (AddMonoidAlgebra.coeff (Finsupp.linearCombination S v l) (g + H q.2.2)))) q.1 : K) : k) = c q
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_fintype l (fun i s ↦ s • v i) (fun i ↦ zero_smul S (v i))]
  simp only [Subring.smul_def, smul_eq_mul, MvPolynomial.coeff_sum, map_sum]
  simp_rw [hf]
  simp only [apply_ite, map_zero, Finsupp.finsetSum_apply]
  simp only [apply_ite (fun f : Q →₀ K ↦ f q.1), Finsupp.zero_apply]
  simp_rw [hr]
  have hi (r : Q × (Fin n → Fin p) × (Fin m → Fin p)) :
      (if r.2 = q.2 then (if r.1 = q.1 then (⟨c r, hc r⟩ : K) else 0) else 0) =
      if r = q then (⟨c r, hc r⟩ : K) else 0 := by
    by_cases h : r = q
    · simp [h]
    · have hh : ¬ (r.1 = q.1 ∧ r.2 = q.2) := fun hh ↦ h (Prod.ext hh.1 hh.2)
      simp only [ite_eq_right h]
      split_ifs <;> simp_all
  simp_rw [hi]
  simp




/-- A finite coefficient-field basis lifts to the explicit residue-monomial basis.
Source: Stacks Project, Tag 07P5, finiteness paragraph, expanded by the explicit
coefficient-grouping argument in the parent node, step 2.
(blueprint: lem-weil-pbc-power-series-residue-monomial-basis).

Proof: For each polynomial exponent g and series exponent a write a = p*A + e
and g = p*G + h coordinatewise, with all entries of e and h less than p. Expand
each coefficient uniquely in b. For a fixed triple (q,e,h), put the q-coordinate
of the coefficient at (p*A+e,p*G+h) into a new column at (p*A,p*G), and put zero
at the other exponents. Each column lies in S by hS. There are only finitely many
triples, since the coefficient basis and both residue sets are finite. Moreover,
only finitely many polynomial exponents G occur: they are coordinatewise quotients
of the finitely many polynomial exponents of the original polynomial. Thus each
column really is a polynomial with power-series coefficients. Summing the columns
times the indicated monomials recovers every coefficient, proving spanning.
For uniqueness, take a relation among these monomials with coefficients in S.
At exponent (p*A+e,p*G+h), support divisibility means only the terms with residues
(e,h) contribute. Their coefficient is the sum of b(q) times the corresponding
K coordinates of the columns. Independence of b makes every such coordinate
zero. Varying A,G,e,h and using the support condition proves that all columns
are zero. This gives the claimed basis, with exactly the displayed values.
The proof uses only positivity of p, not characteristic p. For p=1 the residue
sets are singletons; zero variables give empty products and the same argument. -/
theorem powerSeriesResidueMonomialBasis
    (p : ℕ) (hp : 0 < p)
    (k : Type u) [Field k] (K : Subfield k)
    (Q : Type v) [Finite Q] (b : Module.Basis Q K k)
    (n m : ℕ)
    (S : Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hS : ∀ f, f ∈ S ↔
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ∈ K ∧
        (MvPowerSeries.coeff a (AddMonoidAlgebra.coeff f g) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j))) :
    ∃ B : Module.Basis (Q × (Fin n → Fin p) × (Fin m → Fin p)) S
      (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)),
      ∀ q, B q =
        MvPolynomial.C (MvPowerSeries.C (b q.1) *
          ∏ i : Fin n, MvPowerSeries.X i ^ (q.2.1 i : ℕ)) *
        ∏ j : Fin m, MvPolynomial.X j ^ (q.2.2 j : ℕ) := by
  classical
  let v : Q × (Fin n → Fin p) × (Fin m → Fin p) →
      MvPolynomial (Fin m) (MvPowerSeries (Fin n) k) :=
    fun q : Q × (Fin n → Fin p) × (Fin m → Fin p) ↦
      MvPolynomial.C (MvPowerSeries.C (b q.1) *
        ∏ i : Fin n, MvPowerSeries.X i ^ (q.2.1 i : ℕ)) *
      ∏ j : Fin m, MvPolynomial.X j ^ (q.2.2 j : ℕ)
  have hli : LinearIndependent S v := by
    rw [linearIndependent_iff]
    intro l hl
    apply Finsupp.ext
    intro q
    apply Subtype.ext
    apply MvPolynomial.ext
    intro g
    apply MvPowerSeries.ext
    intro a
    change MvPowerSeries.coeff a (AddMonoidAlgebra.coeff (l q :
      MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) g) = 0
    by_cases hc : MvPowerSeries.coeff a (AddMonoidAlgebra.coeff (l q :
      MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) g) = 0
    · exact hc
    · obtain ⟨ha, hg⟩ := ((hS _).mp (l q).property a g).2 hc
      have hr := powerSeriesResidueCoefficientRecovery p k K Q b n m S
        (fun f hf ↦ (hS f).mp hf) l q a g ha hg
      change Finsupp.linearCombination S v l = 0 at hl
      change (((b.repr (MvPowerSeries.coeff _ (AddMonoidAlgebra.coeff
        (Finsupp.linearCombination S v l) _))) q.1 : K) : k) = _ at hr
      rw [hl] at hr
      simpa using hr.symm
  have hsp : ⊤ ≤ Submodule.span S (Set.range v) :=
    powerSeriesResidueMonomialSpan p hp k K Q b n m S hS
  refine ⟨Module.Basis.mk hli hsp, ?_⟩
  intro q
  exact Module.Basis.mk_apply hli hsp q


end RingTheory
