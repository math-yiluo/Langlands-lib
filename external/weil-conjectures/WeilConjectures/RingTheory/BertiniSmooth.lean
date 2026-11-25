/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.BertiniSmoothAux

/-!
# Generic members of a separating linear system avoid `m²`

This is the smoothness half of the Bertini argument (blueprint
`lemma-curve-preserving-finite-cover--1`): for a smooth domain `A` of finite type over an
algebraically closed field `k` and a linear system `v` which separates tangent vectors away from
a finite set `S` of maximal ideals (and generates the cotangent spaces at the points of `S`), a
generic member `∑ bᵢ vᵢ` of the system lies outside `m²` at every maximal ideal `m` containing it.
-/

@[expose] public section

universe u

namespace Algebra

section Incidence

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

open MvPolynomial in
theorem exists_ne_zero_map_mem_of_isPrime [IsDomain A] [FormallySmooth k A] {M : ℕ}
    (v : Fin M → A) (S : Set (Ideal A)) (hS : S.Finite)
    (hgen : ∀ m : Ideal A, m.IsMaximal → m ∉ S → ∀ x : A,
      ∃ c : Fin M → k, x - ∑ i, c i • v i ∈ m ^ 2)
    (hvS : ∀ m ∈ S, ∀ i, v i ∈ m)
    (hcot : ∀ m ∈ S, ∀ x ∈ m, ∃ c : Fin M → k, x - ∑ i, c i • v i ∈ m ^ 2) (hS0 : ⊥ ∉ S)
    (P : Ideal (MvPolynomial (Fin M) A)) [P.IsPrime]
    (hP : ∀ j, ∑ i, X i * C (derivationJet k v j i) ∈ P) :
    ∃ h : MvPolynomial (Fin M) k, h ≠ 0 ∧ map (algebraMap k A) h ∈ P := by
  classical
  by_contra! hcon
  let ξ : Fin M → MvPolynomial (Fin M) A ⧸ P := fun i ↦ Ideal.Quotient.mk P (X i)
  have haeval (h : MvPolynomial (Fin M) k) :
      aeval ξ h = Ideal.Quotient.mk P (map (algebraMap k A) h) := by
    have : aeval ξ = (Ideal.Quotient.mkₐ k P).comp (mapAlgHom (Algebra.ofId k A)) :=
      algHom_ext fun i ↦ by simp [ξ]
    rw [this]
    rfl
  have hind : AlgebraicIndependent k ξ := by
    rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
    intro h hh
    by_contra hne
    exact hcon h hne (Ideal.Quotient.eq_zero_iff_mem.mp (haeval h ▸ hh))
  have hker : RingHom.ker (IsScalarTower.toAlgHom k A (MvPolynomial (Fin M) A ⧸ P)) =
      P.comap C := by
    ext a
    simp only [RingHom.mem_ker, Ideal.mem_comap]
    rw [IsScalarTower.coe_toAlgHom', ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.algebraMap_eq]
  obtain ⟨n, _, _, I, J, hdet, htr⟩ :=
    exists_det_derivationJet_notMem_of_isPrime v S hS hgen hvS hcot hS0 (P.comap C)
  have hgen' : Algebra.adjoin A (Set.range ξ) = ⊤ := by
    have : Set.range ξ = Ideal.Quotient.mkₐ A P '' Set.range X := by
      rw [← Set.range_comp]
      rfl
    rw [this, ← AlgHom.map_adjoin, adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective A P
  have hW (a : n) :
      ∑ i, algebraMap A _ (derivationJet k v (J a) i) * ξ i = 0 := by
    have := hP (J a)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, map_mul, mul_comm]
  have hdet' : algebraMap A (MvPolynomial (Fin M) A ⧸ P)
      (Matrix.of fun a b ↦ derivationJet k v (J a) (I b)).det ≠ 0 := by
    intro h0
    exact hdet (by rw [← hker]; exact h0)
  have hb := trdeg_add_card_le (k := k) ξ hgen' _ hW I hdet'
  rw [← (Ideal.quotientKerEquivRange
      (IsScalarTower.toAlgHom k A (MvPolynomial (Fin M) A ⧸ P))).trdeg_eq,
    (Ideal.quotientEquivAlgOfEq k hker).trdeg_eq] at hb
  have hM := hind.lift_cardinalMk_le_trdeg
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp (htr.trans (Cardinal.natCast_lt_aleph0))
  rw [ht] at hb htr
  rw [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero] at hM
  have := (add_le_add hM le_rfl).trans hb
  norm_cast at this htr
  omega

end Incidence

end Algebra

open MvPolynomial in
/-- (S) Generic members of a separating linear system avoid `m²`: if the linear system `v` on
the smooth domain `A` separates tangent vectors at every maximal ideal outside the finite set `S`
of nonzero ideals, vanishes on `S` and generates the cotangent spaces at the points of `S`, then
for `b` outside a hypersurface `h = 0`, the member `∑ bᵢ vᵢ` lies outside `m²` at every maximal
ideal `m` containing it. Part of the Bertini argument, blueprint
`lemma-curve-preserving-finite-cover--1`. -/
theorem Algebra.Smooth.exists_ne_zero_forall_notMem_sq {k A : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Algebra.Smooth k A]
    {M : ℕ} (v : Fin M → A) (S : Set (Ideal A)) (hS : S.Finite)
    (hgen : ∀ m : Ideal A, m.IsMaximal → m ∉ S → ∀ x : A,
      ∃ c : Fin M → k, x - ∑ i, c i • v i ∈ m ^ 2)
    (hvS : ∀ m ∈ S, ∀ i, v i ∈ m)
    (hcot : ∀ m ∈ S, ∀ x ∈ m, ∃ c : Fin M → k, x - ∑ i, c i • v i ∈ m ^ 2) (hS0 : ⊥ ∉ S) :
    ∃ h : MvPolynomial (Fin M) k, h ≠ 0 ∧ ∀ b : Fin M → k, MvPolynomial.eval b h ≠ 0 →
      ∀ m : Ideal A, m.IsMaximal → ∑ i, b i • v i ∈ m → ∑ i, b i • v i ∉ m ^ 2 := by
  classical
  let F : Option (Derivation k A A) → MvPolynomial (Fin M) A :=
    fun j ↦ ∑ i, X i * C (derivationJet k v j i)
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hfin := (Ideal.span (Set.range F)).finite_minimalPrimes_of_isNoetherianRing
  have hP (P : Ideal (MvPolynomial (Fin M) A)) (hP : P ∈ (Ideal.span (Set.range F)).minimalPrimes) :
      ∃ h : MvPolynomial (Fin M) k, h ≠ 0 ∧ map (algebraMap k A) h ∈ P := by
    have : P.IsPrime := hP.1.1
    exact exists_ne_zero_map_mem_of_isPrime v S hS hgen hvS hcot hS0 P
      fun j ↦ hP.1.2 (Ideal.subset_span ⟨j, rfl⟩)
  choose! hP' hP'0 hP'mem using hP
  refine ⟨∏ P ∈ hfin.toFinset, hP' P,
    Finset.prod_ne_zero_iff.mpr fun P hP ↦ hP'0 P (hfin.mem_toFinset.mp hP),
    fun b hb m hm hbm hbm2 ↦ ?_⟩
  let φ : MvPolynomial (Fin M) A →+* A ⧸ m :=
    eval₂Hom (Ideal.Quotient.mk m) fun i ↦ algebraMap k (A ⧸ m) (b i)
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : Ideal.span (Set.range F) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have : φ (F j) = Ideal.Quotient.mk m (∑ i, b i • derivationJet k v j i) := by
      simp [φ, F, map_sum, Algebra.smul_def, mul_comm]
    rw [this, Ideal.Quotient.eq_zero_iff_mem]
    cases j with
    | none => simpa using hbm
    | some D => simpa [map_sum, D.map_smul] using D.apply_mem_of_mem_sq hbm2
  obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le hle
  have h1 := hPle (hP'mem P hPmin)
  rw [RingHom.mem_ker] at h1
  have h2 : φ (map (algebraMap k A) (hP' P)) = algebraMap k (A ⧸ m) (eval b (hP' P)) := by
    rw [MvPolynomial.coe_eval₂Hom, eval₂_map, MvPolynomial.eval, coe_eval₂Hom,
      eval₂_comp_left]
    congr 1
  rw [h2, map_eq_zero_iff _ (algebraMap k (A ⧸ m)).injective] at h1
  exact hb (by rw [map_prod]; exact Finset.prod_eq_zero (hfin.mem_toFinset.mpr hPmin) h1)
