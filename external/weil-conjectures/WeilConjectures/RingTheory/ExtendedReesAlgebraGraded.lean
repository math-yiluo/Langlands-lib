/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.QuasiRegularRees

/-!
# Coefficients of the extended Rees algebra and nilpotence in the associated graded ring

For an ideal `I` of a commutative ring `R`, a Laurent polynomial `x = ∑ xⱼ tʲ` lies in the extended
Rees algebra `R[t, I t⁻¹]` if and only if `xⱼ ∈ I^{-j}` for all `j` (with `I^{m} = R` for `m ≤ 0`),
`Ideal.mem_extendedReesAlgebra_iff`. An element whose coefficients satisfy `xⱼ ∈ I^{1-j}` is a
multiple of `t` (`Ideal.mem_span_extendedReesAlgebraT_of_coeff_mem`).

We use this to show the algebraic core of Varshavsky's lemma on contracting correspondences
(blueprint `lemma-normal-cones-contracting-ideals`): let `φ : R ⟶ S` be a ring map and `J` an ideal
of `S` with `L = I S ⊆ J` and `L^n ⊆ J^{n+1}` for some `n ≥ 1`. Then the induced map of associated
graded rings `gr_I R = R[t, I t⁻¹] / t ⟶ gr_J S` sends the kernel of the augmentation
`gr_I R ⟶ R / I` (the irrelevant ideal `gr_I^{>0} R`) to nilpotent elements: their `n`-th powers
vanish (`Ideal.pow_extendedReesAlgebraMap_mem_span_extendedReesAlgebraT`).
-/

@[expose] public section

open LaurentPolynomial

namespace Ideal

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- A Laurent polynomial is the sum of its monomials. -/
lemma _root_.LaurentPolynomial.eq_sum_C_mul_T (x : R[T;T⁻¹]) :
    x = ∑ n ∈ x.coeff.support, C (x.coeff n) * T n := by
  ext a
  simp_rw [← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
  rw [Finset.sum_apply', Finset.sum_eq_single a, Finsupp.single_eq_same]
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne' hb]
  · intro ha
    rw [Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp ha]

lemma C_mul_T_mem_extendedReesAlgebra {a : R} {j : ℤ} (ha : a ∈ I ^ (-j).toNat) :
    C a * T j ∈ I.extendedReesAlgebra := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · exact Subalgebra.mul_mem _ (C_mem_extendedReesAlgebra a) (T_natCast_mem_extendedReesAlgebra m)
  · simp only [neg_neg, Int.toNat_natCast] at ha
    induction m generalizing a with
    | zero => simpa using C_mem_extendedReesAlgebra (I := I) a
    | succ m ih =>
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha (fun b hb c hc ↦ ?_) fun b c hb hc ↦ ?_
      · have e : C (b * c) * T (-((m + 1 : ℕ) : ℤ)) = (C b * T (-(m : ℤ))) * (C c * T (-1)) := by
          rw [map_mul, mul_mul_mul_comm, ← T_add]
          congr 2
          push_cast
          ring
        rw [e]
        exact Subalgebra.mul_mem _ (ih hb) (C_mul_T_neg_one_mem_extendedReesAlgebra hc)
      · rw [map_add, add_mul]; exact Subalgebra.add_mem _ hb hc

/-- A Laurent polynomial `∑ xⱼ tʲ` lies in the extended Rees algebra `R[t, I t⁻¹]` if and only if
`xⱼ ∈ I^{-j}` for all `j`. -/
lemma mem_extendedReesAlgebra_iff {x : R[T;T⁻¹]} :
    x ∈ I.extendedReesAlgebra ↔ ∀ j, x.coeff j ∈ I ^ (-j).toNat := by
  refine ⟨coeff_mem_pow_of_mem_extendedReesAlgebra, fun hx ↦ ?_⟩
  rw [LaurentPolynomial.eq_sum_C_mul_T x]
  exact Subalgebra.sum_mem _ fun n _ ↦ C_mul_T_mem_extendedReesAlgebra (hx n)

lemma coeff_C_mul_T_zero {a : R} {j : ℤ} :
    (C a * T j : R[T;T⁻¹]).coeff 0 = if j = 0 then a else 0 := by
  rw [mul_comm, coeff_T_mul, C_apply]
  simp only [zero_sub, neg_eq_zero]

/-- The non-positive part `∑_{j ≤ 0} xⱼ tʲ` of a Laurent polynomial. -/
noncomputable def _root_.LaurentPolynomial.nonposPart (x : R[T;T⁻¹]) : R[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff (x.coeff.filter (· ≤ 0))

lemma _root_.LaurentPolynomial.coeff_nonposPart (x : R[T;T⁻¹]) (j : ℤ) :
    x.nonposPart.coeff j = if j ≤ 0 then x.coeff j else 0 := by
  rw [LaurentPolynomial.nonposPart, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply]

/-- An element `∑ xⱼ tʲ` of the extended Rees algebra with `xⱼ ∈ I^{1-j}` for all `j` is a multiple
of `t`. -/
lemma mem_span_extendedReesAlgebraT_of_coeff_mem {x : I.extendedReesAlgebra}
    (hx : ∀ j, (x : R[T;T⁻¹]).coeff j ∈ I ^ (1 - j).toNat) :
    x ∈ span {I.extendedReesAlgebraT} := by
  have hw : T (-1) * (x : R[T;T⁻¹]) ∈ I.extendedReesAlgebra := by
    refine mem_extendedReesAlgebra_iff.mpr fun j ↦ ?_
    rw [coeff_T_mul]
    convert hx (j - -1) using 2
    omega
  refine mem_span_singleton'.mpr ⟨⟨_, hw⟩, Subtype.ext ?_⟩
  simp only [MulMemClass.coe_mul, coe_extendedReesAlgebraT, mul_comm _ (T 1), ← mul_assoc,
    ← T_add]
  simp

/-- The filtration `x ↦ (xⱼ ∈ L^{max(-j, k)})` of `R[t, t⁻¹]` is multiplicative. -/
lemma coeff_mul_mem_pow_max {L : Ideal R} {x y : R[T;T⁻¹]} {a b : ℕ}
    (hx : ∀ j, x.coeff j ∈ L ^ max (-j).toNat a) (hy : ∀ j, y.coeff j ∈ L ^ max (-j).toNat b)
    (j : ℤ) : (x * y).coeff j ∈ L ^ max (-j).toNat (a + b) := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  refine Ideal.sum_mem _ fun p _ ↦ Ideal.sum_mem _ fun q _ ↦ ?_
  split_ifs with h
  · refine Ideal.pow_le_pow_right (n := max (-p).toNat a + max (-q).toNat b) (by omega) ?_
    rw [pow_add]
    exact Ideal.mul_mem_mul (hx p) (hy q)
  · exact zero_mem _

lemma pow_max_le_pow_succ {S : Type*} [CommRing S] {L J : Ideal S} (hLJ : L ≤ J) {n : ℕ}
    (hn : L ^ n ≤ J ^ (n + 1)) (m : ℕ) : L ^ max m n ≤ J ^ (m + 1) := by
  rcases le_total m n with hmn | hnm
  · rw [max_eq_right hmn]
    exact hn.trans (Ideal.pow_le_pow_right (by omega))
  · rw [max_eq_left hnm, show m = n + (m - n) by omega, pow_add,
      show n + (m - n) + 1 = (n + 1) + (m - n) by omega, pow_add]
    exact Ideal.mul_mono hn (Ideal.pow_right_mono hLJ _)

/-- **Nilpotence of the irrelevant ideal.** Let `φ : R ⟶ S` and `J` an ideal of `S` with
`L = I S ⊆ J` and `L^n ⊆ J^{n+1}` for some `n ≥ 1`. If `x ∈ R[t, I t⁻¹]` has constant coefficient
in `I` (i.e. its class in `gr_I R` lies in the irrelevant ideal `⨁_{r > 0} I^r / I^{r+1}`), then
the `n`-th power of its image in `S[t, J t⁻¹]` is a multiple of `t`: the image of the irrelevant
ideal of `gr_I R` in `gr_J S` consists of nilpotent elements. -/
theorem pow_extendedReesAlgebraMap_mem_span_extendedReesAlgebraT {S : Type*} [CommRing S]
    (φ : R →+* S) (J : Ideal S) (h : I.map φ ≤ J) {n : ℕ} (hn : 0 < n)
    (hn' : I.map φ ^ n ≤ J ^ (n + 1)) {x : I.extendedReesAlgebra}
    (hx : (x : R[T;T⁻¹]).coeff 0 ∈ I) :
    I.extendedReesAlgebraMap φ J h x ^ n ∈ span {J.extendedReesAlgebraT} := by
  classical
  set L := I.map φ
  set y : S[T;T⁻¹] := LaurentPolynomial.mapRingHom φ (x : R[T;T⁻¹]) with hy_def
  have hy (j : ℤ) : y.coeff j ∈ L ^ (-j).toNat := by
    rw [hy_def, AddMonoidAlgebra.coeff_mapRingHom, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (coeff_mem_pow_of_mem_extendedReesAlgebra x.2 j)
  have hy0 : y.coeff 0 ∈ L := by
    rw [hy_def, AddMonoidAlgebra.coeff_mapRingHom]
    exact Ideal.mem_map_of_mem _ hx
  -- the part of `y` of non-positive degree
  set y₀ : S[T;T⁻¹] := y.nonposPart
  have hy₀_coeff (j : ℤ) : y₀.coeff j = if j ≤ 0 then y.coeff j else 0 :=
    y.coeff_nonposPart j
  have hy₀ (j : ℤ) : y₀.coeff j ∈ L ^ max (-j).toNat 1 := by
    rw [hy₀_coeff]
    split_ifs with hj
    · rcases hj.lt_or_eq with hj | rfl
      · rw [max_eq_left (by omega)]
        exact hy j
      · simpa using hy0
    · exact zero_mem _
  have hy₀_mem : y₀ ∈ J.extendedReesAlgebra := by
    refine mem_extendedReesAlgebra_iff.mpr fun j ↦ ?_
    exact Ideal.pow_right_mono h _ (Ideal.pow_le_pow_right (le_max_left _ _) (hy₀ j))
  have hpow (m : ℕ) : ∀ j, (y₀ ^ (m + 1)).coeff j ∈ L ^ max (-j).toNat (m + 1) := by
    induction m with
    | zero => simpa using hy₀
    | succ m ih =>
      rw [pow_succ]
      exact coeff_mul_mem_pow_max ih hy₀
  have hdiff : I.extendedReesAlgebraMap φ J h x - ⟨y₀, hy₀_mem⟩ ∈
      span {J.extendedReesAlgebraT} := by
    refine mem_span_extendedReesAlgebraT_of_coeff_mem fun j ↦ ?_
    change (y - y₀).coeff j ∈ _
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hy₀_coeff]
    split_ifs with hj
    · rw [sub_self]
      exact zero_mem _
    · rw [show (1 - j).toNat = 0 by omega, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  have hy₀n : (⟨y₀, hy₀_mem⟩ : J.extendedReesAlgebra) ^ n ∈ span {J.extendedReesAlgebraT} := by
    refine mem_span_extendedReesAlgebraT_of_coeff_mem fun j ↦ ?_
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [SubmonoidClass.coe_pow]
    exact Ideal.pow_le_pow_right (by omega) (pow_max_le_pow_succ h hn' _ (hpow m j))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, Ideal.Quotient.eq.mpr hdiff, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hy₀n

/-- **The irrelevant ideal under extension.** Let `φ : R ⟶ S` and `J = I S`. If an ideal `P` of
`S[t, J t⁻¹]` contains `t` and the images of all `x ∈ R[t, I t⁻¹]` with constant coefficient in
`I`, then it contains every element with constant coefficient in `J`: the irrelevant ideal of
`gr_J S` is generated by the image of the irrelevant ideal of `gr_I R`. -/
theorem mem_of_coeff_zero_mem_of_map_eq {S : Type*} [CommRing S] (φ : R →+* S) (J : Ideal S)
    (h : I.map φ = J) (P : Ideal J.extendedReesAlgebra) (hT : J.extendedReesAlgebraT ∈ P)
    (hP : ∀ x : I.extendedReesAlgebra, (x : R[T;T⁻¹]).coeff 0 ∈ I →
      I.extendedReesAlgebraMap φ J h.le x ∈ P)
    {y : J.extendedReesAlgebra} (hy : (y : S[T;T⁻¹]).coeff 0 ∈ J) : y ∈ P := by
  classical
  -- the monomials `c tʲ` with `c ∈ J^{max(-j, 1)}` lie in `P`
  have hmono (j : ℤ) {c : S} (hc : c ∈ (I ^ max (-j).toNat 1).map φ)
      (hc' : C c * T j ∈ J.extendedReesAlgebra) : (⟨_, hc'⟩ : J.extendedReesAlgebra) ∈ P := by
    have hle : (I ^ max (-j).toNat 1).map φ ≤ J ^ (-j).toNat := by
      rw [Ideal.map_pow, h]
      exact Ideal.pow_le_pow_right (le_max_left _ _)
    refine Submodule.span_induction (p := fun c hc ↦
      (⟨C c * T j, C_mul_T_mem_extendedReesAlgebra (hle hc)⟩ : J.extendedReesAlgebra) ∈ P)
      ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨a, ha, rfl⟩
      have ha' : C a * T j ∈ I.extendedReesAlgebra :=
        C_mul_T_mem_extendedReesAlgebra (Ideal.pow_le_pow_right (le_max_left _ _) ha)
      convert hP ⟨_, ha'⟩ ?_ using 1
      · exact Subtype.ext (by simp)
      · rw [coeff_C_mul_T_zero]
        split_ifs
        · exact Ideal.pow_le_self (by omega) ha
        · exact zero_mem _
    · convert P.zero_mem using 1
      exact Subtype.ext (by simp)
    · intro c d _ _ hc hd
      convert P.add_mem hc hd using 1
      exact Subtype.ext (by simp [add_mul])
    · intro b c _ hc
      convert P.mul_mem_left (algebraMap S J.extendedReesAlgebra b) hc using 1
      exact Subtype.ext (by simp [mul_assoc])
  set y₀ : S[T;T⁻¹] := (y : S[T;T⁻¹]).nonposPart
  have hy₀ (j : ℤ) : y₀.coeff j ∈ (I ^ max (-j).toNat 1).map φ := by
    rw [Ideal.map_pow, h, LaurentPolynomial.coeff_nonposPart]
    split_ifs with hj
    · rcases hj.lt_or_eq with hj | rfl
      · rw [max_eq_left (by omega)]
        exact coeff_mem_pow_of_mem_extendedReesAlgebra y.2 j
      · simpa using hy
    · exact zero_mem _
  have hy₀_mem (j : ℤ) : C (y₀.coeff j) * T j ∈ J.extendedReesAlgebra := by
    refine C_mul_T_mem_extendedReesAlgebra ?_
    have := hy₀ j
    rw [Ideal.map_pow, h] at this
    exact Ideal.pow_le_pow_right (le_max_left _ _) this
  obtain ⟨z, hzP, hz⟩ : y₀ ∈ P.toAddSubgroup.map
      (J.extendedReesAlgebra.val.toRingHom.toAddMonoidHom) := by
    rw [LaurentPolynomial.eq_sum_C_mul_T y₀]
    exact AddSubgroup.sum_mem _ fun j _ ↦ ⟨_, hmono j (hy₀ j) (hy₀_mem j), rfl⟩
  have hdiff : y - z ∈ span {J.extendedReesAlgebraT} := by
    refine mem_span_extendedReesAlgebraT_of_coeff_mem fun j ↦ ?_
    change ((y : S[T;T⁻¹]) - (z : S[T;T⁻¹])).coeff j ∈ _
    rw [show (z : S[T;T⁻¹]) = y₀ from hz, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      LaurentPolynomial.coeff_nonposPart]
    split_ifs with hj
    · rw [sub_self]
      exact zero_mem _
    · rw [show (1 - j).toNat = 0 by omega, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  have := P.add_mem ((Ideal.span_singleton_le_iff_mem P).mpr hT hdiff) hzP
  rwa [sub_add_cancel] at this

/-- The extended Rees algebra of a finitely generated ideal `I = (s)` is generated by `t` and the
elements `x t⁻¹` with `x ∈ s`. -/
lemma extendedReesAlgebra_eq_adjoin {s : Set R} (hs : span s = I) :
    I.extendedReesAlgebra =
      Algebra.adjoin R (insert (T 1) ((fun x ↦ LaurentPolynomial.C x * T (-1)) '' s)) := by
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_mono ?_)
  · rintro _ (rfl | ⟨x, hx, rfl⟩)
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · rw [← hs] at hx
      refine Submodule.span_induction (p := fun x _ ↦ LaurentPolynomial.C x * T (-1) ∈
        Algebra.adjoin R (insert (T 1) ((fun x ↦ LaurentPolynomial.C x * T (-1)) '' s)))
        (fun y hy ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩)) ?_ ?_ ?_ hx
      · simp
      · intro x y _ _ hx hy
        rw [map_add, add_mul]
        exact Subalgebra.add_mem _ hx hy
      · intro r x _ hx
        rw [smul_eq_mul, map_mul, mul_assoc, LaurentPolynomial.C_eq_algebraMap]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) hx
  · refine Set.insert_subset_insert (Set.image_mono ?_)
    rw [← hs]
    exact subset_span

/-- The extended Rees algebra of a finitely generated ideal is of finite type. -/
theorem finiteType_extendedReesAlgebra (hI : I.FG) :
    Algebra.FiniteType R I.extendedReesAlgebra := by
  obtain ⟨s, hs⟩ := hI
  refine ⟨I.extendedReesAlgebra.fg_top.mpr (Subalgebra.fg_def.mpr ⟨_, ?_,
    (extendedReesAlgebra_eq_adjoin hs).symm⟩)⟩
  exact ((s.finite_toSet.image _).insert _)

/-- The constant term of the image of `x ∈ R[t, I t⁻¹]` in `S[t]` is the image of the coefficient
of `t⁰` of `x`. -/
lemma eval_zero_extendedReesAlgebraToPolynomial {S : Type*} [CommRing S] (φ : R →+* S)
    (h : I ≤ RingHom.ker φ) (x : I.extendedReesAlgebra) :
    (I.extendedReesAlgebraToPolynomial φ h x).eval 0 = φ ((x : R[T;T⁻¹]).coeff 0) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← coeff_toLaurent_natCast,
    toLaurent_extendedReesAlgebraToPolynomial, AddMonoidAlgebra.coeff_mapRingHom, Nat.cast_zero]

end Ideal
