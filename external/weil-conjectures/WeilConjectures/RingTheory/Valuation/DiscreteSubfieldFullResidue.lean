/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FieldTheory.PBasis
public import WeilConjectures.RingTheory.Valuation.IntegralClosureHenselianDVR
public import WeilConjectures.RingTheory.Valuation.ResiduallyIndependentRadicals

/-!
# A discrete subfield with the full residue field

Let `R` be a henselian discrete valuation ring with separably closed residue field `κ` of
exponential characteristic `p`, and let `Ω` be an algebraically closed field algebraic over `R`,
with the valuation ring `𝒪 = integralClosureValuationSubring R Ω`. We construct a subfield
`K₀ ⊆ Ω` containing the fraction field `K` of `R` such that

* the values of `K₀` are the values of `K` (powers of the value of a uniformizer `ϖ` of `R`),
* every element of `𝒪` is congruent modulo the maximal ideal to an element of `K₀ ∩ 𝒪`.

Construction: lift a `p`-basis `b` of `κ` to units `t i` of `R`, and adjoin to `K` compatible
`p ^ n`-th roots `θ i n` of the `t i` (`θ i (n + 1) ^ p = θ i n`). The finite level fields
`K(θ i n : i ∈ s)` are unramified of degree `p ^ (n * #s)` over `K`
(`ValuationSubring.finrank_adjoin_eq`), so `K₀` is discrete; its residue field contains all
`p ^ n`-th roots of elements of `κ`, hence is the residue field of `𝒪` (the perfect closure of
`κ`).

## Main statements

- `Field.exists_powIndependent_closure`: a `p`-basis in the form used here.
- `IsDiscreteValuationRing.exists_discrete_subfield_full_residue`: the construction.
-/

@[expose] public section

open IsLocalRing IntermediateField

universe u

namespace Field

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every family is `1`-independent. -/
lemma powIndependent_one (b : ι → k) : PowIndependent 1 b := by
  unfold PowIndependent
  intro g hg E
  have h0 (x : Fin 1) : (x : ℕ) = 0 := Nat.lt_one_iff.1 x.2
  have hE (E' : ι → Fin 1) : E' = E := funext fun i => Fin.ext (by rw [h0, h0])
  rw [Finset.sum_eq_single E (fun E' _ hE' => (hE' (hE E')).elim)
    (fun h => (h (Finset.mem_univ E)).elim)] at hg
  simpa [h0] using hg

/-- **`p`-bases.** A field `k` of exponential characteristic `p` has a family `b` of nonzero
elements such that `k` is generated as a ring by `p`-th powers and the `b i`, and every finite
subfamily of `b` is `p`-independent. -/
theorem exists_powIndependent_closure (k : Type u) [Field k] (p : ℕ) [hp : ExpChar k p] :
    ∃ (ι : Type u) (b : ι → k), (∀ i, b i ≠ 0) ∧
      (∀ x, x ∈ Subring.closure (Set.range (· ^ p) ∪ Set.range b)) ∧
      ∀ (s : Finset ι) [DecidableEq s], PowIndependent p fun i : s => b i := by
  classical
  rcases hp with _ | ⟨hprime⟩
  · refine ⟨PEmpty, PEmpty.elim, fun i => i.elim, fun x => ?_, fun s _ => powIndependent_one _⟩
    exact Subring.subset_closure (Set.mem_union_left _ ⟨x, pow_one x⟩)
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨I, t, b, hb⟩ := Field.exists_pBasis k p
  have hcoef (c : (frobenius k p).fieldRange) : ∃ a : k, (c : k) = a ^ p := by
    obtain ⟨a, ha⟩ := c.2
    exact ⟨a, by rw [← ha, frobenius_def]⟩
  refine ⟨I, t, fun i => ?_, fun x => ?_, fun s _ => ?_⟩
  · have hi : ∀ j, (Finsupp.single i 1 : I →₀ ℕ) j < p := fun j => by
      rw [Finsupp.single_apply]
      split_ifs <;> linarith [hprime.two_le]
    have := b.ne_zero ⟨_, hi⟩
    rw [hb] at this
    dsimp only at this
    simpa using this
  · rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Subring.sum_mem _ fun E _ => ?_
    obtain ⟨a, ha⟩ := hcoef (b.repr x E)
    rw [Subfield.smul_def, ha, hb]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩)) ?_
    exact Subring.prod_mem _ fun i _ =>
      Subring.pow_mem _ (Subring.subset_closure (Set.mem_union_right _ (Set.mem_range_self i))) _
  · let ext : (s → Fin p) → {E : I →₀ ℕ // ∀ i, E i < p} := fun E =>
      ⟨Finsupp.onFinset s (fun j => if h : j ∈ s then (E ⟨j, h⟩ : ℕ) else 0) fun j hj => by
        by_contra h
        exact hj (dite_eq_right h), fun j => by
        rw [Finsupp.onFinset_apply]
        split_ifs
        · exact Fin.isLt _
        · exact hprime.pos⟩
    have hext (E : s → Fin p) : b (ext E) = ∏ i : s, t i ^ (E i : ℕ) := by
      rw [hb]
      dsimp only [ext]
      rw [Finsupp.onFinset_prod _ fun _ => pow_zero _, ← Finset.prod_coe_sort s]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [dite_eq_left i.2]
    have hinj : Function.Injective ext := fun E E' h => funext fun i => Fin.ext (by
      have := congrArg (fun E : {E : I →₀ ℕ // ∀ i, E i < p} => E.1 i) h
      simpa [ext] using this)
    have hli := Fintype.linearIndependent_iff.1 (b.linearIndependent.comp ext hinj)
    unfold PowIndependent
    intro g hg E
    have h0 := hli (fun E => ⟨g E ^ p, g E, frobenius_def p (g E)⟩) (by
      simpa [Subfield.smul_def, hext] using hg) E
    simpa [hprime.ne_zero] using congrArg Subtype.val h0

/-- If `k` is generated as a ring by `p`-th powers and the `b i`, then it is generated by
`p ^ n`-th powers and the `b i`. -/
theorem mem_closure_pow_pow_union {k : Type*} [Field k] {p : ℕ} [ExpChar k p] {ι : Type*}
    {b : ι → k} (hb : ∀ x, x ∈ Subring.closure (Set.range (· ^ p) ∪ Set.range b)) (n : ℕ)
    (x : k) : x ∈ Subring.closure (Set.range (· ^ p ^ n) ∪ Set.range b) := by
  induction n generalizing x with
  | zero => exact Subring.subset_closure (Set.mem_union_left _ ⟨x, by simp⟩)
  | succ n ih =>
    refine (Subring.closure_le.2 ?_) (ih x)
    rintro _ (⟨y, rfl⟩ | ⟨i, rfl⟩)
    · have hy : y ^ p ^ n ∈ (Subring.closure (Set.range (· ^ p) ∪ Set.range b)).map
          (iterateFrobenius k p n) := ⟨y, hb y, iterateFrobenius_def p n y⟩
      rw [RingHom.map_closure] at hy
      refine Subring.closure_le.2 ?_ hy
      rintro _ ⟨_, ⟨a, rfl⟩ | ⟨i, rfl⟩, rfl⟩
      · refine Subring.subset_closure (Set.mem_union_left _ ⟨a, ?_⟩)
        dsimp only
        rw [iterateFrobenius_def, ← pow_mul, ← pow_succ']
      · rw [iterateFrobenius_def]
        exact Subring.pow_mem _
          (Subring.subset_closure (Set.mem_union_right _ (Set.mem_range_self i))) _
    · exact Subring.subset_closure (Set.mem_union_right _ ⟨i, rfl⟩)

end Field

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {Ω : Type*} [Field Ω] [Algebra R Ω] [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω]

@[inherit_doc] local notation "𝒪" => integralClosureValuationSubring R Ω

variable (R Ω) in
/-- The inclusion of `R` in `integralClosureValuationSubring R Ω`. -/
noncomputable def toIntegralClosureValuationSubring : R →+* integralClosureValuationSubring R Ω :=
  (algebraMap R Ω).codRestrict _ algebraMap_mem_integralClosureValuationSubring

@[simp]
lemma coe_toIntegralClosureValuationSubring (r : R) :
    (toIntegralClosureValuationSubring R Ω r : Ω) = algebraMap R Ω r :=
  rfl

instance : IsLocalHom (toIntegralClosureValuationSubring R Ω) :=
  ⟨fun _ hr => valuation_algebraMap_eq_one_iff.1
    (((integralClosureValuationSubring R Ω).valuation_eq_one_iff _).1 hr)⟩

/-- The residue field of `integralClosureValuationSubring R Ω` has the exponential characteristic
of the residue field of `R`. -/
lemma expChar_residueField_integralClosureValuationSubring :
    ExpChar (ResidueField (integralClosureValuationSubring R Ω))
      (ringExpChar (ResidueField R)) :=
  expChar_of_injective_ringHom
    (ResidueField.map (toIntegralClosureValuationSubring R Ω)).injective _

/-- Elements of the fraction field `K` of `R` which are integral for `𝒪` lie in `R`. -/
lemma algebraMap_mem_integralClosureValuationSubring_iff {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] [Algebra K Ω] [IsScalarTower R K Ω] (x : K) :
    algebraMap K Ω x ∈ integralClosureValuationSubring R Ω ↔ x ∈ (algebraMap R K).range := by
  refine ⟨fun h => IsIntegrallyClosed.isIntegral_iff.1
    ((isIntegral_algHom_iff (IsScalarTower.toAlgHom R K Ω) (algebraMap K Ω).injective).1 h), ?_⟩
  rintro ⟨r, rfl⟩
  rw [← IsScalarTower.algebraMap_apply]
  exact algebraMap_mem_integralClosureValuationSubring r

/-- Nonzero elements of `R` have values in `v(ϖ) ^ ℕ`. -/
lemma exists_valuation_algebraMap_eq_pow {ϖ : R} (hϖ : Irreducible ϖ) {a : R} (ha : a ≠ 0) :
    ∃ k : ℕ, (integralClosureValuationSubring R Ω).valuation (algebraMap R Ω a) =
      (integralClosureValuationSubring R Ω).valuation (algebraMap R Ω ϖ) ^ k := by
  obtain ⟨k, w, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨k, ?_⟩
  rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow,
    valuation_algebraMap_eq_one_iff.2 w.isUnit, one_mul]

/-- Nonzero elements of the fraction field `K` of `R` have values in `v(ϖ) ^ ℤ`. -/
lemma exists_valuation_algebraMap_eq_zpow {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] [Algebra K Ω] [IsScalarTower R K Ω] {ϖ : R} (hϖ : Irreducible ϖ)
    {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, (integralClosureValuationSubring R Ω).valuation (algebraMap K Ω x) =
      (integralClosureValuationSubring R Ω).valuation (algebraMap R Ω ϖ) ^ m := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨k₁, hk₁⟩ := exists_valuation_algebraMap_eq_pow (Ω := Ω) hϖ ha
  obtain ⟨k₂, hk₂⟩ := exists_valuation_algebraMap_eq_pow (Ω := Ω) hϖ (nonZeroDivisors.ne_zero hb)
  have hϖ0 : (integralClosureValuationSubring R Ω).valuation (algebraMap R Ω ϖ) ≠ 0 := by
    rw [Valuation.ne_zero_iff, map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R Ω)]
    exact hϖ.ne_zero
  refine ⟨(k₁ : ℤ) - k₂, ?_⟩
  rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    hk₁, hk₂, zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast]

/-- **Residue fields.** If the residue field `κ` of `R` is separably closed, then for every
`y ∈ 𝒪` some `p ^ n`-th power of the residue of `y` comes from `κ`. -/
lemma exists_residue_pow_eq [IsSepClosed (ResidueField R)]
    (y : integralClosureValuationSubring R Ω) :
    ∃ n : ℕ, ∃ r : R, residue _ y ^ ringExpChar (ResidueField R) ^ n =
      ResidueField.map (toIntegralClosureValuationSubring R Ω) (residue R r) := by
  set f := toIntegralClosureValuationSubring R Ω
  set ψ := ResidueField.map f
  let := ψ.toAlgebra
  have hcomp : (algebraMap (ResidueField R) (ResidueField 𝒪)).comp (residue R) =
      (residue 𝒪).comp f := RingHom.ext (ResidueField.map_residue f)
  have : Algebra.IsIntegral (ResidueField R) (ResidueField 𝒪) := ⟨fun x => by
    obtain ⟨⟨y, hy⟩, rfl⟩ := residue_surjective x
    obtain ⟨P, hPm, hP⟩ := id hy
    refine ⟨P.map (residue R), hPm.map _, ?_⟩
    have h0 : P.eval₂ f ⟨y, hy⟩ = 0 := Subtype.ext (by
      have := Polynomial.hom_eval₂ P f (ValuationSubring.subtype 𝒪) ⟨y, hy⟩
      exact this.trans hP)
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, h0, map_zero]⟩
  have : Algebra.IsAlgebraic (ResidueField R) (ResidueField 𝒪) :=
    Algebra.IsIntegral.isAlgebraic
  obtain ⟨n, hn⟩ := exists_isSeparable_pow_ringExpChar_pow (K := ResidueField R) (residue 𝒪 y)
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.1 (Polynomial.natDegree_eq_of_degree_eq_some
    (IsSepClosed.degree_eq_one_of_irreducible (ResidueField R)
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral _)) hn))
  obtain ⟨r, rfl⟩ := residue_surjective c
  exact ⟨n, r, hc.symm⟩

section RootSystem

/-! ### Compatible systems of `p ^ n`-th roots of units -/

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Algebra K Ω]
  [IsScalarTower R K Ω] {ι : Type*} {t : ι → Rˣ} {θ : ι → ℕ → Ω}

omit [IsDomain R] [IsDiscreteValuationRing R] [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] in
lemma pow_pow_eq_of_succ (hθ0 : ∀ i, θ i 0 = algebraMap R Ω (t i))
    (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n) (i : ι) (n : ℕ) :
    θ i n ^ ringExpChar (ResidueField R) ^ n = algebraMap R Ω (t i) := by
  induction n with
  | zero => rw [pow_zero, pow_one, hθ0]
  | succ n ih => rw [pow_succ', pow_mul, hθs, ih]

omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R Ω] [FaithfulSMul R Ω]
  [Algebra.IsAlgebraic R Ω] in
lemma pow_pow_sub_eq_of_succ (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n)
    (i : ι) {m n : ℕ} (h : m ≤ n) : θ i n ^ ringExpChar (ResidueField R) ^ (n - m) = θ i m := by
  induction n, h using Nat.le_induction with
  | base => rw [Nat.sub_self, pow_zero, pow_one]
  | succ n hmn ih => rw [Nat.sub_add_comm hmn, pow_succ', pow_mul, hθs, ih]

lemma valuation_root_eq_one (hθ0 : ∀ i, θ i 0 = algebraMap R Ω (t i))
    (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n) (i : ι) (n : ℕ) :
    (𝒪).valuation (θ i n) = 1 := by
  rw [← pow_eq_one_iff_left
      (pow_ne_zero n (expChar_pos (ResidueField R) (ringExpChar (ResidueField R))).ne'),
    ← Valuation.map_pow, pow_pow_eq_of_succ hθ0 hθs, valuation_algebraMap_eq_one_iff]
  exact (t i).isUnit

lemma root_mem (hθ0 : ∀ i, θ i 0 = algebraMap R Ω (t i))
    (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n) (i : ι) (n : ℕ) :
    θ i n ∈ 𝒪 :=
  ((𝒪).valuation_le_one_iff _).1 (valuation_root_eq_one hθ0 hθs i n).le

omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R Ω] [FaithfulSMul R Ω]
  [Algebra.IsAlgebraic R Ω] [Algebra R K] [IsFractionRing R K] [IsScalarTower R K Ω] in
/-- The level fields `K(θ i n : i ∈ s)` increase with `s` and `n`. -/
lemma adjoin_roots_mono (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n)
    {s s' : Finset ι} {n n' : ℕ} (hs : s ⊆ s') (hn : n ≤ n') :
    adjoin K (Set.range fun i : s => θ i n) ≤ adjoin K (Set.range fun i : s' => θ i n') := by
  rw [adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  dsimp only
  rw [← pow_pow_sub_eq_of_succ hθs i hn]
  exact pow_mem (subset_adjoin K (Set.range fun i : s' => θ i n') ⟨⟨i, hs i.2⟩, rfl⟩) _

omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R Ω] [FaithfulSMul R Ω]
  [Algebra.IsAlgebraic R Ω] [Algebra R K] [IsFractionRing R K] [IsScalarTower R K Ω] in
/-- `K(θ i n : i, n)` is the directed union of the level fields `K(θ i n : i ∈ s)`. -/
lemma exists_mem_adjoin_roots (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n)
    {z : Ω} (hz : z ∈ adjoin K (Set.range fun x : ι × ℕ => θ x.1 x.2)) :
    ∃ (s : Finset ι) (n : ℕ), z ∈ adjoin K (Set.range fun i : s => θ i n) := by
  classical
  have hdir : Directed (· ≤ ·)
      fun x : Finset ι × ℕ => adjoin K (Set.range fun i : x.1 => θ i x.2) := fun x y =>
    ⟨(x.1 ∪ y.1, max x.2 y.2),
      adjoin_roots_mono hθs Finset.subset_union_left (le_max_left _ _),
      adjoin_roots_mono hθs Finset.subset_union_right (le_max_right _ _)⟩
  have hle : adjoin K (Set.range fun x : ι × ℕ => θ x.1 x.2) ≤
      ⨆ x : Finset ι × ℕ, adjoin K (Set.range fun i : x.1 => θ i x.2) := by
    rw [adjoin_le_iff]
    rintro _ ⟨⟨i, n⟩, rfl⟩
    exact le_iSup (fun x : Finset ι × ℕ => adjoin K (Set.range fun i : x.1 => θ i x.2)) ({i}, n)
      (subset_adjoin K _ ⟨⟨i, Finset.mem_singleton_self i⟩, rfl⟩)
  have h := hle hz
  rw [← SetLike.mem_coe, coe_iSup_of_directed hdir, Set.mem_iUnion] at h
  obtain ⟨⟨s, n⟩, h⟩ := h
  exact ⟨s, n, h⟩

variable (K) in
/-- The units `t i`, `i ∈ s`, are residually `p ^ n`-independent over `K`. -/
lemma residuallyPowIndependent_units
    (ht : ∀ (s : Finset ι) [DecidableEq s],
      Field.PowIndependent (ringExpChar (ResidueField R)) fun i : s => residue R (t i))
    (s : Finset ι) [DecidableEq s] (n : ℕ) :
    (𝒪).valuation.ResiduallyPowIndependent K (ringExpChar (ResidueField R) ^ n)
      fun i : s => algebraMap R K (t i) :=
  ValuationSubring.residuallyPowIndependent_of_powIndependent
    algebraMap_mem_integralClosureValuationSubring_iff ((ht s).pow n)

omit [IsDomain R] [IsDiscreteValuationRing R] [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω]
  [IsFractionRing R K] in
lemma root_pow_eq_algebraMap (hθ0 : ∀ i, θ i 0 = algebraMap R Ω (t i))
    (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n) (s : Finset ι) (n : ℕ)
    (i : s) : θ i n ^ ringExpChar (ResidueField R) ^ n =
      algebraMap K Ω (algebraMap R K (t i)) := by
  rw [← IsScalarTower.algebraMap_apply]
  exact pow_pow_eq_of_succ hθ0 hθs i n

omit [IsFractionRing R K] in
lemma valuation_algebraMap_unit_eq_one (s : Finset ι) (i : s) :
    (𝒪).valuation (algebraMap K Ω (algebraMap R K (t i))) = 1 := by
  rw [← IsScalarTower.algebraMap_apply, valuation_algebraMap_eq_one_iff]
  exact (t i).isUnit

/-- **The level fields are unramified.** The monomials `∏ i, θ i n ^ E i` (`0 ≤ E i < p ^ n`)
are residually independent over `K`. -/
theorem residuallyIndependent_prod_roots (hθ0 : ∀ i, θ i 0 = algebraMap R Ω (t i))
    (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n)
    (ht : ∀ (s : Finset ι) [DecidableEq s],
      Field.PowIndependent (ringExpChar (ResidueField R)) fun i : s => residue R (t i))
    (s : Finset ι) [DecidableEq s] (n : ℕ) :
    (𝒪).valuation.ResiduallyIndependent K
      fun E : s → Fin (ringExpChar (ResidueField R) ^ n) => ∏ i : s, θ i n ^ (E i : ℕ) :=
  have := expChar_residueField_integralClosureValuationSubring (R := R) (Ω := Ω)
  ValuationSubring.residuallyIndependent_prod_pow _ (root_pow_eq_algebraMap hθ0 hθs s n)
    (valuation_algebraMap_unit_eq_one s) (residuallyPowIndependent_units K ht s n)

/-- **Degree of the level fields.** `[K(θ i n : i ∈ s) : K] = p ^ (n * #s)`. -/
theorem finrank_adjoin_roots (hθ0 : ∀ i, θ i 0 = algebraMap R Ω (t i))
    (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n)
    (ht : ∀ (s : Finset ι) [DecidableEq s],
      Field.PowIndependent (ringExpChar (ResidueField R)) fun i : s => residue R (t i))
    (s : Finset ι) (n : ℕ) :
    Module.finrank K (adjoin K (Set.range fun i : s => θ i n)) =
      ringExpChar (ResidueField R) ^ (n * s.card) := by
  classical
  have := expChar_residueField_integralClosureValuationSubring (R := R) (Ω := Ω)
  rw [ValuationSubring.finrank_adjoin_eq _ (root_pow_eq_algebraMap hθ0 hθs s n)
    (valuation_algebraMap_unit_eq_one s) (residuallyPowIndependent_units K ht s n),
    Fintype.card_coe]

/-- **Discreteness.** The nonzero elements of `K(θ i n : i, n)` have values in `v(ϖ) ^ ℤ`. -/
theorem exists_valuation_eq_zpow_of_mem_adjoin_roots (hθ0 : ∀ i, θ i 0 = algebraMap R Ω (t i))
    (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n)
    (ht : ∀ (s : Finset ι) [DecidableEq s],
      Field.PowIndependent (ringExpChar (ResidueField R)) fun i : s => residue R (t i))
    {ϖ : R} (hϖ : Irreducible ϖ) {z : Ω}
    (hz : z ∈ adjoin K (Set.range fun x : ι × ℕ => θ x.1 x.2)) (hz0 : z ≠ 0) :
    ∃ m : ℤ, (𝒪).valuation z = (𝒪).valuation (algebraMap R Ω ϖ) ^ m := by
  classical
  have := expChar_residueField_integralClosureValuationSubring (R := R) (Ω := Ω)
  obtain ⟨s, n, hzs⟩ := exists_mem_adjoin_roots hθs hz
  obtain ⟨c, hc⟩ := ValuationSubring.exists_valuation_eq_of_mem_adjoin _
    (root_pow_eq_algebraMap hθ0 hθs s n) (valuation_algebraMap_unit_eq_one s)
    (residuallyPowIndependent_units K ht s n) hzs
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero, Valuation.zero_iff] at hc
    exact hz0 hc
  obtain ⟨m, hm⟩ := exists_valuation_algebraMap_eq_zpow (Ω := Ω) hϖ hc0
  exact ⟨m, hc.trans hm⟩

omit [IsFractionRing R K] in
/-- **Full residue field.** If `κ` is separably closed and generated as a ring by `p`-th powers
and the residues of the `t i`, then every element of `𝒪` is congruent modulo the maximal ideal
to an element of `K(θ i n : i, n) ∩ 𝒪`. -/
theorem exists_valuation_sub_lt_one_of_mem [IsSepClosed (ResidueField R)]
    (hθ0 : ∀ i, θ i 0 = algebraMap R Ω (t i))
    (hθs : ∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n)
    (hb : ∀ x, x ∈ Subring.closure (Set.range (· ^ ringExpChar (ResidueField R)) ∪
      Set.range fun i => residue R (t i)))
    {y : Ω} (hy : y ∈ 𝒪) :
    ∃ z ∈ adjoin K (Set.range fun x : ι × ℕ => θ x.1 x.2), z ∈ 𝒪 ∧
      (𝒪).valuation (y - z) < 1 := by
  have := expChar_residueField_integralClosureValuationSubring (R := R) (Ω := Ω)
  set p := ringExpChar (ResidueField R)
  set K₀ := adjoin K (Set.range fun x : ι × ℕ => θ x.1 x.2)
  set f := toIntegralClosureValuationSubring R Ω
  obtain ⟨n, r, hr⟩ := exists_residue_pow_eq (Ω := Ω) ⟨y, hy⟩
  let A : Subring 𝒪 := K₀.toSubfield.toSubring.comap (ValuationSubring.subtype 𝒪)
  let S : Subring (ResidueField 𝒪) := (A.map (residue 𝒪)).map (iterateFrobenius _ p n)
  have hmemK (x : 𝒪) (hx : (x : Ω) ∈ K₀) : residue 𝒪 x ^ p ^ n ∈ S :=
    ⟨residue 𝒪 x, ⟨x, hx, rfl⟩, iterateFrobenius_def p n _⟩
  have hψ (c : ResidueField R) : ResidueField.map f c ∈ S := by
    have h : ResidueField.map f c ∈ (Subring.closure (Set.range (· ^ p ^ n) ∪
        Set.range fun i => residue R (t i))).map (ResidueField.map f) :=
      ⟨c, Field.mem_closure_pow_pow_union hb n c, rfl⟩
    rw [RingHom.map_closure] at h
    refine Subring.closure_le.2 ?_ h
    rintro _ ⟨_, ⟨a, rfl⟩ | ⟨i, rfl⟩, rfl⟩
    · obtain ⟨a, rfl⟩ := residue_surjective a
      dsimp only
      rw [map_pow, ResidueField.map_residue]
      refine hmemK (f a) ?_
      rw [coe_toIntegralClosureValuationSubring, IsScalarTower.algebraMap_apply R K Ω]
      exact IntermediateField.algebraMap_mem K₀ _
    · have hfi : f (t i) = ⟨θ i n, root_mem hθ0 hθs i n⟩ ^ p ^ n :=
        Subtype.ext (by simp [f, p, pow_pow_eq_of_succ hθ0 hθs])
      rw [ResidueField.map_residue, hfi, map_pow]
      exact hmemK _ (subset_adjoin K _ ⟨(i, n), rfl⟩)
  obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := hψ (residue R r)
  have hres : residue 𝒪 x = residue 𝒪 ⟨y, hy⟩ :=
    iterateFrobenius_inj _ p n (by rw [hxy, ← hr, iterateFrobenius_def])
  refine ⟨x, hx, x.2, ?_⟩
  have h := ((𝒪).valuation_lt_one_iff (⟨y, hy⟩ - x)).1 (by
    rw [← residue_eq_zero_iff, map_sub, hres, sub_self])
  simpa using h

end RootSystem

/-- **A discrete subfield with the full residue field.** Let `R` be a henselian discrete valuation
ring with separably closed residue field `κ` of exponential characteristic `p`, uniformizer `ϖ`
and fraction field `K`, and let `Ω` be an algebraically closed field algebraic over `R`, with
`𝒪 = integralClosureValuationSubring R Ω`. There are units `t i` of `R` whose residues generate
`κ` over `κ ^ p` and are `p`-independent, and compatible roots `θ i n` (`θ i 0 = t i`,
`θ i (n + 1) ^ p = θ i n`), such that `K₀ = K(θ i n : i, n)` satisfies:

* `K₀` is the directed union of the level fields `K(θ i n : i ∈ s)`, `s` finite, which are
  unramified of degree `p ^ (n * #s)` over `K` (`finrank_adjoin_roots`,
  `residuallyIndependent_prod_roots`);
* the values of nonzero elements of `K₀` are integral powers of `v(ϖ)`;
* every element of `𝒪` is congruent modulo the maximal ideal to an element of `K₀ ∩ 𝒪`. -/
theorem exists_discrete_subfield_full_residue [IsSepClosed (ResidueField R)] [IsAlgClosed Ω]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Algebra K Ω] [IsScalarTower R K Ω]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ (ι : Type u) (t : ι → Rˣ) (θ : ι → ℕ → Ω),
      (∀ i, θ i 0 = algebraMap R Ω (t i)) ∧
      (∀ i n, θ i (n + 1) ^ ringExpChar (ResidueField R) = θ i n) ∧
      (∀ (s : Finset ι) [DecidableEq s],
        Field.PowIndependent (ringExpChar (ResidueField R)) fun i : s => residue R (t i)) ∧
      (∀ x, x ∈ Subring.closure (Set.range (· ^ ringExpChar (ResidueField R)) ∪
        Set.range fun i => residue R (t i))) ∧
      (∀ z ∈ adjoin K (Set.range fun x : ι × ℕ => θ x.1 x.2),
        ∃ (s : Finset ι) (n : ℕ), z ∈ adjoin K (Set.range fun i : s => θ i n)) ∧
      (∀ z ∈ adjoin K (Set.range fun x : ι × ℕ => θ x.1 x.2), z ≠ 0 →
        ∃ m : ℤ, (𝒪).valuation z = (𝒪).valuation (algebraMap R Ω ϖ) ^ m) ∧
      (∀ y ∈ 𝒪, ∃ z ∈ adjoin K (Set.range fun x : ι × ℕ => θ x.1 x.2), z ∈ 𝒪 ∧
        (𝒪).valuation (y - z) < 1) := by
  set p := ringExpChar (ResidueField R)
  obtain ⟨ι, b, hb0, hbcl, hbind⟩ := Field.exists_powIndependent_closure (ResidueField R) p
  have hlift (i : ι) : ∃ w : Rˣ, residue R w = b i := by
    obtain ⟨r, hr⟩ := residue_surjective (b i)
    exact ⟨((residue_ne_zero_iff_isUnit r).1 (hr ▸ hb0 i)).unit, hr⟩
  choose t ht using hlift
  choose root hroot using fun x : Ω =>
    IsAlgClosed.exists_pow_nat_eq x (expChar_pos (ResidueField R) p)
  let θ : ι → ℕ → Ω := fun i n => Nat.rec (algebraMap R Ω (t i)) (fun _ x => root x) n
  have hθ0 (i : ι) : θ i 0 = algebraMap R Ω (t i) := rfl
  have hθs (i : ι) (n : ℕ) : θ i (n + 1) ^ p = θ i n := hroot _
  have hind (s : Finset ι) [DecidableEq s] : Field.PowIndependent p fun i : s => residue R (t i) :=
    by simpa only [ht] using hbind s
  have hcl (x : ResidueField R) : x ∈ Subring.closure (Set.range (· ^ p) ∪
      Set.range fun i => residue R (t i)) := by
    simpa only [ht] using hbcl x
  exact ⟨ι, t, θ, hθ0, hθs, hind, hcl, fun z hz => exists_mem_adjoin_roots hθs hz,
    fun z hz hz0 => exists_valuation_eq_zpow_of_mem_adjoin_roots hθ0 hθs hind hϖ hz hz0,
    fun y hy => exists_valuation_sub_lt_one_of_mem hθ0 hθs hcl hy⟩

end IsDiscreteValuationRing
