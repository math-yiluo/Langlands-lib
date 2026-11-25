/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.SemilocalDimOneConductor
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Algebra.Order.Archimedean.Basic
import WeilConjectures.RingTheory.SemilocalDedekindDvrReduction
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# A common denominator lies in Jacobson radicals

Source: Stacks Project, Varieties, Lemma 33.37.8 (Tag 09N5)
(blueprint: lem-sc-jacobson-denominator-function-field).
-/

@[expose] public section

universe u v w t

namespace RingTheory

private theorem tensor_surjective_overring
    {A : Type u} {B : Type t} {C : Type w} {K : Type v}
    [CommRing A] [CommRing B] [CommRing C] [CommRing K]
    [Algebra A K] [Algebra B K] [Algebra C K] [Algebra B C]
    [IsScalarTower B C K]
    (h : Function.Surjective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ B K))) :
    Function.Surjective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ C K)) := by
  let g := Algebra.TensorProduct.map (AlgHom.id ℤ A) (IsScalarTower.toAlgHom ℤ B C)
  have hg : (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ C K)).comp g =
      Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ B K) := by
    apply Algebra.TensorProduct.ext
    · ext x
      simp [g, Algebra.TensorProduct.includeLeft]
    · ext x
      simp [g, Algebra.TensorProduct.includeRight,
        ← IsScalarTower.algebraMap_apply B C K]
  intro k
  obtain ⟨z, hz⟩ := h k
  refine ⟨g z, ?_⟩
  exact (DFunLike.congr_fun hg z).trans hz

private theorem jacobson_descends_integral
    {B : Type u} {C : Type v} [CommRing B] [CommRing C]
    [Algebra B C] [Algebra.IsIntegral B C]
    (hinj : Function.Injective (algebraMap B C)) (b : B)
    (hb : algebraMap B C b ∈ Ideal.jacobson (⊥ : Ideal C)) :
    b ∈ Ideal.jacobson (⊥ : Ideal B) := by
  rw [Ideal.jacobson, Submodule.mem_sInf]
  rintro m ⟨_, hm⟩
  have := hm
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C) m
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  rw [← hqm]
  exact (show Ideal.jacobson (⊥ : Ideal C) ≤ q from
    sInf_le ⟨bot_le, hq⟩) hb

private theorem exists_large_power (a b : WithZero (Multiplicative ℤ)) (ha : 1 < a) :
    ∃ n : ℕ, b < a ^ n := by
  by_cases hb : b = 0
  · refine ⟨1, ?_⟩
    simpa [hb] using zero_lt_one.trans ha
  · obtain ⟨n, hn⟩ := MulArchimedean.arch (b * a) ha
    exact ⟨n, (lt_mul_of_one_lt_right (pos_iff_ne_zero.mpr hb) ha).trans_le hn⟩

private theorem simultaneous_large_valuations
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] {ι : Type w} (v : ι → Valuation K (WithZero (Multiplicative ℤ)))
    (hbase : ∀ i, ∃ x : A, x ≠ 0 ∧ 1 < v i (algebraMap A K x))
    (s : Finset ι) :
    ∃ x : A, x ≠ 0 ∧ ∀ i ∈ s, 1 < v i (algebraMap A K x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨x, hx, hxs⟩ := ih
    by_cases hxi : 1 < v i (algebraMap A K x)
    · exact ⟨x, hx, fun j hj ↦ (Finset.mem_insert.mp hj).elim
        (fun h ↦ h ▸ hxi) (hxs j)⟩
    obtain ⟨y, _, hyi⟩ := hbase i
    have hexp : ∀ j, ∃ n : ℕ, j ∈ s →
        max 1 (v j (algebraMap A K y)) < v j (algebraMap A K x) ^ n := by
      intro j
      by_cases hj : j ∈ s
      · obtain ⟨n, hn⟩ := exists_large_power _
          (max 1 (v j (algebraMap A K y))) (hxs j hj)
        exact ⟨n, fun _ ↦ hn⟩
      · exact ⟨0, fun h ↦ (hj h).elim⟩
    choose n hn using hexp
    let N := (∑ j ∈ s, n j) + 1
    have hlarge : ∀ j ∈ s,
        max 1 (v j (algebraMap A K y)) < v j (algebraMap A K (x ^ N)) := by
      intro j hj
      rw [map_pow, map_pow]
      apply (hn j hj).trans_le
      apply pow_le_pow_right₀ (hxs j hj).le
      exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hj).trans
        (Nat.le_add_right _ _)
    have hnew : 1 < v i (algebraMap A K (x ^ N + y)) := by
      rw [map_add, (v i).map_add_eq_of_lt_right]
      · exact hyi
      · rw [map_pow, map_pow]
        exact (pow_le_one₀ zero_le (le_of_not_gt hxi)).trans_lt hyi
    refine ⟨x ^ N + y, ?_, ?_⟩
    · intro h
      simp [h] at hnew
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hnew
      · rw [map_add, (v j).map_add_eq_of_lt_left]
        · exact (le_max_left _ _).trans_lt (hlarge j hj)
        · exact (le_max_right _ _).trans_lt (hlarge j hj)

private theorem exists_large_valuation_of_tensor_surjective
    {A : Type u} {D : Type t} {K : Type v}
    [CommRing A] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Field K] [Algebra A K] [Algebra D K] [IsFractionRing D K]
    (h : Function.Surjective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ D K))) :
    ∃ x : A, x ≠ 0 ∧
      1 < (IsDiscreteValuationRing.maximalIdeal D).valuation K (algebraMap A K x) := by
  let v := (IsDiscreteValuationRing.maximalIdeal D).valuation K
  have hex : ∃ x : A, 1 < v (algebraMap A K x) := by
    by_contra! hn
    let p := Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ D K)
    have hp : ∀ z : TensorProduct ℤ A D, v (p z) ≤ 1 := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a d =>
        simp only [p, Algebra.TensorProduct.productMap_apply_tmul,
          IsScalarTower.toAlgHom_apply, Valuation.map_mul]
        simpa using mul_le_mul (hn a)
          ((IsDiscreteValuationRing.maximalIdeal D).valuation_le_one (K := K) d)
          zero_le zero_le
      | add z z' hz hz' =>
        rw [map_add]
        exact (v.map_add _ _).trans (max_le hz hz')
    obtain ⟨k, hk⟩ :=
      (IsDiscreteValuationRing.maximalIdeal D).valuation_surjective K (WithZero.exp (1 : ℤ))
    obtain ⟨z, hz⟩ := h k
    have hbad := hp z
    change v (Algebra.TensorProduct.productMap _ _ z) ≤ 1 at hbad
    rw [hz, hk] at hbad
    exact (show ¬ (WithZero.exp (1 : ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 by decide) hbad
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, ?_, hx⟩
  intro hzero
  simp [hzero] at hx

private theorem exists_inv_mem_maximalIdeal_of_tensor_surjective
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    {ι : Type w} [Finite ι]
    (D : ι → Type t) [∀ i, CommRing (D i)] [∀ i, IsDomain (D i)]
    [∀ i, IsDiscreteValuationRing (D i)]
    [∀ i, Algebra (D i) K] [∀ i, IsFractionRing (D i) K]
    (hsurj : ∀ i, Function.Surjective
      (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ (D i) K))) :
    ∃ f : A, f ≠ 0 ∧ ∀ i, ∃ d : D i,
      d ∈ IsLocalRing.maximalIdeal (D i) ∧
        algebraMap (D i) K d = (algebraMap A K f)⁻¹ := by
  classical
  let v := fun i ↦ (IsDiscreteValuationRing.maximalIdeal (D i)).valuation K
  have hbase : ∀ i, ∃ x : A, x ≠ 0 ∧ 1 < v i (algebraMap A K x) :=
    fun i ↦ exists_large_valuation_of_tensor_surjective (hsurj i)
  let := Fintype.ofFinite ι
  obtain ⟨f, hf, hfv⟩ := simultaneous_large_valuations v hbase Finset.univ
  refine ⟨f, hf, fun i ↦ ?_⟩
  have hval : v i ((algebraMap A K f)⁻¹) < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ (hfv i (Finset.mem_univ i))
  obtain ⟨d, hd⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hval.le
  refine ⟨d, ?_, hd⟩
  apply ((IsDiscreteValuationRing.maximalIdeal (D i)).valuation_lt_one_iff_mem (K := K) d).mp
  simpa only [hd] using hval


/-- Source: Stacks Project, Varieties, Lemma 33.37.8 (Tag 09N5).
For a domain `A` with fraction field `K` and a finite family of Noetherian one-dimensional
semilocal domains `B i` in `K` with fraction field `K`, if each canonical multiplication map
`A ⊗[ℤ] B i → K` is surjective, then a nonzero element of `A` has inverse in the Jacobson
radical of every `B i`.

Proof (Stacks Tag 09N5):
1. Replace each `B i` by its integral closure `B' i` in `K`. The tensor map remains
   surjective since its image contains the old image. By
   `lem-sc-semilocal-dim-one-conductor`, each `B' i` is semilocal Dedekind. If a nonzero
   `x : A` has inverse in their radicals, that conductor lemma with `y = 1` gives positive
   exponents `n i` with `x ^ (-n i)` in `B i`. Replace `x` by the power whose exponent is
   the product of these finitely many exponents. Its inverse then belongs to every `B i`
   and remains in every radical of `B' i`. For a maximal ideal `m` of `B i`, integral
   lying-over (`lem-weil-pbc-integral-injective-lying-over`) gives a prime above `m` in
   `B' i`. A maximal ideal containing that prime contracts to `m`, so the inverse lies
   in `m`. This descends radical membership to `B i`.
2. By `lem-sc-semilocal-dedekind-dvr-reduction`, replace every semilocal Dedekind ring
   by its finitely many localizations at maximal ideals. These are DVRs with fraction
   field `K`, their tensor maps remain surjective, and membership in all their maximal
   ideals is equivalent to membership in the original Jacobson radical.
3. For one DVR, `lem-sc-dvr-tensor-surjective-negative-valuation` gives a nonzero element
   of `A` with negative valuation: otherwise `A` lies in the DVR and the tensor map
   cannot surject onto `K`. Induct on the finite family of valuations. Choose nonzero
   `x` negative at all but the last valuation. If it is negative there too, finish.
   Otherwise choose nonzero `y` negative at the last valuation by the base case.
   Using `lem-sc-dvr-valuation-arithmetic`, replace `x` by a sufficiently large positive
   power so its valuations at all earlier places are smaller than those of `y`.
   The unequal-value sum rule makes `x + y` negative at every place and nonzero.
   Its inverse has positive valuation, hence lies in every maximal ideal. For the empty
   family take `1 : A`.
(blueprint: lem-sc-jacobson-denominator-function-field) -/
theorem exists_inv_mem_jacobson_of_tensor_surjective
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    {ι : Type w} [Finite ι]
    (B : ι → Type t) [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    [∀ i, IsNoetherianRing (B i)] [∀ i, Finite (MaximalSpectrum (B i))]
    (hdim : ∀ i, ringKrullDim (B i) = 1)
    [∀ i, Algebra (B i) K] [∀ i, IsFractionRing (B i) K]
    (hsurj : ∀ i, Function.Surjective
      (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ (B i) K))) :
    ∃ f : A, f ≠ 0 ∧ ∀ i, ∃ b : B i,
      b ∈ (Ideal.jacobson (⊥ : Ideal (B i)) : Set (B i)) ∧
        algebraMap (B i) K b = (algebraMap A K f)⁻¹ := by
  classical
  let C := fun i ↦ integralClosure (B i) K
  have hc := fun i ↦ semilocal_dim_one_conductor (B i) (hdim i) K
  have : ∀ i, Finite (MaximalSpectrum (C i)) := fun i ↦ (hc i).1
  have : ∀ i, IsDedekindDomain (C i) := fun i ↦ (hc i).2.1
  have : ∀ i, IsFractionRing (C i) K := fun i ↦ (hc i).2.2.2.1
  have hCdim : ∀ i, ringKrullDim (C i) = 1 := fun i ↦ (hc i).2.2.1
  let J := Σ i, MaximalSpectrum (C i)
  let D := fun j : J ↦ Localization.AtPrime j.2.asIdeal
  let a := fun j : J ↦
    IsLocalization.localizationAlgebraOfSubmonoidLe (D j) K
      j.2.asIdeal.primeCompl (nonZeroDivisors (C j.1))
      j.2.asIdeal.primeCompl_le_nonZeroDivisors
  let : ∀ j : J, CommRing (D j) := fun j ↦ inferInstance
  have : ∀ j : J, IsDomain (D j) := fun j ↦ inferInstance
  let : ∀ j : J, Algebra ℤ (D j) := fun j ↦ Ring.toIntAlgebra (D j)
  let : ∀ j : J, Algebra (D j) K := a
  let : ∀ j : J, Module (D j) K := fun j ↦ (a j).toModule
  have : ∀ j : J, IsScalarTower ℤ (D j) K := fun j ↦
    AddCommGroup.intIsScalarTower
  have hdvr := fun i ↦
    MaximalSpectrum.semilocal_dedekind_dvr_reduction (C i) (hCdim i) K
  have : ∀ j : J, IsDiscreteValuationRing (D j) := fun j ↦ (hdvr j.1).2.1 j.2 |>.1
  have : ∀ j : J, IsFractionRing (D j) K := fun j ↦ (hdvr j.1).2.1 j.2 |>.2
  have hsC : ∀ i, Function.Surjective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ (C i) K)) :=
    fun i ↦ tensor_surjective_overring (C := C i) (hsurj i)
  have hsD : ∀ j : J, Function.Surjective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ℤ A K) (IsScalarTower.toAlgHom ℤ (D j) K)) := by
    intro j
    let : Algebra (D j) K := a j
    have : IsScalarTower (C j.1) (D j) K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (D j) K
        j.2.asIdeal.primeCompl (nonZeroDivisors (C j.1))
        j.2.asIdeal.primeCompl_le_nonZeroDivisors
    exact tensor_surjective_overring (A := A) (B := C j.1) (C := D j)
      (K := K) (hsC j.1)
  obtain ⟨f, hf, hflocal⟩ := exists_inv_mem_maximalIdeal_of_tensor_surjective D hsD
  have hfn : algebraMap A K f ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hf
  have hglobal : ∀ i, ∃ c : C i, c ∈ Ideal.jacobson (⊥ : Ideal (C i)) ∧
      algebraMap (C i) K c = (algebraMap A K f)⁻¹ := by
    intro i
    exact ((hdvr i).2.2 _).mpr (fun m ↦ hflocal ⟨i, m⟩)
  choose c hcjac hceq using hglobal
  have hcpower : ∀ i, ∃ n : ℕ, 0 < n ∧ ∃ b : B i,
      algebraMap (B i) K b = (algebraMap A K f)⁻¹ ^ n := by
    intro i
    have hcne : c i ≠ 0 := by
      intro hz
      have := hceq i
      rw [hz, map_zero] at this
      exact (inv_ne_zero hfn) this.symm
    obtain ⟨n, hn, b, hb⟩ := (hc i).2.2.2.2 (c i) 1 hcne (hcjac i)
    refine ⟨n, hn, b, ?_⟩
    simpa [C, ← hceq i] using hb
  choose n hn b hb using hcpower
  let := Fintype.ofFinite ι
  let N := ∏ i, n i
  have hN : 0 < N := Finset.prod_pos (fun i _ ↦ hn i)
  refine ⟨f ^ N, pow_ne_zero _ hf, fun i ↦ ?_⟩
  have hdiv : n i ∣ N := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨b i ^ k, ?_, ?_⟩
  · have hinj : Function.Injective (algebraMap (B i) (C i)) := by
      intro x y h
      apply IsFractionRing.injective (B i) K
      simpa only [← IsScalarTower.algebraMap_apply (B i) (C i) K] using
        congrArg (algebraMap (C i) K) h
    apply jacobson_descends_integral hinj (b i ^ k)
    have heq : algebraMap (B i) (C i) (b i ^ k) = c i ^ N := by
      apply IsFractionRing.injective (C i) K
      rw [← IsScalarTower.algebraMap_apply (B i) (C i) K,
        map_pow, map_pow, hb i, hceq i, ← pow_mul, ← hk]
    rw [heq]
    exact Ideal.pow_mem_of_mem _ (hcjac i) N hN
  · rw [map_pow, hb i, ← pow_mul, ← hk, map_pow, inv_pow]

end RingTheory
