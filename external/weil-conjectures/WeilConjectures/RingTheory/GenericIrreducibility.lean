/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.Flat.Equalizer
public import WeilConjectures.RingTheory.BertiniNoether
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Generic irreducibility of fibres

Let `A` be a noetherian domain with fraction field `K` and `C` a finite type `A`-algebra whose
generic fibre is geometrically irreducible. Then the fibres of `Spec C → Spec A` over a dense
open subset of `Spec A` are irreducible (Stacks `0559`, ring-theoretic form).

## Main statements

- `exists_ne_zero_forall_isIrreducible_fiber`: generic irreducibility of fibres.

## References

- Stacks Project, Tag `0559`, <https://stacks.math.columbia.edu/tag/0559>
-/

@[expose] public section

open TensorProduct MvPolynomial

namespace GenericIrreducibility

/-- Irreducibility of the spectrum descends along ring maps that are surjective on spectra. -/
lemma irreducibleSpace_of_comap_surjective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective (PrimeSpectrum.comap f)) [IrreducibleSpace (PrimeSpectrum S)] :
    IrreducibleSpace (PrimeSpectrum R) := by
  have := (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum S)).image _
    (PrimeSpectrum.continuous_comap f).continuousOn
  rw [Set.image_univ, hf.range_eq] at this
  exact (irreducibleSpace_def _).mpr this

/-- If `g` is a nonzerodivisor of `R` and `Spec R_g` is irreducible, so is `Spec R`. -/
lemma irreducibleSpace_of_isLocalization_away {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (g : R) [IsLocalization.Away g S] (hg : g ∈ nonZeroDivisors R)
    [IrreducibleSpace (PrimeSpectrum S)] : IrreducibleSpace (PrimeSpectrum R) := by
  have hd : DenseRange (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro x hx
    rw [RingHom.mem_ker, ← map_zero (algebraMap R S)] at hx
    rw [IsLocalization.injective S (M := Submonoid.powers g) (Submonoid.powers_le.mpr hg) hx]
    exact zero_mem _
  have := (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum S)).image _
    (PrimeSpectrum.continuous_comap (algebraMap R S)).continuousOn
  rw [Set.image_univ] at this
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hd.closure_range]
  exact this.closure

/-- If `g` is a nonzerodivisor of `C` and `C ⧸ g` is flat over `A` after inverting `a`, then
`1 ⊗ g` is a nonzerodivisor of `M ⊗[A] C` for every `A`-algebra `M` in which `a` is a unit. -/
lemma one_tmul_mem_nonZeroDivisors {A C M : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [CommRing M] [Algebra A M] {g : C} (hg : g ∈ nonZeroDivisors C) {a : A}
    (ha : IsUnit (algebraMap A M a))
    (hflat : Module.Flat A (LocalizedModule (Submonoid.powers a) (C ⧸ Ideal.span {g}))) :
    (1 ⊗ₜ g : M ⊗[A] C) ∈ nonZeroDivisors (M ⊗[A] C) := by
  set S := Submonoid.powers a
  let μ : C →ₗ[A] C := LinearMap.mulLeft A g
  let π : C →ₗ[A] C ⧸ Ideal.span {g} := (Ideal.Quotient.mkₐ A (Ideal.span {g})).toLinearMap
  let ℓ := LocalizedModule.mkLinearMap S C
  let ℓ' := LocalizedModule.mkLinearMap S (C ⧸ Ideal.span {g})
  have hμ : Function.Injective μ := fun x y h ↦ (mul_cancel_left_mem_nonZeroDivisors hg).mp h
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective A _
  have hex : Function.Exact μ π := by
    intro x
    simp only [π, μ, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton', Set.mem_range,
      LinearMap.mulLeft_apply, mul_comm g]
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat
    (IsLocalizedModule.map S ℓ ℓ' π) (IsLocalizedModule.map_surjective S ℓ ℓ' π hπ)
    (IsLocalizedModule.map S ℓ ℓ μ) (IsLocalizedModule.map_injective S ℓ ℓ μ hμ)
    (IsLocalizedModule.map_exact S ℓ ℓ ℓ' μ π hex) M
  have hℓ' : Function.Injective (ℓ.rTensor M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := S)
      (f := AlgebraTensorModule.rTensor A M ℓ) (x₁ := x) (x₂ := 0) (by rw [map_zero]; exact hx)
    rw [smul_zero, Submonoid.smul_def, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply',
      map_pow] at hn
    exact ((ha.pow n).map
      (Algebra.TensorProduct.includeRight (R := A) (A := C))).mul_right_eq_zero.mp hn
  have hℓ : Function.Injective (ℓ.lTensor M) := by
    rw [← LinearMap.comm_comp_rTensor_comp_comm_eq]
    exact (TensorProduct.comm A _ M).injective.comp (hℓ'.comp (TensorProduct.comm A M C).injective)
  have hmul (y : M ⊗[A] C) : μ.lTensor M y = (1 ⊗ₜ g) * y := by
    induction y using TensorProduct.inductionOn with
    | tmul m c => simp [μ]
    | add x y hx hy => simp [mul_add, hx, hy]
  rw [mem_nonZeroDivisors_iff_left]
  intro x hx
  apply hℓ
  apply hinj
  rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    IsLocalizedModule.map_comp, LinearMap.lTensor_comp, LinearMap.comp_apply, hmul, hx, map_zero]

/-- Let `J` be an ideal of `A[X]` containing `P` with `a J ⊆ (P)`. If `a` is invertible in the
field `k` and `P` stays irreducible over `k`, then `k ⊗[A] (A[X] ⧸ J)` is a domain. -/
lemma isDomain_tensor_quotient {A k σ : Type*} [CommRing A] [Field k] [Algebra A k]
    (P : MvPolynomial σ A) (J : Ideal (MvPolynomial σ A)) (hPJ : P ∈ J) (a : A)
    (ha : algebraMap A k a ≠ 0) (hJ : ∀ Q ∈ J, P ∣ C a * Q)
    (hP : Irreducible (map (algebraMap A k) P)) :
    IsDomain (k ⊗[A] (MvPolynomial σ A ⧸ J)) := by
  set φ : MvPolynomial σ A →+* MvPolynomial σ k := map (algebraMap A k)
  set ψ := (algebraTensorAlgEquiv A k (σ := σ)).toRingEquiv
  have hJφ : Ideal.span {φ P} =
      (J.map (Algebra.TensorProduct.includeRight (R := A) (A := k))).map (ψ : _ →+* _) := by
    have h1 : J.map (Algebra.TensorProduct.includeRight (R := A) (A := k)) =
        J.map (Algebra.TensorProduct.includeRight (R := A) (A := k)).toRingHom := rfl
    have h2 : (ψ : _ →+* _).comp
        (Algebra.TensorProduct.includeRight (R := A) (A := k)).toRingHom = φ := by
      ext <;> simp [φ, ψ]
    rw [h1, Ideal.map_map, h2]
    symm
    refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hPJ))
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQ
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    obtain ⟨R, hR⟩ := hJ Q hQ
    have hu : IsUnit (φ (C a)) := by
      simpa [φ] using (isUnit_iff_ne_zero.mpr ha).map (C : k →+* MvPolynomial σ k)
    refine (hu.dvd_mul_left).mp ⟨φ R, ?_⟩
    rw [← map_mul, hR, map_mul]
  have hprime : (Ideal.span {φ P}).IsPrime :=
    (Ideal.span_singleton_prime hP.ne_zero).mpr hP.prime
  let e := (Algebra.TensorProduct.tensorQuotientEquiv (R := A) k (MvPolynomial σ A) k
    J).toRingEquiv.trans (Ideal.quotientEquiv _ _ ψ hJφ)
  exact Function.Injective.isDomain e.toRingHom e.injective

/-- The subalgebra `R[1/x]` of a field `F`, for `x ∈ R`. -/
def locSub {A F : Type*} [CommRing A] [Field F] [Algebra A F] (R : Subalgebra A F) {x : F}
    (hx : x ∈ R) : Subalgebra A F where
  carrier := {z | ∃ r ∈ R, ∃ m : ℕ, z * x ^ m = r}
  mul_mem' := by
    rintro z₁ z₂ ⟨r₁, hr₁, m₁, h₁⟩ ⟨r₂, hr₂, m₂, h₂⟩
    exact ⟨r₁ * r₂, mul_mem hr₁ hr₂, m₁ + m₂, by rw [← h₁, ← h₂]; ring⟩
  add_mem' := by
    rintro z₁ z₂ ⟨r₁, hr₁, m₁, h₁⟩ ⟨r₂, hr₂, m₂, h₂⟩
    refine ⟨r₁ * x ^ m₂ + r₂ * x ^ m₁, add_mem (mul_mem hr₁ (pow_mem hx _))
      (mul_mem hr₂ (pow_mem hx _)), m₁ + m₂, by rw [← h₁, ← h₂]; ring⟩
  algebraMap_mem' a := ⟨algebraMap A F a, R.algebraMap_mem a, 0, by simp⟩

section locSub

variable {A F : Type*} [CommRing A] [Field F] [Algebra A F] {R : Subalgebra A F} {x : F}
  (hx : x ∈ R)

lemma mem_locSub {z : F} : z ∈ locSub R hx ↔ ∃ r ∈ R, ∃ m : ℕ, z * x ^ m = r := Iff.rfl


lemma locSub_congr {y : F} (hxy : x = y) (hy : y ∈ R) : locSub R hx = locSub R hy := by
  subst hxy
  rfl

lemma le_locSub : R ≤ locSub R hx := fun z hz ↦ ⟨z, hz, 0, by simp⟩

lemma inv_mem_locSub (hx0 : x ≠ 0) : x⁻¹ ∈ locSub R hx :=
  ⟨1, R.one_mem, 1, by rw [pow_one, inv_mul_cancel₀ hx0]⟩

lemma locSub_le (hx0 : x ≠ 0) {S : Subalgebra A F} (hRS : R ≤ S) (hxS : x⁻¹ ∈ S) :
    locSub R hx ≤ S := by
  rintro z ⟨r, hr, m, hz⟩
  have : z = r * x⁻¹ ^ m := by rw [← hz, inv_pow, mul_inv_cancel_right₀ (pow_ne_zero _ hx0)]
  rw [this]
  exact mul_mem (hRS hr) (pow_mem hxS _)

end locSub

/-- A subring `E` of a field of the form `R[1/x]`, with `R` embedded in the field, is the
localization of `R` away from `x`. -/
lemma isLocalization_away_locSub {A R F : Type*} [CommRing A] [CommRing R] [Field F] [Algebra A R]
    [Algebra A F] (f : R →ₐ[A] F) (hf : Function.Injective f) (x : R) (hx : f x ≠ 0)
    (E : Subalgebra A F) (hE : E = locSub f.range (AlgHom.mem_range_self f x)) [Algebra R E]
    (hRE : ∀ r, (algebraMap R E r : F) = f r) : IsLocalization.Away x E where
  map_units := by
    rintro ⟨_, m, rfl⟩
    rw [map_pow]
    refine IsUnit.pow m ?_
    have hinv : (f x)⁻¹ ∈ E := hE ▸ inv_mem_locSub _ hx
    refine IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext ?_)
    rw [Subalgebra.coe_mul, hRE, Subalgebra.coe_one, mul_inv_cancel₀ hx]
  surj := by
    rintro ⟨z, hz⟩
    rw [hE] at hz
    obtain ⟨_, ⟨r, rfl⟩, m, hm⟩ := hz
    refine ⟨⟨r, ⟨x ^ m, m, rfl⟩⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hRE, hRE, map_pow]
    exact hm
  exists_of_eq := by
    intro r₁ r₂ h
    have : r₁ = r₂ := hf (by rw [← hRE, ← hRE, h])
    exact ⟨1, by rw [this]⟩

/-- Base change of a localization: `M ⊗[A] C_g` is the localization of `M ⊗[A] C` away from
`1 ⊗ g`. -/
lemma isLocalization_away_tensor {A C E M : Type*} [CommRing A] [CommRing C] [CommRing E]
    [CommRing M] [Algebra A C] [Algebra A E] [Algebra A M] [Algebra C E] [IsScalarTower A C E]
    (g : C) [IsLocalization.Away g E] :
    letI := (Algebra.TensorProduct.map (AlgHom.id A M) (IsScalarTower.toAlgHom A C E)).toAlgebra
    IsLocalization.Away (1 ⊗ₜ g : M ⊗[A] C) (M ⊗[A] E) := by
  let := (Algebra.TensorProduct.map (AlgHom.id A M) (IsScalarTower.toAlgHom A C E)).toAlgebra
  have : IsScalarTower M (M ⊗[A] C) (M ⊗[A] E) := .of_algebraMap_eq fun m ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have := IsLocalization.tensorProduct_tensorProduct_right A M (Submonoid.powers g) E
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  rwa [Submonoid.map_powers] at this

/-- Let `E` be simultaneously a localization `C_g` and a localization `D_h`. If `1 ⊗ g` is a
nonzerodivisor of the nonzero ring `M ⊗[A] C` and `M ⊗[A] D` is a domain, then
`Spec (M ⊗[A] C)` is irreducible. -/
lemma irreducibleSpace_tensor_of_isLocalization {A C D E M : Type*} [CommRing A] [CommRing C]
    [CommRing D] [CommRing E] [CommRing M] [Algebra A C] [Algebra A D] [Algebra A E]
    [Algebra A M] [Algebra C E] [Algebra D E] [IsScalarTower A C E] [IsScalarTower A D E]
    (g : C) (h : D) [IsLocalization.Away g E] [IsLocalization.Away h E]
    (hg : (1 ⊗ₜ g : M ⊗[A] C) ∈ nonZeroDivisors (M ⊗[A] C)) [Nontrivial (M ⊗[A] C)]
    [IsDomain (M ⊗[A] D)] : IrreducibleSpace (PrimeSpectrum (M ⊗[A] C)) := by
  let iC := (Algebra.TensorProduct.map (AlgHom.id A M) (IsScalarTower.toAlgHom A C E)).toAlgebra
  let iD := (Algebra.TensorProduct.map (AlgHom.id A M) (IsScalarTower.toAlgHom A D E)).toAlgebra
  have hC := isLocalization_away_tensor (A := A) (M := M) (E := E) g
  have hD := isLocalization_away_tensor (A := A) (M := M) (E := E) h
  have hinj := IsLocalization.injective (M ⊗[A] E) (M := Submonoid.powers (1 ⊗ₜ g : M ⊗[A] C))
    (Submonoid.powers_le.mpr hg)
  have hnt : Nontrivial (M ⊗[A] E) := by
    refine ⟨⟨0, 1, fun h0 ↦ zero_ne_one (α := M ⊗[A] C) (hinj ?_)⟩⟩
    rw [map_zero, map_one, h0]
  have hh : (1 ⊗ₜ h : M ⊗[A] D) ≠ 0 := by
    intro h0
    have := IsLocalization.map_units (M ⊗[A] E) (⟨_, 1, pow_one _⟩ :
      Submonoid.powers (1 ⊗ₜ h : M ⊗[A] D))
    rw [h0, map_zero, isUnit_zero_iff] at this
    exact zero_ne_one this
  have := IsLocalization.isDomain_of_le_nonZeroDivisors (M ⊗[A] E)
    (M := Submonoid.powers (1 ⊗ₜ h : M ⊗[A] D))
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hh))
  exact irreducibleSpace_of_isLocalization_away (S := M ⊗[A] E) _ hg

/-- Two subalgebras `R, S` of a field with `R ⊆ S[1/s]` and `S ⊆ R[1/r]` have a common
localization `R[1/x] = S[1/y]`. -/
lemma exists_locSub_eq {A F : Type*} [CommRing A] [Field F] [Algebra A F] {R S : Subalgebra A F}
    {r s : F} (hr : r ∈ R) (hs : s ∈ S) (hr0 : r ≠ 0) (hs0 : s ≠ 0) (hRS : R ≤ locSub S hs)
    (hSR : S ≤ locSub R hr) :
    ∃ (x : F) (hx : x ∈ R) (y : F) (hy : y ∈ S), x ≠ 0 ∧ y ≠ 0 ∧
      (∃ c ∈ R, x = r * c) ∧ (∃ d ∈ S, y = s * d) ∧ locSub R hx = locSub S hy := by
  obtain ⟨c, hc, k, hk⟩ := hSR hs
  obtain ⟨d, hd, j, hj⟩ := hRS hr
  have hc0 : c ≠ 0 := by
    rw [← hk]
    exact mul_ne_zero hs0 (pow_ne_zero _ hr0)
  have hd0 : d ≠ 0 := by
    rw [← hj]
    exact mul_ne_zero hr0 (pow_ne_zero _ hs0)
  refine ⟨r * c, mul_mem hr hc, s * d, mul_mem hs hd, mul_ne_zero hr0 hc0, mul_ne_zero hs0 hd0,
    ⟨c, hc, rfl⟩, ⟨d, hd, rfl⟩, le_antisymm ?_ ?_⟩
  · -- `s⁻¹ = (r ^ (j+1) * (s * d)⁻¹)`-type identities
    have hsinv : s⁻¹ ∈ locSub S (mul_mem hs hd) := by
      have : s⁻¹ = d * (s * d)⁻¹ := by field_simp
      rw [this]
      exact mul_mem (le_locSub _ hd) (inv_mem_locSub _ (mul_ne_zero hs0 hd0))
    have hrinv : r⁻¹ ∈ locSub S (mul_mem hs hd) := by
      have : r⁻¹ = s ^ j * (s * d)⁻¹ * s := by
        rw [← hj]
        field_simp
      rw [this]
      exact mul_mem (mul_mem (pow_mem (le_locSub _ hs) _) (inv_mem_locSub _ (mul_ne_zero hs0 hd0)))
        (le_locSub _ hs)
    have hRS' : R ≤ locSub S (mul_mem hs hd) :=
      hRS.trans (locSub_le _ hs0 (le_locSub _) hsinv)
    refine locSub_le _ (mul_ne_zero hr0 hc0) hRS' ?_
    have : (r * c)⁻¹ = r⁻¹ * s⁻¹ * (r⁻¹) ^ k := by
      rw [← hk]
      field_simp
      rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hr0)]
    rw [this]
    exact mul_mem (mul_mem hrinv hsinv) (pow_mem hrinv _)
  · have hrinv : r⁻¹ ∈ locSub R (mul_mem hr hc) := by
      have : r⁻¹ = c * (r * c)⁻¹ := by field_simp
      rw [this]
      exact mul_mem (le_locSub _ hc) (inv_mem_locSub _ (mul_ne_zero hr0 hc0))
    have hsinv : s⁻¹ ∈ locSub R (mul_mem hr hc) := by
      have : s⁻¹ = r ^ k * (r * c)⁻¹ * r := by
        rw [← hk]
        field_simp
      rw [this]
      exact mul_mem (mul_mem (pow_mem (le_locSub _ hr) _) (inv_mem_locSub _ (mul_ne_zero hr0 hc0)))
        (le_locSub _ hr)
    have hSR' : S ≤ locSub R (mul_mem hr hc) :=
      hSR.trans (locSub_le _ hr0 (le_locSub _) hrinv)
    refine locSub_le _ (mul_ne_zero hs0 hd0) hSR' ?_
    have : (s * d)⁻¹ = s⁻¹ * r⁻¹ * (s⁻¹) ^ j := by
      rw [← hj]
      field_simp
      rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs0)]
    rw [this]
    exact mul_mem (mul_mem hsinv hrinv) (pow_mem hsinv _)

/-- If the ideal `J` is generated by elements `Q` with `P ∣ a_Q Q` for some `a_Q ≠ 0`, then a single
`a ≠ 0` works for all of `J`. -/
lemma exists_ne_zero_forall_dvd {A R : Type*} [CommRing A] [IsDomain A] [CommRing R]
    [Algebra A R] (P : R) (J : Ideal R) (hJ : J.FG)
    (h : ∀ Q ∈ J, ∃ a : A, a ≠ 0 ∧ P ∣ algebraMap A R a * Q) :
    ∃ a : A, a ≠ 0 ∧ ∀ Q ∈ J, P ∣ algebraMap A R a * Q := by
  classical
  obtain ⟨T, hT⟩ := hJ
  have hTJ (Q : T) : (Q : R) ∈ J := hT ▸ Submodule.subset_span Q.2
  choose f hf0 hfP using fun Q : T ↦ h Q (hTJ Q)
  refine ⟨∏ Q : T, f Q, Finset.prod_ne_zero_iff.mpr fun Q _ ↦ hf0 Q, fun Q hQ ↦ ?_⟩
  rw [← hT] at hQ
  induction hQ using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ ⟨Q, hQ⟩)
    rw [hb, map_mul, mul_comm (algebraMap A R _), mul_assoc]
    exact dvd_mul_of_dvd_right (hfP ⟨Q, hQ⟩) _
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact dvd_add hx hy
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact dvd_mul_of_dvd_right hx r

/-- **Core of generic irreducibility.** Let `C` be a finite type domain over the noetherian domain
`A`, embedded in a field `F`, and birational (over `A`) to the hypersurface `P = 0` through
`v : Fin n → F`, where `P` is absolutely irreducible: the values of polynomials at `v` and
`C` have a common localization, and `P` generates the ideal of relations of `v` generically.
Then the fibres of `Spec C → Spec A` over a dense open subset of `Spec A` are irreducible. -/
theorem exists_ne_zero_forall_irreducibleSpace_of_birational {A C F : Type*} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [CommRing C] [IsDomain C] [Algebra A C]
    [Algebra.FiniteType A C] [Field F] [Algebra A F] [Algebra C F] [IsScalarTower A C F]
    (hCF : Function.Injective (algebraMap C F)) (hAC : Function.Injective (algebraMap A C))
    (K L : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [IsAlgClosed L]
    [Algebra K L] {n : ℕ} (v : Fin n → F) (P : MvPolynomial (Fin n) A)
    (hP : Irreducible (map ((algebraMap K L).comp (algebraMap A K)) P)) (hPv : aeval v P = 0)
    (hker : ∀ Q : MvPolynomial (Fin n) A, aeval v Q = 0 →
      ∃ a : A, a ≠ 0 ∧ P ∣ MvPolynomial.C a * Q)
    (g : C) (hg : g ≠ 0)
    (hv : ∀ i, ∃ c : C, ∃ m : ℕ, v i * algebraMap C F g ^ m = algebraMap C F c)
    (h : MvPolynomial (Fin n) A) (hh : aeval v h ≠ 0)
    (hC : ∀ c : C, ∃ Q : MvPolynomial (Fin n) A, ∃ m : ℕ,
      algebraMap C F c * aeval v h ^ m = aeval v Q) :
    ∃ a : A, a ≠ 0 ∧ ∀ p : PrimeSpectrum A, a ∉ p.asIdeal →
      IrreducibleSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[A] C)) := by
  classical
  set ι := IsScalarTower.toAlgHom A C F
  set J := RingHom.ker (aeval (R := A) v)
  set κD := Ideal.kerLiftAlg (aeval (R := A) v)
  have hκD (Q : MvPolynomial (Fin n) A) : κD (Ideal.Quotient.mk J Q) = aeval v Q :=
    Ideal.kerLiftAlg_mk _ _
  have hgm : ι g ∈ ι.range := ι.mem_range_self g
  have hwm : aeval v h ∈ κD.range := hκD h ▸ κD.mem_range_self _
  have hg0 : ι g ≠ 0 := (map_ne_zero_iff _ hCF).mpr hg
  have hCD : ι.range ≤ locSub κD.range hwm := by
    intro z hz
    obtain ⟨c, rfl⟩ := (AlgHom.mem_range _).mp hz
    obtain ⟨Q, m, hQ⟩ := hC c
    exact ⟨aeval v Q, hκD Q ▸ κD.mem_range_self _, m, hQ⟩
  have hDC : κD.range ≤ locSub ι.range hgm := by
    intro z hz
    obtain ⟨d, rfl⟩ := (AlgHom.mem_range _).mp hz
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [hκD]
    have : (aeval (R := A) v).range ≤ locSub ι.range hgm := by
      rw [← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      obtain ⟨c, m, hc⟩ := hv i
      exact ⟨ι c, ι.mem_range_self c, m, hc⟩
    exact this (AlgHom.mem_range_self _ Q)
  obtain ⟨x, hx, y, hy, hx0, hy0, ⟨_, ⟨c, rfl⟩, rfl⟩, ⟨_, ⟨d, rfl⟩, rfl⟩, hE⟩ :=
    exists_locSub_eq hgm hwm hg0 hh hCD hDC
  set E := locSub ι.range hx
  have hcE (c : C) : ι c ∈ E := le_locSub hx (ι.mem_range_self c)
  have hdE (d : MvPolynomial (Fin n) A ⧸ J) : κD d ∈ E := hE ▸ le_locSub hy (κD.mem_range_self d)
  let : Algebra C E := (ι.codRestrict E hcE).toRingHom.toAlgebra
  let : Algebra (MvPolynomial (Fin n) A ⧸ J) E := (κD.codRestrict E hdE).toRingHom.toAlgebra
  have : IsScalarTower A C E := by
    refine .of_algebraMap_eq fun a ↦ Subtype.ext ?_
    simp [RingHom.algebraMap_toAlgebra, ι]
  have : IsScalarTower A (MvPolynomial (Fin n) A ⧸ J) E := ⟨fun a d e ↦ by
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective d
    apply Subtype.ext
    rw [Algebra.smul_def a (Ideal.Quotient.mk J Q), Algebra.smul_def, Algebra.smul_def,
      Algebra.smul_def]
    simp [RingHom.algebraMap_toAlgebra, mul_assoc]⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hx0
  have : IsLocalization.Away (g * c) E :=
    isLocalization_away_locSub ι hCF (g * c) (by rwa [map_mul]) E
      (locSub_congr hx (map_mul ι g c).symm _) fun _ ↦ rfl
  have : IsLocalization.Away (Ideal.Quotient.mk J h * d) E :=
    isLocalization_away_locSub κD (Ideal.kerLiftAlg_injective _) _
      (by rwa [map_mul, hκD]) E
      (hE.trans (locSub_congr hy (by rw [map_mul, hκD]; rfl) _)) fun _ ↦ rfl
  obtain ⟨a₁, ha₁, hflat⟩ :=
    Module.exists_flat_localizedModule_powers (R := A) (S := C) (C ⧸ Ideal.span {g * c})
  obtain ⟨a₂, ha₂, hBN⟩ := MvPolynomial.bertini_noether P K L hP
  obtain ⟨a₃, ha₃, hJ⟩ := exists_ne_zero_forall_dvd P J (IsNoetherian.noetherian J)
    fun Q hQ ↦ hker Q hQ
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∉
      (Set.range (PrimeSpectrum.comap (algebraMap A C)))ᶜ := by
    rw [Set.notMem_compl_iff]
    exact ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hAC)⟩
  obtain ⟨a₄, ha₄, hch⟩ := BertiniNoether.exists_ne_zero_forall_mem_of_isConstructible
    (PrimeSpectrum.isConstructible_range_comap
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance))).compl hgen
  refine ⟨a₁ * a₂ * a₃ * a₄, by simp [ha₁, ha₂, ha₃, ha₄], fun p hp ↦ ?_⟩
  simp only [p.2.mul_mem_iff_mem_or_mem, not_or] at hp
  obtain ⟨⟨⟨hp₁, hp₂⟩, hp₃⟩, hp₄⟩ := hp
  have hne (b : A) (hb : b ∉ p.asIdeal) : algebraMap A p.asIdeal.ResidueField b ≠ 0 := by
    rwa [Ne, Ideal.algebraMap_residueField_eq_zero]
  have hG := one_tmul_mem_nonZeroDivisors (M := p.asIdeal.ResidueField)
    (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hg hc0))
    (isUnit_iff_ne_zero.mpr (hne a₁ hp₁)) hflat
  have : Nontrivial (p.asIdeal.ResidueField ⊗[A] C) := by
    obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A C)) := by
      by_contra h
      exact hp₄ (hch p h)
    exact PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨PrimeSpectrum.preimageEquivFiber A C p ⟨q, hq⟩⟩
  have : IsDomain (p.asIdeal.ResidueField ⊗[A] (MvPolynomial (Fin n) A ⧸ J)) :=
    isDomain_tensor_quotient P J hPv a₃ (hne a₃ hp₃)
      (by simpa [MvPolynomial.algebraMap_eq] using hJ) (hBN _ (hne a₂ hp₂)).1
  exact irreducibleSpace_tensor_of_isLocalization (D := MvPolynomial (Fin n) A ⧸ J) (E := E)
    (g * c) (Ideal.Quotient.mk J h * d) hG

/-- Evaluation of a polynomial in `n + 1` variables, through `finSuccEquiv`. -/
lemma aeval_eq_eval₂_finSuccEquiv {k F : Type*} [CommRing k] [CommRing F] [Algebra k F] {r : ℕ}
    (v : Fin (r + 1) → F) (Q : MvPolynomial (Fin (r + 1)) k) :
    aeval v Q = Polynomial.eval₂ (aeval (v ∘ Fin.succ)).toRingHom (v 0) (finSuccEquiv k r Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply, Polynomial.eval₂_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, hp, aeval_X]
    congr 1
    induction i using Fin.cases with
    | zero => simp [finSuccEquiv_X_zero]
    | succ j => simp [finSuccEquiv_X_succ]

/-- **The ideal of relations of a hypersurface point.** Let `v = (y, t₁, …, t_r)` in a field with
`t` algebraically independent over the field `k`, and let `P` be an irreducible relation of `v`.
Then every relation of `v` is divisible by `P`. -/
lemma dvd_of_aeval_eq_zero {k F : Type*} [Field k] [Field F] [Algebra k F] {r : ℕ}
    (v : Fin (r + 1) → F) (hv : AlgebraicIndependent k (v ∘ Fin.succ))
    {P : MvPolynomial (Fin (r + 1)) k} (hP : Irreducible P) (hPv : aeval v P = 0)
    {Q : MvPolynomial (Fin (r + 1)) k} (hQv : aeval v Q = 0) : P ∣ Q := by
  have hφ : Function.Injective (aeval (R := k) (v ∘ Fin.succ)).toRingHom := by
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact algebraicIndependent_iff_injective_aeval.mp hv
  let ψ : FractionRing (MvPolynomial (Fin r) k) →+* F := IsFractionRing.lift hφ
  have hψ (x : MvPolynomial (Fin r) k) :
      ψ (algebraMap _ _ x) = aeval (R := k) (v ∘ Fin.succ) x :=
    IsFractionRing.lift_algebraMap hφ x
  have hcomp : ψ.comp (algebraMap _ _) = (aeval (R := k) (v ∘ Fin.succ)).toRingHom :=
    RingHom.ext hψ
  have hP' : Irreducible (finSuccEquiv k r P) :=
    (MulEquiv.irreducible_iff (finSuccEquiv k r).toMulEquiv).mpr hP
  have hev (Q : MvPolynomial (Fin (r + 1)) k) :
      Polynomial.eval₂ ψ (v 0) ((finSuccEquiv k r Q).map (algebraMap _ _)) = aeval v Q := by
    rw [Polynomial.eval₂_map, hcomp, aeval_eq_eval₂_finSuccEquiv]
  have hdeg : (finSuccEquiv k r P).natDegree ≠ 0 := by
    intro h0
    rw [Polynomial.natDegree_eq_zero] at h0
    obtain ⟨c, hc⟩ := h0
    have : (aeval (R := k) (v ∘ Fin.succ)).toRingHom c = 0 := by
      rw [← hPv, aeval_eq_eval₂_finSuccEquiv, ← hc, Polynomial.eval₂_C]
    rw [map_eq_zero_iff _ hφ] at this
    rw [this, map_zero] at hc
    exact hP.ne_zero ((finSuccEquiv k r).injective (hc.symm.trans (map_zero _).symm))
  have hprim := hP'.isPrimitive hdeg
  have hirr := (hprim.irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing (MvPolynomial (Fin r) k))).mp hP'
  suffices h : (finSuccEquiv k r P).map (algebraMap _ (FractionRing (MvPolynomial (Fin r) k))) ∣
      (finSuccEquiv k r Q).map (algebraMap _ _) by
    obtain ⟨T, hT⟩ := hprim.dvd_of_fraction_map_dvd_fraction_map h
    refine ⟨(finSuccEquiv k r).symm T, ?_⟩
    rw [← (finSuccEquiv k r).symm_apply_apply Q, hT, map_mul, AlgEquiv.symm_apply_apply]
  by_contra hnd
  obtain ⟨U, V, hUV⟩ := (hirr.coprime_iff_not_dvd).mpr hnd
  have := congrArg (Polynomial.eval₂ ψ (v 0)) hUV
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, hev, hev, hPv, hQv,
    Polynomial.eval₂_one] at this
  simp at this

/-- A finitely generated field extension `F` of a perfect field `L` is birational to a
hypersurface: there are `v = (y, t₁, …, t_r)` in `F` with `t` algebraically independent, such
that every element of `F` is a quotient of polynomials in `v`, and an irreducible relation `P`
of `v`. -/
lemma exists_hypersurface_of_perfectField (L F : Type*) [Field L] [PerfectField L] [Field F]
    [Algebra L F] [Algebra.EssFiniteType L F] :
    ∃ (r : ℕ) (v : Fin (r + 1) → F) (P : MvPolynomial (Fin (r + 1)) L),
      AlgebraicIndependent L (v ∘ Fin.succ) ∧ Irreducible P ∧ aeval v P = 0 ∧
      ∀ z : F, ∃ Q h : MvPolynomial (Fin (r + 1)) L, aeval v h ≠ 0 ∧ z * aeval v h = aeval v Q := by
  classical
  obtain ⟨s', hs', hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField L F
  set r := s'.card
  let t : Fin r → F := Subtype.val ∘ s'.equivFin.symm
  have hrange : Set.range t = Set.range ((↑) : s' → F) := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  have ht : AlgebraicIndependent L t := hs'.1.comp _ s'.equivFin.symm.injective
  set E := IntermediateField.adjoin L (Set.range ((↑) : s' → F))
  have halg : Algebra.IsAlgebraic E F := hs'.isAlgebraic_field
  have hsep' : Algebra.IsSeparable E F := by
    convert hsep <;> simp
  obtain ⟨G, hG⟩ := IntermediateField.fg_top L F
  have hfin : FiniteDimensional E F := by
    have h1 : IntermediateField.adjoin E (G : Set F) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ IntermediateField.adjoin L (G : Set F) := hG ▸ IntermediateField.mem_top
      exact (IntermediateField.adjoin_le_iff
        (T := (IntermediateField.adjoin E (G : Set F)).restrictScalars L)).mpr
        (IntermediateField.subset_adjoin E _) hx
    have := IntermediateField.finiteDimensional_adjoin (K := E) (S := (G : Set F))
      fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [h1] at this
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  obtain ⟨y, hy⟩ := Field.exists_primitive_element E F
  let v : Fin (r + 1) → F := Fin.cons y t
  have hvt : v ∘ Fin.succ = t := by
    funext i
    simp [v]
  have hdep : ¬ AlgebraicIndependent L v := by
    intro h
    have := h.transcendental_adjoin (i := 0) (s := Set.range Fin.succ) (by simp)
    rw [← Set.range_comp, hvt, hrange] at this
    exact this ((IntermediateField.isAlgebraic_adjoin_iff).mp (Algebra.IsAlgebraic.isAlgebraic y))
  have hne : {P : MvPolynomial (Fin (r + 1)) L | P ≠ 0 ∧ aeval v P = 0}.Nonempty := by
    obtain ⟨P, hP⟩ : ∃ P, ¬P = 0 ∧ aeval v P = 0 := by
      simpa [algebraicIndependent_iff, and_comm] using hdep
    exact ⟨P, hP⟩
  set P := Function.argminOn totalDegree _ hne
  have hP : P ≠ 0 ∧ aeval v P = 0 := Function.argminOn_mem _ _ hne
  have hmin (P' : MvPolynomial (Fin (r + 1)) L) (h0 : P' ≠ 0) (h1 : aeval v P' = 0) :
      totalDegree P ≤ totalDegree P' :=
    Function.argminOn_le totalDegree {P : MvPolynomial (Fin (r + 1)) L | P ≠ 0 ∧ aeval v P = 0}
      (a := P') ⟨h0, h1⟩
  have htop : IntermediateField.adjoin L (Set.range v) = ⊤ := by
    have := IntermediateField.adjoin_adjoin_left L (Set.range ((↑) : s' → F)) {y}
    rw [hy, IntermediateField.restrictScalars_top] at this
    rw [this, Fin.range_cons, hrange, Set.union_singleton]
  refine ⟨r, v, P, hvt ▸ ht, MvPolynomial.irreducible_of_forall_totalDegree_le hmin hP.1 hP.2,
    hP.2, fun z ↦ ?_⟩
  have hz : z ∈ IntermediateField.adjoin L (Set.range v) := htop ▸ IntermediateField.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  rw [Algebra.adjoin_range_eq_range_aeval] at ha hb
  obtain ⟨Q, rfl⟩ := ha
  obtain ⟨h, rfl⟩ := hb
  by_cases h0 : aeval v h = 0
  · exact ⟨0, 1, by simp, by simp [h0]⟩
  · exact ⟨Q, h, h0, div_mul_cancel₀ _ h0⟩

/-- If the kernel of a surjection `f : M → M'` of `R`-algebras is generated by elements having a
power killed by `b`, then for every `R`-algebra `k` in which `b` is a unit, the map
`Spec (k ⊗ M') → Spec (k ⊗ M)` is surjective. -/
lemma comap_surjective_map_tensor_of_ker {R M M' k : Type*} [CommRing R] [CommRing M]
    [CommRing M'] [CommRing k] [Algebra R M] [Algebra R M'] [Algebra R k] (f : M →ₐ[R] M')
    (hf : Function.Surjective f) (b : R) (hb : IsUnit (algebraMap R k b))
    (T : Set M) (hT : RingHom.ker f = Ideal.span T) (hTb : ∀ x ∈ T, ∃ m : ℕ, b • x ^ m = 0) :
    Function.Surjective
      (PrimeSpectrum.comap (Algebra.TensorProduct.map (AlgHom.id R k) f).toRingHom) := by
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _
    (Algebra.TensorProduct.map_surjective (AlgHom.id R k) f Function.surjective_id hf),
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  have : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R k) f).toRingHom =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R k) f) := rfl
  rw [this, Algebra.TensorProduct.lTensor_ker f hf]
  intro y hy
  have hle : (RingHom.ker f).map (Algebra.TensorProduct.includeRight (R := R) (A := k)) ≤
      nilradical (k ⊗[R] M) := by
    rw [hT, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, hmn⟩ := hTb x hx
    refine ⟨m, ?_⟩
    obtain ⟨u, hu⟩ := hb
    have h1 : (algebraMap R k b) ⊗ₜ[R] (x ^ m) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, hmn, TensorProduct.tmul_zero]
    have h2 : (1 : k) ⊗ₜ[R] (x ^ m) =
        ((↑u⁻¹ : k) ⊗ₜ[R] (1 : M)) * ((algebraMap R k b) ⊗ₜ[R] (x ^ m)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hu, Units.inv_mul]
    rw [← map_pow, Algebra.TensorProduct.includeRight_apply, h2, h1, mul_zero]
    rfl
  exact hle hy

/-- Base change of `k ⊗[A] C` along a field extension `k → k'` is surjective on spectra. -/
lemma comap_surjective_map_tensor_of_field {A k k' C : Type*} [CommRing A] [Field k] [Field k']
    [CommRing C] [Algebra A k] [Algebra A k'] [Algebra k k'] [IsScalarTower A k k'] [Algebra A C] :
    Function.Surjective (PrimeSpectrum.comap
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A k k') (AlgHom.id A C)).toRingHom) := by
  let e := Algebra.TensorProduct.cancelBaseChange A k k' k' C
  let c := Algebra.TensorProduct.comm k (k ⊗[A] C) k'
  have hf : (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A k k') (AlgHom.id A C)).toRingHom =
      (e.toRingHom.comp c.toRingHom).comp (algebraMap (k ⊗[A] C) ((k ⊗[A] C) ⊗[k] k')) := by
    refine RingHom.ext fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      simp [e, c, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.algebraMap_eq_smul_one a]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hf, PrimeSpectrum.comap_comp, PrimeSpectrum.comap_comp]
  refine (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := k ⊗[A] C)
    (B := (k ⊗[A] C) ⊗[k] k')).comp (Function.Surjective.comp ?_ ?_)
  · exact (PrimeSpectrum.comapEquiv c.toRingEquiv.symm).surjective
  · exact (PrimeSpectrum.comapEquiv e.toRingEquiv.symm).surjective

/-- Let `A'` be a domain, `L` a field containing `A'`, and `C` an `A`-algebra with `A → A'`. If
`y ∈ A' ⊗[A] C` vanishes in `L ⊗[A] C`, then `b • y = 0` for some `b ≠ 0` in `A'`. -/
lemma exists_smul_eq_zero_of_map_eq_zero {A A' L C : Type*} [CommRing A] [CommRing A']
    [IsDomain A'] [Field L] [CommRing C] [Algebra A A'] [Algebra A' L] [Algebra A L]
    [IsScalarTower A A' L] [Algebra A C] (hinj : Function.Injective (algebraMap A' L))
    (y : A' ⊗[A] C)
    (hy : Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' L) (AlgHom.id A C) y = 0) :
    ∃ b : A', b ≠ 0 ∧ b • y = 0 := by
  let K' := FractionRing A'
  let : Algebra K' L := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower A' K' L := .of_algebraMap_eq fun a ↦
    (IsFractionRing.lift_algebraMap hinj a).symm
  have : IsScalarTower A K' L := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A A' K', ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K' L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K' L).injective)
  let j : K' ⊗[A] C →ₗ[A] L ⊗[A] C :=
    LinearMap.rTensor C ((Algebra.linearMap K' L).restrictScalars A)
  have hj : Function.Injective j := by
    refine Function.LeftInverse.injective (g := LinearMap.rTensor C (g.restrictScalars A)) ?_
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    have : (g.restrictScalars A).comp ((Algebra.linearMap K' L).restrictScalars A) =
        LinearMap.id := by
      ext a
      exact congrArg (fun φ : K' →ₗ[K'] K' ↦ φ a) hg
    rw [this, LinearMap.rTensor_id, LinearMap.id_apply]
  let : Algebra (A' ⊗[A] C) (K' ⊗[A] C) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' K') (AlgHom.id A C)).toAlgebra
  have : IsScalarTower A' (A' ⊗[A] C) (K' ⊗[A] C) := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have := IsLocalization.tensorProduct_tensorProduct A C (nonZeroDivisors A') K'
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  have hcomp (z : A' ⊗[A] C) : j (algebraMap (A' ⊗[A] C) (K' ⊗[A] C) z) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' L) (AlgHom.id A C) z := by
    induction z using TensorProduct.inductionOn with
    | tmul a c => simp [j, RingHom.algebraMap_toAlgebra]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hcomp := hcomp y
  rw [hy, ← map_zero j] at hcomp
  obtain ⟨⟨_, b, hb, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Algebra.algebraMapSubmonoid (A' ⊗[A] C) (nonZeroDivisors A')) _ _).mp (hj hcomp)
  exact ⟨b, nonZeroDivisors.coe_ne_zero ⟨b, hb⟩, by rwa [Algebra.smul_def]⟩

/-- A multivariate polynomial over a field which is irreducible over an extension field is
irreducible. -/
lemma irreducible_of_irreducible_map {σ K L : Type*} [Field K] [Field L] (f : K →+* L)
    {P : MvPolynomial σ K} (hP : Irreducible (map f P)) : Irreducible P := by
  have hunit (a : MvPolynomial σ K) (ha : IsUnit (map f a)) : IsUnit a := by
    rw [isUnit_iff_totalDegree_of_isReduced] at ha ⊢
    rw [coeff_map, BertiniNoether.totalDegree_map_of_injective f.injective] at ha
    exact ⟨isUnit_iff_ne_zero.mpr fun h0 ↦ by simp [h0] at ha, ha.2⟩
  refine ⟨fun h ↦ hP.not_isUnit (h.map _), fun a b hab ↦ ?_⟩
  rw [hab, map_mul] at hP
  exact (hP.isUnit_or_isUnit rfl).imp (hunit a) (hunit b)

/-- Clearing denominators in a divisibility over the fraction field. -/
lemma exists_ne_zero_dvd_C_mul_of_map_dvd {σ A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] {P Q : MvPolynomial σ A}
    (h : map (algebraMap A K) P ∣ map (algebraMap A K) Q) :
    ∃ a : A, a ≠ 0 ∧ P ∣ C a * Q := by
  classical
  obtain ⟨R, hR⟩ := h
  obtain ⟨⟨b, hb⟩, hbR⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    R.coeffs
  obtain ⟨R', hR'⟩ : C (algebraMap A K b) * R ∈ Set.range (map (σ := σ) (algebraMap A K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨m, hm, rfl⟩ := mem_coeffs_iff.mp hc
    rw [coeff_C_mul]
    by_cases h0 : R.coeff m = 0
    · rw [h0, mul_zero]
      exact ⟨0, map_zero _⟩
    · obtain ⟨d, hd⟩ := hbR (R.coeff m) (mem_coeffs_iff.mpr ⟨m, mem_support_iff.mpr h0, rfl⟩)
      exact ⟨d, by rw [hd, Algebra.smul_def]⟩
  refine ⟨b, nonZeroDivisors.coe_ne_zero ⟨b, hb⟩, R', map_injective _
    (IsFractionRing.injective A K) ?_⟩
  rw [map_mul, map_mul, map_C, hR', hR]
  ring

/-- Generic irreducibility descends along a finite type extension of domains and a surjective
algebra map whose kernel elements have powers annihilated by nonzero scalars. -/
private lemma exists_ne_zero_forall_irreducibleSpace_of_torsion_nilpotent_ker
    {A A' C D : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing A'] [IsDomain A'] [Algebra A A'] [Algebra.FiniteType A A']
    [CommRing C] [Algebra A C] [Algebra.FiniteType A C] [CommRing D] [Algebra A' D]
    (hA'inj : Function.Injective (algebraMap A A')) (f : A' ⊗[A] C →ₐ[A'] D)
    (hf : Function.Surjective f)
    (hnil : ∀ x ∈ RingHom.ker f, ∃ b : A', b ≠ 0 ∧ ∃ m : ℕ, b • x ^ m = 0)
    (a' : A') (ha' : a' ≠ 0)
    (hB : ∀ p : PrimeSpectrum A', a' ∉ p.asIdeal →
      IrreducibleSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[A'] D))) :
    ∃ a : A, a ≠ 0 ∧ ∀ p : PrimeSpectrum A, a ∉ p.asIdeal →
      IrreducibleSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[A] C)) := by
  classical
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing A A'
  have : IsNoetherianRing (A' ⊗[A] C) := Algebra.FiniteType.isNoetherianRing A' _
  obtain ⟨T', hT'⟩ := (IsNoetherian.noetherian (RingHom.ker f) :
    (RingHom.ker f).FG)
  choose! b hb0 m hbm using hnil
  have hTk (x : A' ⊗[A] C) (hx : x ∈ T') : x ∈ RingHom.ker f :=
    hT' ▸ Submodule.subset_span hx
  obtain ⟨bb, hbb⟩ : ∃ bb, bb = ∏ x ∈ T', b x := ⟨_, rfl⟩
  have hbb0 : bb ≠ 0 := hbb ▸ Finset.prod_ne_zero_iff.mpr fun x hx ↦ hb0 x (hTk x hx)
  have hTb : ∀ x ∈ (T' : Set (A' ⊗[A] C)), ∃ m : ℕ, bb • x ^ m = 0 := by
    intro x hx
    refine ⟨m x, ?_⟩
    rw [hbb, ← Finset.mul_prod_erase T' b hx, mul_comm, mul_smul, hbm x (hTk x hx), smul_zero]
  -- Chevalley: the image of `D(a' bb)` contains a dense open of `Spec A`
  set Z := PrimeSpectrum.comap (algebraMap A A') ''
    (PrimeSpectrum.basicOpen (a' * bb) : Set (PrimeSpectrum A'))
  have hZ : Topology.IsConstructible Z := PrimeSpectrum.isConstructible_comap_image
    (RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp inferInstance))
    PrimeSpectrum.isConstructible_basicOpen
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∉ Zᶜ := by
    rw [Set.notMem_compl_iff]
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hA'inj)⟩
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    exact mul_ne_zero ha' hbb0
  obtain ⟨a, ha, hZa⟩ := BertiniNoether.exists_ne_zero_forall_mem_of_isConstructible hZ.compl hgen
  refine ⟨a, ha, fun p hp ↦ ?_⟩
  obtain ⟨p', hp'O, rfl⟩ : p ∈ Z := by
    by_contra h
    exact hp (hZa p h)
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, p'.2.mul_mem_iff_mem_or_mem, not_or] at hp'O
  -- transfer the irreducibility of the fibres
  have h1 := hB p' hp'O.1
  have h2 : IrreducibleSpace (PrimeSpectrum (p'.asIdeal.ResidueField ⊗[A'] (A' ⊗[A] C))) :=
    irreducibleSpace_of_comap_surjective _ (comap_surjective_map_tensor_of_ker f
      hf bb (isUnit_iff_ne_zero.mpr
        (by rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact hp'O.2)) T' hT'.symm hTb)
  have h3 : IrreducibleSpace (PrimeSpectrum (p'.asIdeal.ResidueField ⊗[A] C)) :=
    irreducibleSpace_of_comap_surjective (Algebra.TensorProduct.cancelBaseChange A A'
      p'.asIdeal.ResidueField p'.asIdeal.ResidueField C).symm.toRingHom
      (PrimeSpectrum.comapEquiv _).surjective
  let : Algebra (PrimeSpectrum.comap (algebraMap A A') p').asIdeal.ResidueField
      p'.asIdeal.ResidueField :=
    (Ideal.ResidueField.map _ p'.asIdeal (algebraMap A A') rfl).toAlgebra
  have : IsScalarTower A (PrimeSpectrum.comap (algebraMap A A') p').asIdeal.ResidueField
      p'.asIdeal.ResidueField := .of_algebraMap_eq fun x ↦
    (IsScalarTower.algebraMap_apply A A' p'.asIdeal.ResidueField x).trans
      (Ideal.ResidueField.map_algebraMap _ p'.asIdeal (algebraMap A A') rfl x).symm
  exact irreducibleSpace_of_comap_surjective _
    (comap_surjective_map_tensor_of_field (k' := p'.asIdeal.ResidueField))

/-- **Spreading out.** Let `φ : L ⊗[A] C → F` be a map to a field whose kernel is nil, such that
`F` is birational to an (absolutely) irreducible hypersurface over the algebraically closed field
`L ⊇ A`, as in `exists_hypersurface_of_perfectField`, where the coordinates `v` have a common
denominator coming from `L ⊗[A] C`. Then the fibres of `Spec C → Spec A` over a dense open subset
of `Spec A` are irreducible. -/
theorem exists_ne_zero_forall_irreducibleSpace_of_hypersurface {A C : Type*} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
    (L F : Type*) [Field L] [IsAlgClosed L] [Algebra A L]
    (hAL : Function.Injective (algebraMap A L)) [Field F] [Algebra L F]
    (φ : L ⊗[A] C →ₐ[L] F) (hφ : ∀ y, φ y = 0 → IsNilpotent y)
    (w : L ⊗[A] C) (hw : φ w ≠ 0) {r : ℕ} (u : Fin (r + 1) → L ⊗[A] C) (v : Fin (r + 1) → F)
    (hvu : ∀ i, v i * φ w = φ (u i)) (P : MvPolynomial (Fin (r + 1)) L)
    (hv : AlgebraicIndependent L (v ∘ Fin.succ)) (hP : Irreducible P) (hPv : aeval v P = 0)
    (hrep : ∀ z : F, ∃ Q h : MvPolynomial (Fin (r + 1)) L,
      aeval v h ≠ 0 ∧ z * aeval v h = aeval v Q) :
    ∃ a : A, a ≠ 0 ∧ ∀ p : PrimeSpectrum A, a ∉ p.asIdeal →
      IrreducibleSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[A] C)) := by
  classical
  obtain ⟨X, hX⟩ := Algebra.FiniteType.out (R := A) (A := C)
  choose Qx hx hxne hxeq using fun x : C ↦ hrep (φ (1 ⊗ₜ x))
  choose Sexp hSexp using fun y : L ⊗[A] C ↦ TensorProduct.exists_finset y
  -- the finitely many coefficients needed
  let T : Finset L := P.coeffs ∪ X.biUnion (fun x ↦ (Qx x).coeffs ∪ (hx x).coeffs) ∪
    (Sexp w).image Prod.fst ∪ Finset.univ.biUnion (fun i ↦ (Sexp (u i)).image Prod.fst)
  obtain ⟨A', hA'⟩ : ∃ A' : Subalgebra A L, A' = Algebra.adjoin A (T : Set L) := ⟨_, rfl⟩
  have hTA' : (T : Set L) ⊆ A' := hA' ▸ Algebra.subset_adjoin
  have : Algebra.FiniteType A A' :=
    (Subalgebra.fg_iff_finiteType _).mp (hA' ▸ Subalgebra.fg_adjoin_finset T)
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing A A'
  have hlift (Q : MvPolynomial (Fin (r + 1)) L) (hQ : Q.coeffs ⊆ T) :
      ∃ Q' : MvPolynomial (Fin (r + 1)) A', map (algebraMap A' L) Q' = Q := by
    have : Q ∈ Set.range (map (σ := Fin (r + 1)) (algebraMap A' L)) := by
      rw [mem_range_map_iff_coeffs_subset]
      intro c hc
      exact ⟨⟨c, hTA' (hQ hc)⟩, rfl⟩
    exact this
  let ι' : A' ⊗[A] C →ₐ[A'] L ⊗[A] C :=
    Algebra.TensorProduct.map (Algebra.ofId A' L) (AlgHom.id A C)
  have hliftT (y : L ⊗[A] C) (hy : (Sexp y).image Prod.fst ⊆ T) :
      ∃ y' : A' ⊗[A] C, ι' y' = y := by
    refine ⟨∑ i ∈ (Sexp y).attach,
      (⟨i.1.1, hTA' (hy (Finset.mem_image_of_mem _ i.2))⟩ : A') ⊗ₜ i.1.2, ?_⟩
    calc _ = ∑ i ∈ (Sexp y).attach, i.1.1 ⊗ₜ[A] i.1.2 := by
          rw [map_sum]
          rfl
      _ = ∑ i ∈ Sexp y, i.1 ⊗ₜ[A] i.2 :=
        Finset.sum_attach _ (fun i : L × C ↦ i.1 ⊗ₜ[A] i.2)
      _ = y := (hSexp y).symm
  -- the algebras over `A'`
  have hA'L : Function.Injective (algebraMap A' L) := Subtype.val_injective
  have : IsScalarTower A' L F := inferInstance
  have hA'F : Function.Injective (algebraMap A' F) := by
    rw [IsScalarTower.algebraMap_eq A' L F]
    exact (algebraMap L F).injective.comp hA'L
  let Φ : A' ⊗[A] C →ₐ[A'] F := (φ.restrictScalars A').comp ι'
  have hΦ (y : A' ⊗[A] C) : Φ y = φ (ι' y) := rfl
  let K' := FractionRing A'
  let : Algebra K' L := (IsFractionRing.lift hA'L).toAlgebra
  have : IsScalarTower A' K' L := .of_algebraMap_eq fun a ↦
    (IsFractionRing.lift_algebraMap hA'L a).symm
  let : Algebra K' F := ((algebraMap L F).comp (algebraMap K' L)).toAlgebra
  have : IsScalarTower K' L F := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A' K' F := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A' L F, IsScalarTower.algebraMap_apply A' K' L]
    rfl
  -- lifts of the data
  obtain ⟨P', hP'⟩ := hlift P fun c hc ↦ Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ hc))
  choose! Q' hQ' using fun x (hxX : x ∈ X) ↦ hlift (Qx x) fun c hc ↦ Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨x, hxX, Finset.mem_union_left _ hc⟩)))
  choose! h' hh' using fun x (hxX : x ∈ X) ↦ hlift (hx x) fun c hc ↦ Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨x, hxX, Finset.mem_union_right _ hc⟩)))
  obtain ⟨w', hw'⟩ := hliftT w fun c hc ↦ Finset.mem_union_left _ (Finset.mem_union_right _ hc)
  choose u' hu' using fun i ↦ hliftT (u i) fun c hc ↦ Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩)
  have haeval (Q : MvPolynomial (Fin (r + 1)) A') : aeval v Q = aeval v (map (algebraMap A' L) Q) :=
    (aeval_map_algebraMap L v Q).symm
  -- the common denominator of the generators of `C`
  let H : MvPolynomial (Fin (r + 1)) A' := ∏ x ∈ X, h' x
  have hH : aeval v H = ∏ x ∈ X, aeval v (hx x) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun x hxX ↦ ?_
    rw [haeval, hh' x hxX]
  have hH0 : aeval v H ≠ 0 := by
    rw [hH]
    exact Finset.prod_ne_zero_iff.mpr fun x _ ↦ hxne x
  have hHm : aeval v H ∈ (aeval (R := A') v).range := AlgHom.mem_range_self _ _
  have hgen (x : C) (hxX : x ∈ X) : φ (1 ⊗ₜ x) ∈ locSub (aeval (R := A') v).range hHm := by
    refine ⟨aeval v (Q' x * ∏ y ∈ X.erase x, h' y), AlgHom.mem_range_self _ _, 1, ?_⟩
    rw [pow_one, hH, ← Finset.mul_prod_erase X _ hxX, ← mul_assoc, hxeq, map_mul, map_prod,
      haeval, hQ' x hxX]
    congr 1
    refine Finset.prod_congr rfl fun y hy ↦ ?_
    rw [haeval, hh' y (Finset.mem_of_mem_erase hy)]
  have hall (c : C) : φ (1 ⊗ₜ c) ∈ locSub (aeval (R := A') v).range hHm := by
    have hc : c ∈ Algebra.adjoin A (X : Set C) := hX ▸ Algebra.mem_top
    induction hc using Algebra.adjoin_induction with
    | mem x hxX => exact hgen x hxX
    | algebraMap a =>
      have : φ (1 ⊗ₜ algebraMap A C a) = algebraMap A' F (algebraMap A A' a) := by
        rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply A L,
          AlgHom.commutes, IsScalarTower.algebraMap_apply A' L F]
        rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy =>
      rw [TensorProduct.tmul_add, map_add]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [← one_mul (1 : L), ← Algebra.TensorProduct.tmul_mul_tmul, map_mul]
      exact mul_mem hx hy
  have hC''le : Φ.range ≤ locSub (aeval (R := A') v).range hHm := by
    intro z hz
    obtain ⟨y, rfl⟩ := (AlgHom.mem_range _).mp hz
    clear hz
    induction y using TensorProduct.inductionOn with
    | tmul a c =>
      have : Φ (a ⊗ₜ c) = algebraMap A' F a * φ (1 ⊗ₜ c) := by
        rw [hΦ, ← one_mul c, ← mul_one (a : A'), ← Algebra.TensorProduct.tmul_mul_tmul,
          map_mul, map_mul, mul_one, one_mul]
        congr 1
        have : ι' (a ⊗ₜ 1) = algebraMap L (L ⊗[A] C) (algebraMap A' L a) := rfl
        rw [this, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
      rw [this]
      exact mul_mem (Subalgebra.algebraMap_mem _ a) (hall c)
    | add x y hx hy =>
      rw [map_add]
      exact add_mem hx hy
  -- apply the core theorem to `C'' = Φ(A' ⊗ C) ⊆ F`
  have : Algebra.FiniteType A' Φ.range :=
    Algebra.FiniteType.of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have : IsScalarTower A' Φ.range F := .of_algebraMap_eq fun _ ↦ rfl
  have hAC : Function.Injective (algebraMap A' Φ.range) := by
    intro a b hab
    apply hA'F
    exact congrArg (fun z : Φ.range ↦ (z : F)) hab
  have hvK : AlgebraicIndependent K' (v ∘ Fin.succ) :=
    hv.restrictScalars (algebraMap K' L).injective
  have hPL : map (algebraMap A' L) P' = P := hP'
  have hPK : Irreducible (map (algebraMap A' K') P') := by
    refine irreducible_of_irreducible_map (algebraMap K' L) ?_
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq, hPL]
    exact hP
  have hPv' : aeval v P' = 0 := by rw [haeval, hPL, hPv]
  have hker (Q : MvPolynomial (Fin (r + 1)) A') (hQ : aeval v Q = 0) :
      ∃ a : A', a ≠ 0 ∧ P' ∣ MvPolynomial.C a * Q := by
    refine exists_ne_zero_dvd_C_mul_of_map_dvd (K := K') (dvd_of_aeval_eq_zero v hvK hPK ?_ ?_)
    · rw [aeval_map_algebraMap]
      exact hPv'
    · rw [aeval_map_algebraMap]
      exact hQ
  have hg0 : (⟨Φ w', Φ.mem_range_self w'⟩ : Φ.range) ≠ 0 := by
    intro h0
    apply hw
    rw [← hw', ← hΦ]
    exact congrArg Subtype.val h0
  have hvu' (i : Fin (r + 1)) : v i * Φ w' = Φ (u' i) := by
    rw [hΦ, hΦ, hw', hu']
    exact hvu i
  obtain ⟨a', ha', hB⟩ := exists_ne_zero_forall_irreducibleSpace_of_birational
    (A := A') (C := Φ.range) (F := F) Subtype.val_injective hAC K' L v P'
    (by rw [← IsScalarTower.algebraMap_eq, hPL]; exact hP) hPv' hker
    ⟨Φ w', Φ.mem_range_self w'⟩ hg0
    (fun i ↦ ⟨⟨Φ (u' i), Φ.mem_range_self _⟩, 1, by
      rw [pow_one]
      exact hvu' i⟩)
    H hH0 (fun c ↦ by
      obtain ⟨_, ⟨Q, rfl⟩, m, hm⟩ := hC''le c.2
      exact ⟨Q, m, hm⟩)
  -- the kernel of `A' ⊗ C → C''` is nil generically
  have hnil (x : A' ⊗[A] C) (hx : x ∈ RingHom.ker Φ.rangeRestrict) :
      ∃ b : A', b ≠ 0 ∧ ∃ m : ℕ, b • x ^ m = 0 := by
    have hx0 : φ (ι' x) = 0 := congrArg Subtype.val (RingHom.mem_ker.mp hx)
    obtain ⟨m, hm⟩ := hφ _ hx0
    have hm' : ι' (x ^ m) = 0 := by rw [map_pow]; exact hm
    have hιeq (y : A' ⊗[A] C) :
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' L) (AlgHom.id A C) y = ι' y := by
      induction y using TensorProduct.inductionOn with
      | tmul a c => rfl
      | add y z hy hz => rw [map_add, map_add, hy, hz]
    have h3 := (hιeq (x ^ m)).trans hm'
    obtain ⟨b, hb, hbm⟩ := exists_smul_eq_zero_of_map_eq_zero (A := A) (C := C) hA'L (x ^ m) h3
    exact ⟨b, hb, m, hbm⟩
  have hA'inj : Function.Injective (algebraMap A A') := fun x y h ↦ hAL (by
    rw [IsScalarTower.algebraMap_apply A A' L x, h, ← IsScalarTower.algebraMap_apply])
  exact exists_ne_zero_forall_irreducibleSpace_of_torsion_nilpotent_ker hA'inj
    Φ.rangeRestrict Φ.rangeRestrict_surjective hnil a' ha' hB

end GenericIrreducibility

open GenericIrreducibility in
/-- **Generic irreducibility of fibres** (ring-theoretic form of Stacks `0559`). Let `A` be a
noetherian domain with fraction field `K`, `L` an algebraically closed extension of `K` and `C` a
finite type `A`-algebra whose geometric generic fibre `Spec (L ⊗[A] C)` is irreducible. Then there
is `a ≠ 0` in `A` such that the fibres `Spec (κ(p) ⊗[A] C)` over all primes `p ∌ a` are
irreducible. -/
theorem exists_ne_zero_forall_isIrreducible_fiber {A C : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C] (K L : Type*)
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [IsAlgClosed L] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L]
    (hC : IrreducibleSpace (PrimeSpectrum (L ⊗[A] C))) :
    ∃ a : A, a ≠ 0 ∧ ∀ p : PrimeSpectrum A, a ∉ p.asIdeal →
      IrreducibleSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[A] C)) := by
  classical
  have hN := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hC
  let R := L ⊗[A] C ⧸ nilradical (L ⊗[A] C)
  let F := FractionRing R
  let φ : L ⊗[A] C →ₐ[L] F :=
    (IsScalarTower.toAlgHom L R F).comp (Ideal.Quotient.mkₐ L (nilradical (L ⊗[A] C)))
  have hφ (y : L ⊗[A] C) (hy : φ y = 0) : IsNilpotent y := by
    have : Ideal.Quotient.mk (nilradical (L ⊗[A] C)) y = 0 :=
      IsFractionRing.injective R F (by rw [map_zero]; exact hy)
    exact (Ideal.Quotient.eq_zero_iff_mem.mp this)
  have : Algebra.EssFiniteType L F := Algebra.EssFiniteType.comp L R F
  obtain ⟨r, v, P, hv, hP, hPv, hrep⟩ := exists_hypersurface_of_perfectField L F
  obtain ⟨⟨b, hb⟩, hbv⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (Finset.univ.image v)
  choose n hn using fun i ↦ hbv (v i) (Finset.mem_image_of_mem v (Finset.mem_univ i))
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
  choose u hu using fun i ↦ Ideal.Quotient.mk_surjective (n i)
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  refine exists_ne_zero_forall_irreducibleSpace_of_hypersurface L F hAL φ hφ w ?_ u v
    (fun i ↦ ?_) P hv hP hPv hrep
  · exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors (M := nonZeroDivisors R) F le_rfl hb
  · calc v i * φ w = ((⟨_, hb⟩ : nonZeroDivisors R) : R) • v i := by
          rw [mul_comm]
          exact (Algebra.smul_def (R := R) (A := F) _ _).symm
      _ = φ (u i) := by
          rw [← hn i, ← hu i]
          rfl
