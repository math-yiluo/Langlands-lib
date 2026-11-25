/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Unramified.Field

/-!
# Standard etale algebras lift along quotient maps, and are reduced over reduced rings

Every standard etale algebra over a quotient `R ⧸ I` is the base change of a standard etale
algebra over `R`. This is the ring theoretic half of the statement that etale morphisms lift
along closed immersions.

## Main results

- `StandardEtalePair.exists_algEquiv_quotient_tensor_ring`: for every
  `P : StandardEtalePair (R ⧸ I)` there is a `Q : StandardEtalePair R` together with an
  `R ⧸ I`-algebra isomorphism `(R ⧸ I) ⊗[R] Q.Ring ≃ₐ[R ⧸ I] P.Ring`.
- `StandardEtalePair.exists_algEquiv_tensor_ring_of_coeffs_subset`: a standard etale pair over
  `S` whose coefficients come from `R` is the base change of a standard etale pair over `R`.
- `StandardEtalePair.exists_subalgebra_finite_algEquiv_tensor_ring`: finitely many standard
  etale algebras over an integral `A`-algebra `B` descend to a subalgebra of `B` finite over `A`.
- `Algebra.IsStandardEtale.exists_algEquiv_quotient_tensor`: if `S` is a standard etale
  `R ⧸ I`-algebra, then there is a standard etale `R`-algebra `T` together with an
  `R ⧸ I`-algebra isomorphism `(R ⧸ I) ⊗[R] T ≃ₐ[R ⧸ I] S`.
- `AdjoinRoot.etale_X_pow_sub_C`: for `n` and `t` invertible in `R`, the Kummer algebra
  `R[X]/(Xⁿ - t)` is etale over `R`.
- `StandardEtalePair.isReduced_ring`: a standard etale algebra over a reduced ring is reduced.

## Implementation notes

Lifting `f`, `g` and the witnesses of `StandardEtalePair.cond` naively does not work, since a lift
of the identity witnessing `cond` only holds modulo `I`. Instead one observes that for a monic
`f : R[X]` and an *arbitrary* `g : R[X]` the pair `(f, g * f')` is a standard etale pair
(`StandardEtalePair.ofMonic`), since `f'` trivially divides `g * f'`; and that replacing `g` by
`g * f'` does not change the associated standard etale algebra
(`StandardEtalePair.mulDerivativeRingEquiv`), since `f'` is already invertible there. So one lifts
`f` to a monic `F` of the same degree, lifts `g` to an arbitrary `G`, and takes the pair
`(F, G * F')` over `R`.
-/

@[expose] public section

universe u v

open Polynomial

open scoped TensorProduct

noncomputable section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace StandardEtalePair

/-- Two standard etale pairs over `R` with the same `f` and the same `g` are equal: the
remaining fields of `StandardEtalePair` are proofs. -/
@[ext]
protected lemma ext {P Q : StandardEtalePair R} (hf : P.f = Q.f) (hg : P.g = Q.g) : P = Q := by
  obtain ⟨f₁, _, g₁, _⟩ := P
  obtain ⟨f₂, _, g₂, _⟩ := Q
  obtain rfl : f₁ = f₂ := hf
  obtain rfl : g₁ = g₂ := hg
  rfl

/-- For a monic `f : R[X]` and an arbitrary `g : R[X]`, the pair `(f, g * f')` is a standard etale
pair, since `f'` divides `(g * f') ^ 1`. -/
@[simps]
def ofMonic {f : R[X]} (hf : f.Monic) (g : R[X]) : StandardEtalePair R where
  f := f
  monic_f := hf
  g := g * derivative f
  cond := ⟨g, 0, 1, by ring⟩

@[simp]
lemma map_ofMonic {f : R[X]} (hf : f.Monic) (g : R[X]) (φ : R →+* S) :
    (ofMonic hf g).map φ = ofMonic (hf.map φ) (g.map φ) :=
  StandardEtalePair.ext (by simp) (by simp [Polynomial.map_mul])

/-- The standard etale pair `(f, g * f')` associated to the standard etale pair `P = (f, g)`.
It has the same standard etale algebra as `P`, see
`StandardEtalePair.mulDerivativeRingEquiv`. -/
@[simps!]
def mulDerivative (P : StandardEtalePair R) : StandardEtalePair R := ofMonic P.monic_f P.g

/-- Inverting the derivative `f'` in the standard etale algebra `R[X][1/g]/f` of `(f, g)` does not
change it, since `f'` is already invertible there: `R[X][1/(g * f')]/f ≃ R[X][1/g]/f`. -/
def mulDerivativeRingEquiv (P : StandardEtalePair R) : P.mulDerivative.Ring ≃ₐ[R] P.Ring := by
  have h₁ : P.mulDerivative.HasMap P.X := by
    refine ⟨by simpa using P.hasMap_X.1, ?_⟩
    simpa [map_mul] using P.hasMap_X.2.mul P.hasMap_X.isUnit_derivative_f
  have h₂ : P.HasMap P.mulDerivative.X := by
    refine ⟨by simpa using P.mulDerivative.hasMap_X.1, ?_⟩
    have h := P.mulDerivative.hasMap_X.2
    simp only [mulDerivative_g, map_mul] at h
    exact isUnit_of_mul_isUnit_left h
  exact .ofAlgHom (P.mulDerivative.lift P.X h₁) (P.lift P.mulDerivative.X h₂)
    (by
      ext
      simp)
    (by
      ext
      simp)

/-- `P.Ring` as a standard etale presentation of itself. -/
def presentation (P : StandardEtalePair R) : StandardEtalePresentation R P.Ring where
  __ := P
  x := P.X
  hasMap := P.hasMap_X
  lift_bijective := by simpa [StandardEtalePair.lift_X_left] using Function.bijective_id

/-- The base change of the standard etale algebra of `P : StandardEtalePair R` along `R → T` is
the standard etale algebra of the pair obtained from `P` by mapping the coefficients to `T`. -/
def baseChangeEquiv (P : StandardEtalePair R) (T : Type*) [CommRing T] [Algebra R T] :
    T ⊗[R] P.Ring ≃ₐ[T] (P.map (algebraMap R T)).Ring :=
  P.presentation.baseChange.equivRing

/-- Every standard etale pair over a quotient `R ⧸ I` becomes, after passing to the associated
standard etale algebras, the base change of a standard etale pair over `R`. -/
theorem exists_algEquiv_quotient_tensor_ring (I : Ideal R) (P : StandardEtalePair (R ⧸ I)) :
    ∃ Q : StandardEtalePair R, Nonempty ((R ⧸ I) ⊗[R] Q.Ring ≃ₐ[R ⧸ I] P.Ring) := by
  obtain ⟨F, hF, -, hFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts (f := Ideal.Quotient.mk I) P.f).mpr
      (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective P.f)) P.monic_f
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective P.g
  refine ⟨ofMonic hFm G, ⟨((ofMonic hFm G).baseChangeEquiv (R ⧸ I)).trans ?_⟩⟩
  have h : (ofMonic hFm G).map (algebraMap R (R ⧸ I)) = P.mulDerivative := by
    rw [map_ofMonic]
    refine StandardEtalePair.ext ?_ ?_
    · simpa [Ideal.Quotient.algebraMap_eq] using hF
    · simp [Ideal.Quotient.algebraMap_eq, hF, hG]
  rw [h]
  exact P.mulDerivativeRingEquiv

/-- Every standard etale pair over `S` whose polynomials have coefficients in the image of an
`R`-algebra `S` is, after passing to the associated standard etale algebras, the base change of
a standard etale pair over `R`. -/
theorem exists_algEquiv_tensor_ring_of_coeffs_subset [Algebra R S] (P : StandardEtalePair S)
    (hf : ↑P.f.coeffs ⊆ Set.range (algebraMap R S))
    (hg : ↑P.g.coeffs ⊆ Set.range (algebraMap R S)) :
    ∃ Q : StandardEtalePair R, Nonempty (S ⊗[R] Q.Ring ≃ₐ[S] P.Ring) := by
  obtain ⟨F, hF, -, hFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.lifts_iff_coeffs_subset_range _).mpr hf) P.monic_f
  obtain ⟨G, hG⟩ := (Polynomial.lifts_iff_coeffs_subset_range _).mpr hg
  rw [Polynomial.coe_mapRingHom] at hG
  refine ⟨ofMonic hFm G, ⟨((ofMonic hFm G).baseChangeEquiv S).trans ?_⟩⟩
  have h : (ofMonic hFm G).map (algebraMap R S) = P.mulDerivative := by
    rw [map_ofMonic]
    exact StandardEtalePair.ext hF (by simp [hF, hG])
  rw [h]
  exact P.mulDerivativeRingEquiv

/-- **Standard etale algebras over an integral algebra descend to a finite subalgebra.** For a
finite family of standard etale pairs `P i` over an integral `A`-algebra `B` there is a
subalgebra `B'` of `B`, finite over `A`, such that each `(P i).Ring` is the base change of a
standard etale algebra over `B'`: take for `B'` the subalgebra generated by the coefficients
of the polynomials of the `P i`. -/
theorem exists_subalgebra_finite_algEquiv_tensor_ring {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] {ι : Type*}
    [Finite ι] (P : ι → StandardEtalePair B) :
    ∃ (B' : Subalgebra A B) (_ : Module.Finite A B') (Q : ι → StandardEtalePair B'),
      ∀ i, Nonempty (B ⊗[B'] (Q i).Ring ≃ₐ[B] (P i).Ring) := by
  classical
  have := Fintype.ofFinite ι
  let s : Finset B := Finset.univ.biUnion fun i ↦ (P i).f.coeffs ∪ (P i).g.coeffs
  let B' := Algebra.adjoin A (s : Set B)
  have : Algebra.FiniteType A B' :=
    (Subalgebra.fg_iff_finiteType B').mp (Subalgebra.fg_adjoin_finset s)
  have : Algebra.IsIntegral A B' := ⟨fun x ↦
    (isIntegral_algHom_iff B'.val Subtype.val_injective).mp (Algebra.IsIntegral.isIntegral _)⟩
  have hs (i : ι) (p : B[X]) (hp : p.coeffs ⊆ (P i).f.coeffs ∪ (P i).g.coeffs) :
      ↑p.coeffs ⊆ Set.range (algebraMap B' B) := by
    intro b hb
    refine ⟨⟨b, Algebra.subset_adjoin ?_⟩, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp hb⟩
  refine ⟨B', Algebra.IsIntegral.finite, fun i ↦ (exists_algEquiv_tensor_ring_of_coeffs_subset
    (P i) (hs i _ Finset.subset_union_left) (hs i _ Finset.subset_union_right)).choose,
    fun i ↦ (exists_algEquiv_tensor_ring_of_coeffs_subset
    (P i) (hs i _ Finset.subset_union_left) (hs i _ Finset.subset_union_right)).choose_spec⟩

/-- For `n ≠ 0` and `n`, `t` invertible in `R`, the pair `(Xⁿ - t, 1)` is a standard etale pair:
`Xⁿ - t` is monic, and `(t⁻¹ n⁻¹ X) · nXⁿ⁻¹ - t⁻¹ (Xⁿ - t) = 1`, so the derivative of `Xⁿ - t` is
invertible modulo `Xⁿ - t`. -/
@[simps]
def ofXPowSubC {n : ℕ} {t : R} (hn₀ : n ≠ 0) (hn : IsUnit (n : R)) (ht : IsUnit t) :
    StandardEtalePair R where
  f := X ^ n - C t
  monic_f := monic_X_pow_sub_C t hn₀
  g := 1
  cond := by
    obtain ⟨u, hu⟩ := hn
    obtain ⟨v, rfl⟩ := ht
    refine ⟨C (((u⁻¹ : Rˣ) : R) * ((v⁻¹ : Rˣ) : R)) * X, -C ((v⁻¹ : Rˣ) : R), 0, ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn₀
    have h₁ : C (u : R) = C ((m.succ : ℕ) : R) := by rw [hu]
    have h₂ : C ((u⁻¹ : Rˣ) : R) * C (u : R) = 1 := by rw [← C_mul]; simp
    have h₃ : C ((v⁻¹ : Rˣ) : R) * C (v : R) = 1 := by rw [← C_mul]; simp
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_zero, C_mul]
    rw [← h₁, Nat.succ_sub_one, pow_succ]
    linear_combination (X ^ (m + 1) * C ((v⁻¹ : Rˣ) : R)) * h₂ + h₃

/-- The standard etale algebra of the pair `(Xⁿ - t, 1)` is the Kummer algebra
`R[X]/(Xⁿ - t)`. -/
def ofXPowSubCRingEquiv {n : ℕ} {t : R} (hn₀ : n ≠ 0) (hn : IsUnit (n : R)) (ht : IsUnit t) :
    (ofXPowSubC hn₀ hn ht).Ring ≃ₐ[R] AdjoinRoot (X ^ n - C t) :=
  .ofAlgHom
    ((ofXPowSubC hn₀ hn ht).lift (AdjoinRoot.root _)
      ⟨by rw [ofXPowSubC_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], by simp⟩)
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (ofXPowSubC hn₀ hn ht).X hasMap_X.1)
    (AdjoinRoot.algHom_ext (by simp [AdjoinRoot.liftAlgHom_root]))
    (hom_ext (by simp [AdjoinRoot.liftAlgHom_root]))

section IsReduced

/-- Let `P = (f, g)` be a standard etale pair over a reduced ring `R`, and `a ∈ R[X]/f`. If
`gʲ aᵐ = 0` in `R[X]/f`, then already `gⁿ a = 0` with `n = deg f`; in other words, the kernel of
`R[X]/f ⟶ (R[X]/f)[1/g]` contains every nilpotent class and is killed by `gⁿ`.

Over each minimal prime `p` of `R` the localisation `R_p` is a field, over which
`(R_p[X]/f)[1/g]` is etale, hence reduced; so `gᵏ a = 0` in the `n`-dimensional `R_p`-vector
space `R_p[X]/f` for some `k`, hence for `k = n`. The remainder of `gⁿ a` modulo the monic `f`
therefore has all its coefficients in every minimal prime of `R`, which intersect to `0`. -/
theorem mk_g_pow_natDegree_mul_eq_zero [IsReduced R] (P : StandardEtalePair R)
    (a : AdjoinRoot P.f) (j m : ℕ) (h : AdjoinRoot.mk P.f P.g ^ j * a ^ m = 0) :
    AdjoinRoot.mk P.f P.g ^ P.f.natDegree * a = 0 := by
  set s := AdjoinRoot.mk P.f P.g
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective (s ^ P.f.natDegree * a)
  have hr : AdjoinRoot.mk P.f (q %ₘ P.f) = s ^ P.f.natDegree * a := by
    rw [← hq, AdjoinRoot.mk_eq_mk]
    exact ⟨-(q /ₘ P.f), by linear_combination (exp := 1) modByMonic_add_div q P.f⟩
  rw [← hr]
  suffices q %ₘ P.f = 0 by rw [this, map_zero]
  ext i
  rw [coeff_zero, ← Ideal.mem_bot, ← Ideal.radical_bot_of_isReduced, ← Ideal.sInf_minimalPrimes]
  refine Submodule.mem_sInf.2 fun (p : Ideal R) hp ↦ ?_
  have : p.IsPrime := hp.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := .of_isLocalization _ hp _
  let : Field (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced.toField
  let K := Localization.AtPrime p
  let φ := algebraMap R K
  let Q := P.map φ
  have hred : IsReduced (Localization.Away (AdjoinRoot.mk Q.f Q.g)) := by
    have : IsReduced Q.Ring := Algebra.FormallyUnramified.isReduced_of_field K _
    exact isReduced_of_injective Q.equivAwayAdjoinRoot.symm.toRingHom
      Q.equivAwayAdjoinRoot.symm.injective
  let ψ := AdjoinRoot.map φ P.f Q.f dvd_rfl
  have hψ (r : R[X]) : ψ (AdjoinRoot.mk P.f r) = AdjoinRoot.mk Q.f (r.map φ) := by
    conv_rhs => rw [← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]
    simp [ψ, AdjoinRoot.map, AdjoinRoot.lift_mk, AdjoinRoot.algebraMap_eq]
  have hψs : ψ s = AdjoinRoot.mk Q.f Q.g := hψ _
  have hψa : AdjoinRoot.mk Q.f Q.g ^ j * ψ a ^ m = 0 := by
    have := congrArg ψ h
    rwa [map_mul, map_pow, map_pow, hψs, map_zero] at this
  -- In `(R_p[X]/f)[1/g]`, which is reduced, the image of `ψ a` is nilpotent, hence zero.
  obtain ⟨⟨_, k, rfl⟩, hk⟩ : ∃ t : Submonoid.powers (AdjoinRoot.mk Q.f Q.g), t.1 * ψ a = 0 := by
    let L := Localization.Away (AdjoinRoot.mk Q.f Q.g)
    have hu : IsUnit (algebraMap _ L (AdjoinRoot.mk Q.f Q.g)) :=
      IsLocalization.Away.algebraMap_isUnit _
    have : IsNilpotent (algebraMap _ L (ψ a)) := by
      refine ⟨m, ?_⟩
      have := congrArg (algebraMap _ L) hψa
      rw [map_mul, map_pow, map_pow, map_zero] at this
      exact (hu.pow j).mul_right_eq_zero.1 this
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (AdjoinRoot.mk Q.f Q.g)) L _).1 this.eq_zero
    exact ⟨t, ht⟩
  -- The kernels of the powers of multiplication by `g` stabilise by `n = dim R_p[X]/f`.
  have hn : AdjoinRoot.mk Q.f Q.g ^ P.f.natDegree * ψ a = 0 := by
    let pb := AdjoinRoot.powerBasis' Q.monic_f
    have : Module.Finite K (AdjoinRoot Q.f) := pb.finite
    have hfr : Module.finrank K (AdjoinRoot Q.f) = P.f.natDegree := by
      rw [pb.finrank]
      simp [pb, Q, P.monic_f.natDegree_map]
    let T : Module.End K (AdjoinRoot Q.f) := LinearMap.mulLeft K (AdjoinRoot.mk Q.f Q.g)
    have hT (l : ℕ) (x : AdjoinRoot Q.f) : (T ^ l) x = AdjoinRoot.mk Q.f Q.g ^ l * x := by
      induction l generalizing x with
      | zero => simp
      | succ l ih => rw [pow_succ, Module.End.mul_apply, ih]; simp [T, pow_succ, mul_assoc]
    have hmem : ψ a ∈ LinearMap.ker (T ^ k) := by simpa [hT] using hk
    simpa [hT, hfr] using Module.End.ker_pow_le_ker_pow_finrank T k hmem
  have hmap : Q.f ∣ (q %ₘ P.f).map φ := by
    rw [← AdjoinRoot.mk_eq_zero, ← hψ, hr, map_mul, map_pow, hψs, hn]
  have : Nontrivial R := φ.domain_nontrivial
  have hzero : (q %ₘ P.f).map φ = 0 := by
    by_contra hne
    refine absurd (Polynomial.degree_le_of_dvd hmap hne) (not_le.2 ?_)
    calc ((q %ₘ P.f).map φ).degree ≤ (q %ₘ P.f).degree := degree_map_le
      _ < P.f.degree := degree_modByMonic_lt _ P.monic_f
      _ = Q.f.degree := (P.monic_f.degree_map φ).symm
  have hc : φ ((q %ₘ P.f).coeff i) = 0 := by
    rw [← coeff_map, hzero, coeff_zero]
  obtain ⟨⟨t, ht⟩, hct⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl K _).1 hc
  exact (‹p.IsPrime›.mem_or_mem_of_mul_eq_zero hct).resolve_left ht

/-- A standard etale algebra `R[X][Y]/⟨f, Yg - 1⟩ = (R[X]/f)[1/g]` over a reduced ring `R` is
reduced: a nilpotent fraction `a / gᵏ` has `gʲ aᵐ = 0`, hence `gⁿ a = 0` by
`StandardEtalePair.mk_g_pow_natDegree_mul_eq_zero`. -/
instance isReduced_ring [IsReduced R] (P : StandardEtalePair R) : IsReduced P.Ring := by
  let s := AdjoinRoot.mk P.f P.g
  suffices IsReduced (Localization.Away s) from
    isReduced_of_injective P.equivAwayAdjoinRoot.toRingHom P.equivAwayAdjoinRoot.injective
  refine ⟨fun z ⟨m, hm⟩ ↦ ?_⟩
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) z
  rw [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_zero_iff] at hm
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := hm
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨_, P.f.natDegree, rfl⟩, P.mk_g_pow_natDegree_mul_eq_zero a j m hj⟩

end IsReduced

/-- **Maps out of a standard étale algebra.** Let `P = (f, g)` be a standard étale pair over `R`,
with standard étale algebra `P.Ring = R[X][Y] ⧸ (f, Yg - 1)` and `x = P.X` the class of `X`, and
let `L` be an `R`-algebra. Then
1. for every `b : L` with `f(b) = 0` and `g(b)` a unit there is exactly one `R`-algebra map
   `χ : P.Ring → L` with `χ x = b`;
2. every `R`-algebra map `χ : P.Ring → L` satisfies `f(χ x) = 0` and `g(χ x)` is a unit, and is
   determined by `χ x`.
This is mathlib's `StandardEtalePair.homEquiv`.
(blueprint: `lem-weil-pbc-standard-etale-pair-maps`) -/
@[stacks 00UB]
theorem existsUnique_algHom_and_hasMap {R : Type*} [CommRing R] (P : StandardEtalePair R)
    (L : Type*) [CommRing L] [Algebra R L] :
    (∀ b : L, P.HasMap b → ∃! χ : P.Ring →ₐ[R] L, χ P.X = b) ∧
      ∀ χ : P.Ring →ₐ[R] L, P.HasMap (χ P.X) ∧
        ∀ χ' : P.Ring →ₐ[R] L, χ' P.X = χ P.X → χ' = χ :=
  ⟨fun b hb ↦ ⟨P.lift b hb, P.lift_X b hb, fun _ h ↦ P.hom_ext (by simpa using h)⟩,
    fun χ ↦ ⟨(P.homEquiv χ).2, fun _ h ↦ P.hom_ext h⟩⟩

end StandardEtalePair

/-- **The Kummer algebra is etale.** For `n ≠ 0` and `n`, `t` invertible in `R`, the algebra
`R[X]/(Xⁿ - t)` is etale over `R`: it is the standard etale algebra of the pair `(Xⁿ - t, 1)`,
the derivative `nXⁿ⁻¹` of `Xⁿ - t` being invertible modulo `Xⁿ - t`.

This is the unramifiedness step of the proof of exactness of the Kummer sequence
(blueprint: `proposition-smooth-proper-curves-torsion-prime`). -/
theorem AdjoinRoot.etale_X_pow_sub_C {n : ℕ} {t : R} (hn₀ : n ≠ 0) (hn : IsUnit (n : R))
    (ht : IsUnit t) : Algebra.Etale R (AdjoinRoot (X ^ n - C t)) :=
  Algebra.Etale.of_equiv (StandardEtalePair.ofXPowSubCRingEquiv hn₀ hn ht)

variable (S) in
/-- Blueprint `lemma-openclosed-standard-etale-lift`: Lifting a standard étale algebra along a
quotient. Every standard etale algebra over a quotient `R ⧸ I` is the base change of a standard
etale algebra over `R`. -/
theorem Algebra.IsStandardEtale.exists_algEquiv_quotient_tensor (I : Ideal R)
    [Algebra (R ⧸ I) S] [Algebra.IsStandardEtale (R ⧸ I) S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Algebra.IsStandardEtale R T ∧ Nonempty ((R ⧸ I) ⊗[R] T ≃ₐ[R ⧸ I] S) := by
  obtain ⟨P⟩ := ‹Algebra.IsStandardEtale (R ⧸ I) S›.nonempty_standardEtalePresentation
  obtain ⟨Q, ⟨e⟩⟩ := StandardEtalePair.exists_algEquiv_quotient_tensor_ring I P.P
  exact ⟨Q.Ring, inferInstance, inferInstance, inferInstance, ⟨e.trans P.equivRing.symm⟩⟩

end

/-!
# The polynomial map `z ↦ P(x)`

Let `P ∈ R[X]` be monic of positive degree and let `φ : R[z] ⟶ R[X]`, `z ↦ P`, be the
`R`-algebra map, with `R[z] = MvPolynomial PUnit R`. Then `R[X] = R[z][Y] / (P(Y) - z)`, so

- `φ` is finite (`Polynomial.Monic.finite_aeval_pUnit`): `X` is a root of the monic polynomial
  `P(Y) - z` over `R[z]`;
- `φ` is étale away from the zeros of `P'` (`Polynomial.Monic.etale_aeval_pUnit`): the
  localization `R[X][1/P']` is the standard étale `R[z]`-algebra `R[z][Y][1/P'(Y)] / (P(Y) - z)`.
-/

@[expose] public section

open Polynomial


namespace Polynomial

variable {R : Type u} [CommRing R]

/-- The polynomial `P(Y) - z` over `R[z] = MvPolynomial PUnit R`: its roots in an `R[z]`-algebra
are the preimages of `z` under the polynomial map `x ↦ P(x)`. -/
noncomputable def subPUnitX (P : R[X]) : (MvPolynomial PUnit.{u + 1} R)[X] :=
  P.map MvPolynomial.C - C (MvPolynomial.X PUnit.unit)

lemma monic_subPUnitX {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    (subPUnitX P).Monic := by
  have : Nontrivial R := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    simp [Subsingleton.elim P 0] at hdeg
  refine (hP.map _).sub_of_left (degree_C_le.trans_lt ?_)
  rw [degree_map_eq_of_leadingCoeff_ne_zero _ (by simp [hP.leadingCoeff])]
  exact natDegree_pos_iff_degree_pos.mp hdeg

lemma aeval_subPUnitX (P : R[X]) {S : Type*} [CommRing S]
    [Algebra (MvPolynomial PUnit.{u + 1} R) S] (x : S) :
    aeval x (subPUnitX P) =
      eval₂ ((algebraMap (MvPolynomial PUnit.{u + 1} R) S).comp
        (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R))) x P -
        algebraMap (MvPolynomial PUnit.{u + 1} R) S (MvPolynomial.X PUnit.unit) := by
  simp [subPUnitX, aeval_def, eval₂_map]

variable (P : R[X])

/-- If `P` is monic of positive degree, then `R[z] ⟶ R[X]`, `z ↦ P`, is finite. -/
theorem Monic.finite_aeval_pUnit (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    (MvPolynomial.aeval (R := R) fun _ : PUnit.{u + 1} ↦ P).toRingHom.Finite := by
  let _ : Algebra (MvPolynomial PUnit.{u + 1} R) R[X] :=
    (MvPolynomial.aeval fun _ : PUnit.{u + 1} ↦ P).toRingHom.toAlgebra
  have hC : (algebraMap (MvPolynomial PUnit.{u + 1} R) R[X]).comp
      (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R)) = C := by
    ext r
    simp [RingHom.algebraMap_toAlgebra]
  have hX : IsIntegral (MvPolynomial PUnit.{u + 1} R) (X : R[X]) := by
    refine ⟨subPUnitX P, monic_subPUnitX hP hdeg, ?_⟩
    rw [← aeval_def, aeval_subPUnitX, hC, eval₂_C_X]
    simp [RingHom.algebraMap_toAlgebra]
  have hadj : Algebra.adjoin (MvPolynomial PUnit.{u + 1} R) {(X : R[X])} = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    induction a using Polynomial.induction_on with
    | C r =>
      rw [← hC]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => exact add_mem hp hq
    | monomial n r _ =>
      rw [← hC]
      exact mul_mem (Subalgebra.algebraMap_mem _ _)
        (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) _)
  have : Module.Finite (MvPolynomial PUnit.{u + 1} R) R[X] := ⟨by
    rw [← Algebra.top_toSubmodule, ← hadj]
    exact hX.fg_adjoin_singleton⟩
  exact this

/-- If `P` is monic of positive degree, then `R[z] ⟶ R[X][1/P']`, `z ↦ P`, is étale: the
target is the standard étale algebra `R[z][Y][1/P'(Y)] / (P(Y) - z)`. -/
theorem Monic.etale_aeval_pUnit (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    ((algebraMap R[X] (Localization.Away (derivative P))).comp
      (MvPolynomial.aeval (R := R) fun _ : PUnit.{u + 1} ↦ P).toRingHom).Etale := by
  let _ : Algebra (MvPolynomial PUnit.{u + 1} R) R[X] :=
    (MvPolynomial.aeval fun _ : PUnit.{u + 1} ↦ P).toRingHom.toAlgebra
  set B := MvPolynomial PUnit.{u + 1} R
  set L := Localization.Away (derivative P)
  have hC : (algebraMap B R[X]).comp (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R)) = C := by
    ext r
    simp [B, RingHom.algebraMap_toAlgebra]
  have hXP : algebraMap B R[X] (MvPolynomial.X PUnit.unit) = P := by
    simp [B, RingHom.algebraMap_toAlgebra]
  have hBL : (algebraMap B L).comp (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R)) =
      (algebraMap R[X] L).comp C := by
    rw [IsScalarTower.algebraMap_eq B R[X] L, RingHom.comp_assoc, hC]
  have hBL' : (algebraMap R[X] L).comp
      (MvPolynomial.aeval (R := R) fun _ : PUnit.{u + 1} ↦ P).toRingHom = algebraMap B L :=
    (IsScalarTower.algebraMap_eq B R[X] L).symm
  rw [hBL', RingHom.etale_algebraMap]
  let Q : StandardEtalePair B :=
    ⟨subPUnitX P, monic_subPUnitX hP hdeg, derivative (subPUnitX P), 1, 0, 1, by simp⟩
  have hg : Q.g = (derivative P).map (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R)) := by
    dsimp only [Q]
    rw [subPUnitX, derivative_sub, derivative_map, derivative_C, sub_zero]
  set x : L := algebraMap R[X] L X
  have hx : Q.HasMap x := by
    refine ⟨?_, ?_⟩
    · rw [aeval_subPUnitX, hBL, ← hom_eval₂, eval₂_C_X, IsScalarTower.algebraMap_apply B R[X] L,
        hXP, sub_self]
    · rw [hg, aeval_def, eval₂_map, hBL, ← hom_eval₂, eval₂_C_X]
      exact IsLocalization.Away.algebraMap_isUnit _
  -- the inverse `R[X][1/P'] ⟶ R[z][Y][1/P'(Y)] / (P(Y) - z)`, `X ↦ Y`
  set c := (algebraMap B Q.Ring).comp (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R))
  let σ : R[X] →+* Q.Ring := eval₂RingHom c Q.X
  have hσ : IsUnit (σ (derivative P)) := by
    have h := Q.hasMap_X.2
    rwa [hg, aeval_def, eval₂_map] at h
  let τ : L →+* Q.Ring := IsLocalization.Away.lift (derivative P) hσ
  have hτ (p : R[X]) : τ (algebraMap R[X] L p) = σ p := IsLocalization.lift_eq _ _
  have hτB : τ.comp (algebraMap B L) = algebraMap B Q.Ring := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun _ ↦ ?_)
    · rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply B R[X] L, hτ]
      simp [σ, c, B, RingHom.algebraMap_toAlgebra]
    · have h := Q.hasMap_X.1
      rw [aeval_subPUnitX, sub_eq_zero] at h
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply B R[X] L, hXP, hτ]
      exact h
  let τA : L →ₐ[B] Q.Ring := { τ with commutes' := fun b ↦ congr($hτB b) }
  have hτA (p : R[X]) : τA (algebraMap R[X] L p) = σ p := hτ p
  refine Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom (Q.lift x hx) τA ?_ ?_)
  · refine AlgHom.toRingHom_injective (IsLocalization.ringHom_ext (Submonoid.powers
      (derivative P)) (Polynomial.ringHom_ext (fun r ↦ ?_) ?_))
    · simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.comp_apply, AlgHom.id_apply]
      rw [hτA]
      simp only [σ, c, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply, AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply B R[X] L]
      simp [B, RingHom.algebraMap_toAlgebra]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.comp_apply, AlgHom.id_apply]
      rw [hτA]
      simp [σ]
      rfl
  · refine StandardEtalePair.hom_ext ?_
    rw [AlgHom.comp_apply, StandardEtalePair.lift_X, hτA]
    simp [σ]

end Polynomial
