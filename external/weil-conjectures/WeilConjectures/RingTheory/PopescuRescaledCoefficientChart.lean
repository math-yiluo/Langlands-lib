/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs
import WeilConjectures.RingTheory.PopescuUnpaddedCoefficientChart
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Simultaneous rescaling of an existing Artinian coefficient chart

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, steps 10--13, 15, 23 and 25.
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

private theorem span_range_pow_le {B : Type*} [CommRing B]
    (d : ℕ) (b : Fin d → B) (e : ℕ) :
    Ideal.span (Set.range b) ^ (d * e + 1) ≤
      Ideal.span (Set.range (fun i ↦ b i ^ e)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.range_fin_succ, Ideal.span_insert]
    have hsplit : (d + 1) * e + 1 = e + (d * e + 1) := by
      simp [Nat.add_mul, Nat.add_comm, Nat.add_assoc]
    rw [hsplit]
    apply (Ideal.sup_pow_add_le_pow_sup_pow).trans
    apply sup_le
    · rw [Ideal.span_singleton_pow]
      exact Ideal.span_mono (by
        intro x hx
        rcases hx with rfl
        exact ⟨0, rfl⟩)
    · exact (ih (Fin.tail b)).trans (Ideal.span_mono (by
        rintro x ⟨i, rfl⟩
        exact ⟨i.succ, rfl⟩))

private theorem span_range_pow_le_of_bound {B : Type*} [CommRing B]
    (d : ℕ) (b : Fin d → B) (e n : ℕ) (hn : d * e + 1 ≤ n) :
    Ideal.span (Set.range b) ^ n ≤ Ideal.span (Set.range (fun i ↦ b i ^ e)) :=
  (Ideal.pow_le_pow_right hn).trans (span_range_pow_le d b e)

private theorem padded_previous_span {B : Type*} [CommRing B]
    {d : ℕ} (b : Fin d → B) (e : ℕ) (i : Fin d) :
    Ideal.span {y | ∃ j : Fin (d + 1), j.val < i.castSucc.val ∧
      y = (Fin.lastCases 0 b j) ^ e} =
    Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧ y = b j ^ e} := by
  congr 1
  ext y
  constructor
  · rintro ⟨j, hj, hy⟩
    cases j using Fin.lastCases with
    | last => simp only [Fin.val_last, Fin.val_castSucc] at hj; omega
    | cast j => exact ⟨j, hj, by simpa using hy⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.castSucc, hj, by simp⟩

private theorem mapped_padded_previous_span {B C : Type*} [CommRing B] [CommRing C]
    [Algebra B C] {d : ℕ} (b : Fin d → B) (e : ℕ) (i : Fin d) :
    Ideal.span {y | ∃ j : Fin (d + 1), j.val < i.castSucc.val ∧
      y = algebraMap B C (Fin.lastCases 0 b j) ^ e} =
    Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧ y = algebraMap B C (b j) ^ e} := by
  congr 1
  ext y
  constructor
  · rintro ⟨j, hj, hy⟩
    cases j using Fin.lastCases with
    | last => simp only [Fin.val_last, Fin.val_castSucc] at hj; omega
    | cast j => exact ⟨j, hj, by simpa using hy⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.castSucc, hj, by simp⟩

private theorem padded_span_pow {B : Type*} [CommRing B]
    {d : ℕ} (b : Fin d → B) (e : ℕ) (he : 0 < e) :
    Ideal.span (Set.range (fun i : Fin (d + 1) ↦ (Fin.lastCases 0 b i) ^ e)) =
      Ideal.span (Set.range (fun i : Fin d ↦ b i ^ e)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨i, rfl⟩
    cases i using Fin.lastCases with
    | last => simp [zero_pow (Nat.ne_of_gt he)]
    | cast i => exact Ideal.subset_span ⟨i, by simp⟩
  · apply Ideal.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i.castSucc, by simp⟩

/-- Rescale a given flat polynomial chart and its Artinian coefficient solution.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, steps 10--13, 15, 23 and 25.
(blueprint: lem-weil-pbc-popescu-rescaled-coefficient-chart).

Proof: Use the unpadded coefficient-chart construction for the simultaneous rescaling
and coefficient inclusion. It supplies d parameters rho, an ideal H extending the
initial contracted prime, and the coefficient algebra over R/H^(N+d(8c)). The
parameters generate HQ and the image of H in L is its maximal ideal.

Append zero using Fin.lastCases. For every old index the preceding-parameter ideal
is unchanged, so both kernel equalities transfer along equality of the quotient
ideals. For the last index, multiplication by zero and by its square have equal
kernels. The powered parameter span is unchanged since c*8 is positive.

For any d elements b and exponent e, their span to the power d*e+1 is contained in
the span of their e-th powers. Prove this by induction on d: split off b_0, apply
(I+J)^(e+d*e+1) ≤ I^e+J^(d*e+1), and use the singleton-span power identity and
the induction hypothesis. The empty family gives the zero ideal to a positive
power. As N>0, n=N+d(8c) is at least d*(c*8)+1. Apply the bound in Q and L, with
I₀=H^n and K=m_L^n. Ideal maps commute with powers and the two localized
structural maps agree by the scalar towers. Thus I₀Q⊆JQ, K⊆JL and I₀L=K.
Take the same n as the positive maximal-ideal-power witness and retain the
coefficient algebra, smoothness, flat local map and evaluation equalities. -/
theorem exists_popescu_rescaled_coefficient_chart
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (N : ℕ) (hN : 0 < N)
    (hpower : IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ N ≤
      (Ideal.map α.toRingHom (singularIdeal k A)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal)))
    (d : ℕ) (hd : d =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank)
    (s : ℕ) (a : Fin s → A) (ha : Ideal.span (Set.range a) = singularIdeal k A)
    (c : ℕ) (hc : 0 < c)
    (r : ℕ) (f : MvPolynomial (Fin r) k →ₐ[k] A) (hf : Function.Surjective f)
    (m₀ : ℕ) (φ₀ : MvPolynomial (Fin m₀) k →ₐ[k] Λ)
    (ψ₀ : Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) →+*
      Localization.AtPrime q.asIdeal)
    (hψ₀ : ψ₀.comp (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom)
    (hideal₀ : q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) =
      (q.asIdeal.comap φ₀.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom))
    (hflat₀ : ψ₀.Flat)
    (D₀ : Type (max u w)) [CommRing D₀] [IsLocalRing D₀] [IsArtinianRing D₀]
    [Algebra (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^ (N + d * (8 * c))) D₀]
    (g₀ : D₀ →+* Localization.AtPrime q.asIdeal ⧸
      (q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        (N + d * (8 * c)))
    [IsLocalHom (algebraMap (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
          (N + d * (8 * c))) D₀)]
    [IsLocalHom g₀]
    (hsmooth₀ : EssentiallySmooth
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c))) D₀)
    (hgflat₀ : g₀.Flat)
    (hfactor₀ : (g₀.comp (algebraMap
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c))) D₀)).comp
      (Ideal.Quotient.mk (((q.asIdeal.comap φ₀.toRingHom).map
        (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c)))) =
      (Ideal.Quotient.mk ((q.asIdeal.map
        (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
          (N + d * (8 * c)))).comp ψ₀)
    (hinc₀ : ∀ i : Fin r, Ideal.Quotient.mk
      ((q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        (N + d * (8 * c)))
      (algebraMap Λ (Localization.AtPrime q.asIdeal) (α (f (MvPolynomial.X i)))) ∈
        Set.range g₀) :
    let S := MvPolynomial (Fin d) k
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (_ : Algebra S (MvPolynomial (Fin m) k))
      (_ : IsScalarTower k S (MvPolynomial (Fin m) k))
      (_ : Algebra S Λ) (_ : IsScalarTower S (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k S Λ)
      (ell : Fin d × Fin s → Λ) (π : Fin (d + 1) → MvPolynomial (Fin m) k),
      (∀ i, algebraMap S Λ (MvPolynomial.X i) ^ (2 * N) =
        ∑ j : Fin s, ell (i, j) * α (a j)) ∧
      (∀ i, π i = 0 ∨ ∃ j : Fin d,
        π i = algebraMap S (MvPolynomial (Fin m) k) (MvPolynomial.X j)) ∧
      (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
      (∀ (i : Fin (d + 1))
        (x : MvPolynomial (Fin m) k ⧸ Ideal.span
          {y | ∃ j : Fin (d + 1), j.val < i.val ∧ y = π j ^ (c * 8)}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ (i : Fin (d + 1))
        (x : Λ ⧸ Ideal.span
          {y | ∃ j : Fin (d + 1), j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ (c * 8)}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin (d + 1) ↦ π i ^ (c * 8)))
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let JQ := J.map (algebraMap R Q)
    let JL := (J.map (algebraMap R Λ)).map (algebraMap Λ L)
    ∃ (n : ℕ), 0 < n ∧ IsLocalRing.maximalIdeal L ^ n ≤ JL ∧
      ∃ (I₀ : Ideal R) (K : Ideal L),
        I₀.map (algebraMap R Q) ≤ JQ ∧ K ≤ JL ∧
        (I₀.map (algebraMap R Q)).map (algebraMap Q L) ≤ K ∧
        ∃ (D' : Type (max u v)) (_ : CommRing D')
          (_ : IsLocalRing D') (_ : IsArtinianRing D') (_ : Algebra k D'),
          let E := MvPolynomial (Fin d) D'
          ∃ (_ : Algebra R E) (_ : Algebra (R ⧸ I₀) E)
            (_ : IsScalarTower R (R ⧸ I₀) E)
            (algSE : Algebra S E) (_ : IsScalarTower S R E)
            (_ : Algebra k E) (_ : IsScalarTower k S E),
            EssentiallySmooth (R ⧸ I₀) E ∧
            ∃ (_ : IsScalarTower k D' E)
              (f₀ : A →ₐ[k] D') (g : D' →+* L ⧸ K)
              (u₀ : Fin d → D') (δ : Fin d → D'ˣ) (coeff : Fin d × Fin s → D'),
              IsLocalRing (L ⧸ K) ∧ IsLocalHom g ∧ g.Flat ∧
              (∀ i : Fin d, @algebraMap S E _ _ algSE (MvPolynomial.X (R := k) i) =
                MvPolynomial.C (σ := Fin d) (u₀ i) * MvPolynomial.X (R := D') i) ∧
              (∀ z : R, MvPolynomial.eval₂Hom g (fun i ↦ g (δ i : D'))
                (algebraMap R E z) =
                Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ z))) ∧
              (∀ x, g (f₀ x) =
                Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
              (∀ ij, g (coeff ij) =
                Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by
  obtain ⟨m, algRΛ, towerkRΛ, algSR, towerkSR, algSΛ, towerSRΛ, towerkSΛ,
    ell, rho, hrho, heq, hmem, hkerR, hkerΛ, H, hHQ, hHL, hcoeff⟩ :=
    exists_popescu_unpadded_coefficient_chart p hp α q hreg N hN hpower d hd s a ha c hc
      r f hf m₀ φ₀ ψ₀ hψ₀ hideal₀ hflat₀ D₀ g₀ hsmooth₀ hgflat₀ hfactor₀ hinc₀
  let S := MvPolynomial (Fin d) k
  let R := MvPolynomial (Fin m) k
  let : Algebra R Λ := algRΛ
  have : IsScalarTower k R Λ := towerkRΛ
  let : Algebra S R := algSR
  have : IsScalarTower k S R := towerkSR
  let : Algebra S Λ := algSΛ
  have : IsScalarTower S R Λ := towerSRΛ
  have : IsScalarTower k S Λ := towerkSΛ
  let π : Fin (d + 1) → R := Fin.lastCases 0 rho
  have he : 0 < c * 8 := Nat.mul_pos hc (by decide)
  refine ⟨m, algRΛ, towerkRΛ, algSR, towerkSR, algSΛ, towerSRΛ, towerkSΛ,
    ell, π, heq, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.lastCases with
    | last => exact Or.inl (by simp [π])
    | cast i => exact Or.inr ⟨i, by simp [π, hrho]⟩
  · intro i
    cases i using Fin.lastCases with
    | last => simp [π]
    | cast i => simpa [π] using hmem i
  · intro i
    cases i using Fin.lastCases with
    | last => intro x; simp [π]
    | cast i =>
      dsimp only [π, Fin.lastCases_castSucc]
      rw [padded_previous_span]
      simpa only [Fin.lastCases_castSucc] using hkerR i
  · intro i
    cases i using Fin.lastCases with
    | last => intro x; simp [π]
    | cast i =>
      dsimp only [π]
      rw [mapped_padded_previous_span]
      simpa only [Fin.lastCases_castSucc] using hkerΛ i
  · let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    let : Algebra Q L :=
      Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let J := Ideal.span (Set.range (fun i ↦ π i ^ (c * 8)))
    let n := N + d * (8 * c)
    let I₀ := H ^ n
    let K := IsLocalRing.maximalIdeal L ^ n
    have hn : 0 < n := by dsimp [n]; omega
    have hbound : d * (c * 8) + 1 ≤ n := by dsimp [n]; rw [Nat.mul_comm c 8]; omega
    have hJQ : J.map (algebraMap R Q) =
        Ideal.span (Set.range (fun i : Fin d ↦ algebraMap R Q (rho i) ^ (c * 8))) := by
      rw [show J = Ideal.span (Set.range (fun i : Fin d ↦ rho i ^ (c * 8))) from
        padded_span_pow rho (c * 8) he, Ideal.map_span]
      congr 1
      ext x
      simp [Set.mem_image, Set.mem_range, map_pow]
    have hJL : (J.map (algebraMap R Λ)).map (algebraMap Λ L) =
        Ideal.span (Set.range (fun i : Fin d ↦
          algebraMap Λ L (algebraMap R Λ (rho i)) ^ (c * 8))) := by
      rw [show J = Ideal.span (Set.range (fun i : Fin d ↦ rho i ^ (c * 8))) from
        padded_span_pow rho (c * 8) he, Ideal.map_map, Ideal.map_span]
      congr 1
      ext x
      simp [Set.mem_image, Set.mem_range, map_pow, RingHom.comp_apply]
    have hI₀Q : I₀.map (algebraMap R Q) ≤ J.map (algebraMap R Q) := by
      rw [show I₀ = H ^ n from rfl, Ideal.map_pow, hHQ, hJQ]
      exact span_range_pow_le_of_bound d _ (c * 8) n hbound
    have hcomp : (algebraMap Q L).comp (algebraMap R Q) =
        (algebraMap Λ L).comp (algebraMap R Λ) := by
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    have hspanL : Ideal.span (Set.range (fun i : Fin d ↦
        algebraMap Λ L (algebraMap R Λ (rho i)))) = IsLocalRing.maximalIdeal L := by
      have h := congrArg (fun I : Ideal Q ↦ I.map (algebraMap Q L)) hHQ
      rw [Ideal.map_map, hcomp, hHL, Ideal.map_span, ← Set.range_comp] at h
      change IsLocalRing.maximalIdeal L = Ideal.span
        (Set.range (fun i : Fin d ↦ algebraMap Q L (algebraMap R Q (rho i)))) at h
      simpa only [← IsScalarTower.algebraMap_apply R Q L,
        ← IsScalarTower.algebraMap_apply R Λ L] using h.symm
    have hKL : K ≤ (J.map (algebraMap R Λ)).map (algebraMap Λ L) := by
      rw [show K = IsLocalRing.maximalIdeal L ^ n from rfl, hJL, ← hspanL]
      exact span_range_pow_le_of_bound d _ (c * 8) n hbound
    have hI₀L : (I₀.map (algebraMap R Q)).map (algebraMap Q L) ≤ K := by
      rw [Ideal.map_map, hcomp, show I₀ = H ^ n from rfl, Ideal.map_pow, hHL]
    exact ⟨n, hn, hKL, I₀, K, hI₀Q, hKL, hI₀L, hcoeff⟩

end Algebra
