/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.RingTheory.ArtinianCoefficientEnlargement
import WeilConjectures.RingTheory.EssentiallySmoothComp
import WeilConjectures.RingTheory.RegularSequencePowers
import WeilConjectures.AlgebraicGeometry.Ogoma
import WeilConjectures.RingTheory.PopescuLocalizedCoefficientRelation
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.CharP.Algebra

/-!
# One coefficient rescaling step

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, justification of step 13.
(blueprint: lem-weil-pbc-popescu-coefficient-step).
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

open RingTheory.Sequence in
open scoped Pointwise in
private theorem regular_ofFn_mul_units
    {R : Type v} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {d : ℕ} (f s : Fin d → R) (hs : ∀ i, IsUnit (s i))
    (h : IsRegular M (List.ofFn f)) :
    IsRegular M (List.ofFn (fun i ↦ s i * f i)) := by
  induction d generalizing M with
  | zero => simpa using h
  | succ d ih =>
    rw [List.ofFn_succ, isRegular_cons_iff] at h ⊢
    refine ⟨((hs 0).isSMulRegular M).mul h.1, ?_⟩
    have heq : (s 0 * f 0) • (⊤ : Submodule R M) = f 0 • ⊤ := by
      rw [← Submodule.ideal_span_singleton_smul,
        Ideal.span_singleton_mul_left_unit (hs 0), Submodule.ideal_span_singleton_smul]
    let E := Submodule.quotEquivOfEq _ _ heq
    apply (E.isRegular_congr _).mpr
    exact ih (fun i ↦ f i.succ) (fun i ↦ s i.succ) (fun i ↦ hs i.succ) h.2

private theorem ofList_take_ofFn
    {R : Type v} [CommRing R] {d : ℕ} (f : Fin d → R) (i : Fin d) :
    Ideal.ofList ((List.ofFn f).take i.val) =
      Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧ y = f j} := by
  apply congrArg Ideal.span
  ext y
  simp only [Set.mem_ofPred_eq, List.mem_take_iff_getElem, List.length_ofFn,
    Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨⟨j, hj.trans i.isLt⟩, hj, by simpa using h.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.val, hj, by simp⟩

private theorem localized_kernel_eq
    {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
    (q : PrimeSpectrum Λ) (d e : ℕ) (he : 0 < e)
    (u : Fin d → Λ)
    (hsequence : RingTheory.Sequence.IsRegular (Localization.AtPrime q.asIdeal)
      (List.ofFn (fun j ↦ algebraMap Λ (Localization.AtPrime q.asIdeal) (u j))))
    (i : Fin d) (t : Fin d → Λ) (ht : ∀ j, j.val < i.val → t j ∉ q.asIdeal)
    (l : Λ) (hl : l ∉ q.asIdeal) :
    {x : LocalizedModule q.asIdeal.primeCompl
        (Λ ⧸ Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧ y = (u j * t j) ^ e}) |
      (u i * l) • x = 0} =
    {x : LocalizedModule q.asIdeal.primeCompl
        (Λ ⧸ Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧ y = (u j * t j) ^ e}) |
      (u i * l) • ((u i * l) • x) = 0} := by
  classical
  let A := Localization.AtPrime q.asIdeal
  let I : Ideal Λ := Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧ y = (u j * t j) ^ e}
  let J : Ideal A := I.map (algebraMap Λ A)
  let f : Fin d → Λ := fun j ↦ if j = i then l else if j.val < i.val then t j else 1
  have hf (j : Fin d) : f j ∉ q.asIdeal := by
    dsimp [f]
    split
    · exact hl
    · split
      · exact ht j ‹_›
      · exact q.asIdeal.one_notMem
  let g : Fin d → A := fun j ↦ algebraMap Λ A (u j * f j) ^ (if j = i then 1 else e)
  have hpowers : RingTheory.Sequence.IsRegular A (List.ofFn g) := by
    apply (RingTheory.Sequence.isRegular_ofFn_pow_iff A
      (fun j ↦ algebraMap Λ A (u j * f j))
      (fun j ↦ if j = i then 1 else e) (fun j ↦ by split <;> omega)).mp
    simpa only [map_mul, mul_comm] using
      regular_ofFn_mul_units (M := A) (fun j ↦ algebraMap Λ A (u j))
        (fun j ↦ algebraMap Λ A (f j))
        (fun j ↦ IsLocalization.map_units A (⟨f j, hf j⟩ : q.asIdeal.primeCompl))
        hsequence
  have hJ : Ideal.ofList ((List.ofFn g).take i.val) = J := by
    rw [ofList_take_ofFn]
    dsimp only [J, I]
    rw [Ideal.map_span]
    apply congrArg Ideal.span
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨(u j * t j) ^ e, ⟨j, hj, rfl⟩, ?_⟩
      have hne : j ≠ i := by intro h; subst j; omega
      simp only [g, f, ite_eq_right hne, ite_eq_left hj, map_pow]
    · rintro ⟨z, ⟨j, hj, rfl⟩, rfl⟩
      refine ⟨j, hj, ?_⟩
      have hne : j ≠ i := by intro h; subst j; omega
      simp only [g, f, ite_eq_right hne, ite_eq_left hj, map_pow]
  have hreg : IsSMulRegular (A ⧸ J) (algebraMap Λ A (u i * l)) := by
    have h := hpowers.toIsWeaklyRegular.regular_mod_prev i.val (by simp)
    rw [hJ, Ideal.smul_eq_mul, Ideal.mul_top] at h
    simpa [g, f] using h
  let : Algebra (Λ ⧸ I) (A ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let F : Λ ⧸ I →ₗ[Λ] A ⧸ J :=
    (IsScalarTower.toAlgHom Λ (Λ ⧸ I) (A ⧸ J)).toLinearMap
  have : IsLocalizedModule q.asIdeal.primeCompl F := inferInstance
  let E := IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (Λ ⧸ I)) F
  have hreg' : IsSMulRegular (A ⧸ J) (u i * l) := by
    intro x y h
    apply hreg
    simpa only [algebraMap_smul] using h
  have hreg'' : IsSMulRegular (LocalizedModule q.asIdeal.primeCompl (Λ ⧸ I))
      (u i * l) := (E.isSMulRegular_congr (u i * l)).mpr hreg'
  ext x
  change ((u i * l) • x = 0) ↔ (u i * l) • ((u i * l) • x) = 0
  constructor
  · intro h
    simp only [h, smul_zero]
  · intro h
    exact hreg'' (by simpa only [smul_zero] using h)

private theorem exists_cleared_relation
    {Λ : Type v} [CommRing Λ] (q : PrimeSpectrum Λ)
    (E : ℕ) (hE : 0 < E) (u : Λ) (s : ℕ) (z : Fin s → Λ)
    (w : Fin s → Localization.AtPrime q.asIdeal)
    (hw : (algebraMap Λ (Localization.AtPrime q.asIdeal) u) ^ E =
      ∑ j, w j * algebraMap Λ (Localization.AtPrime q.asIdeal) (z j)) :
    ∃ (l : Λ) (mu : Fin s → Λ), l ∉ q.asIdeal ∧
      (u * l) ^ E = ∑ j, mu j * z j ∧
      ∀ j, algebraMap Λ (Localization.AtPrime q.asIdeal) (mu j) =
        algebraMap Λ (Localization.AtPrime q.asIdeal) l ^ E * w j := by
  classical
  let A := Localization.AtPrime q.asIdeal
  let f := algebraMap Λ A
  obtain ⟨s0, hs0⟩ := IsLocalization.exist_integer_multiples_of_finite
    q.asIdeal.primeCompl w
  choose v hv using hs0
  have hv' (j : Fin s) : f (v j) = f (s0 : Λ) * w j := by
    simpa only [Algebra.smul_def] using hv j
  let mu0 : Fin s → Λ := fun j ↦ (s0 : Λ) ^ (E - 1) * v j
  have hm0 (j : Fin s) : f (mu0 j) = f (s0 : Λ) ^ E * w j := by
    dsimp [mu0]
    rw [map_mul, map_pow, hv', ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hE]
  have heq : f ((u * (s0 : Λ)) ^ E) = f (∑ j, mu0 j * z j) := by
    simp only [map_pow, map_mul, mul_pow, map_sum, hm0]
    rw [hw, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  obtain ⟨s1, hs1⟩ := (IsLocalization.eq_iff_exists q.asIdeal.primeCompl A).mp heq
  let l : Λ := (s0 : Λ) * s1
  let mu : Fin s → Λ := fun j ↦ (s1 : Λ) ^ E * mu0 j
  refine ⟨l, mu, q.asIdeal.primeCompl.mul_mem s0.property s1.property, ?_, ?_⟩
  · have hpow1 : (s1 : Λ) ^ (E - 1) * (s1 : Λ) = (s1 : Λ) ^ E := by
      rw [← pow_succ, Nat.sub_add_cancel hE]
    calc
      (u * l) ^ E = (s1 : Λ) ^ (E - 1) * ((s1 : Λ) * (u * (s0 : Λ)) ^ E) := by
        dsimp [l]
        simp only [mul_pow]
        rw [← hpow1]
        ring
      _ = (s1 : Λ) ^ (E - 1) * ((s1 : Λ) * ∑ j, mu0 j * z j) := by rw [hs1]
      _ = ∑ j, mu j * z j := by
        simp only [Finset.mul_sum, ← mul_assoc, hpow1, mu]
  · intro j
    dsimp [mu, l]
    rw [map_mul, map_pow, hm0, map_mul, mul_pow]
    ring

private theorem capture_power
    {k : Type u} {D : Type w} {S : Type v}
    [Field k] [CommRing D] [CommRing S] [Algebra k D]
    [IsLocalRing D] [IsArtinianRing D] [IsLocalRing S] [IsArtinianRing S]
    (p : ℕ) [Fact p.Prime] [CharP S p]
    (g : D →+* S) [IsLocalHom g] (hgflat : g.Flat) (x : S) :
    ∃ (r : ℕ), 0 < r ∧
      ∃ (D' : Type (max u v w)) (_ : CommRing D') (_ : IsLocalRing D')
        (_ : IsArtinianRing D') (_ : Algebra k D')
        (h : D →ₐ[k] D') (g' : D' →+* S),
        IsLocalHom g' ∧ g'.Flat ∧
        (let : Algebra D D' := h.toRingHom.toAlgebra; EssentiallySmooth D D') ∧
        g'.comp h.toRingHom = g ∧ x ^ r ∈ Set.range g' := by
  obtain ⟨r, hr, D', hD', hDD', g', hlocal, hart, hmap, hg', hsmooth, hflat, hcomp,
    hx⟩ := exists_artinian_coefficient_enlargement.{w, v, u} D S p g hgflat x
  let : CommRing D' := hD'
  let : Algebra D D' := hDD'
  let : Algebra k D' := ((algebraMap D D').comp (algebraMap k D)).toAlgebra
  let h : D →ₐ[k] D' :=
    { toRingHom := algebraMap D D', commutes' := fun _ ↦ rfl }
  refine ⟨r, hr, D', hD', hlocal, hart, inferInstance, h, g', hg', hflat, ?_, hcomp, hx⟩
  change let : Algebra D D' := (algebraMap D D').toAlgebra; EssentiallySmooth D D'
  rw [toAlgebra_algebraMap]
  exact hsmooth

/-- Extend a coefficient ring for a single parameter, with previously chosen factors fixed.
Source: Stacks Project, Lemma 07FJ, ad (13), using Lemma 07FI and Ogoma's Lemma 07FC.
(blueprint: lem-weil-pbc-popescu-coefficient-step).

Proof: Put L = Λ_q and S = L/m_L^n. The flat local map g is injective and faithfully flat.
The residue of u_i^N belongs to the extended ideal generated by z_j. All these residues
and the residue of u_i are in g(D), so ideal contraction gives u_i^N = sum b_j d_j in D.
Lift g(d_j) to c_j in L. The error is in m_L^n, which lies in m_L^(n-N) times the ideal
of the z_j by hpower. Write the error as sum z_j c'_j with c'_j in m_L^(n-N).
Thus u_i^(2N) = sum z_j w_j in L, where w_j = u_i^N(c_j+c'_j). The correction term
u_i^N c'_j vanishes in S; hence all residues of w_j are in g(D).
Choose a common denominator s₀ outside q, with w_j = v_j/s₀, and a second denominator
s₁ outside q annihilating the cleared equation error. For s=s₀s₁ set
mu_j=s^(2N-1)s₁v_j. Then (s u_i)^(2N)=sum mu_j z_j in Λ and mu_j/s^(2N)=w_j in L.
The enlargement argument of 07FI applies to any flat local Artinian coefficient ring
in positive characteristic: enlarge D essentially smoothly so a positive power s^r
has residue in it. Replace s by s^r and mu_j by s^(2N(r-1))mu_j. Their residues now lie
in the enlarged coefficient ring. Previous factors t_j are units in L. Multiplying
regular-sequence entries by these units, and raising preceding entries to 8c-th powers,
preserves regularity. The current entry therefore has equal first and square kernels
in L modulo the preceding powered entries. Apply Ogoma to the corresponding finitely
generated Λ-quotient to get s' outside q whose every positive power stabilizes these
kernels in Λ. Enlarge once more by 07FI so some (s')^r' has residue in the coefficient
ring. Multiply s by (s')^r' and mu_j by (s')^(2Nr'). This gives l and ell, with the
required equation, kernel equality, and residue memberships. Compose the two
coefficient extensions and their maps to S. Both extensions are essentially smooth,
and the final map is local and flat. Give the new ring its k-structure through D;
the extension map is then a k-algebra map. The construction uses finite polynomial
algebras, finite quotients, and localizations over D, so stays in max u v w.
The case s=0 is covered: ideal contraction gives u_i^N=0 in D and the exact same
correction argument gives u_i^(2N)=0 in L before clearing denominators. -/
theorem exists_popescu_coefficient_step
    {k : Type u} {Λ : Type v} [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (q : PrimeSpectrum Λ) (N n : ℕ) (hN : 0 < N) (hn : N ≤ n)
    (d s c : ℕ) (hc : 0 < c)
    (uΛ : Fin d → Λ) (hu : ∀ j, uΛ j ∈ q.asIdeal)
    (hsequence : RingTheory.Sequence.IsRegular (Localization.AtPrime q.asIdeal)
      (List.ofFn (fun j ↦ algebraMap Λ (Localization.AtPrime q.asIdeal) (uΛ j))))
    (z : Fin s → Λ)
    (hpower : IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ N ≤
      (Ideal.span (Set.range z)).map (algebraMap Λ (Localization.AtPrime q.asIdeal)))
    (D : Type w) [CommRing D] [IsLocalRing D] [IsArtinianRing D] [Algebra k D]
    (g : D →+* Localization.AtPrime q.asIdeal ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n)
    [IsLocalRing (Localization.AtPrime q.asIdeal ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n)]
    [IsLocalHom g] (hgflat : g.Flat)
    (hgk : ∀ x : k, g (algebraMap k D x) = algebraMap k _ x)
    (b : Fin s → D)
    (hb : ∀ j, g (b j) = Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n)
      (algebraMap Λ (Localization.AtPrime q.asIdeal) (z j)))
    (hinc : ∀ j, Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n)
      (algebraMap Λ (Localization.AtPrime q.asIdeal) (uΛ j)) ∈ Set.range g)
    (i : Fin d) (t : Fin d → Λ) (ht : ∀ j, j.val < i.val → t j ∉ q.asIdeal) :
    ∃ (l : Λ) (ell : Fin s → Λ),
      l ∉ q.asIdeal ∧
      (uΛ i * l) ^ (2 * N) = ∑ j : Fin s, ell j * z j ∧
      (∀ x : Λ ⧸ Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧
        y = (uΛ j * t j) ^ (c * 8)},
        (uΛ i * l) • x = 0 ↔ (uΛ i * l) ^ 2 • x = 0) ∧
      ∃ (D' : Type (max u v w)) (_ : CommRing D') (_ : IsLocalRing D')
        (_ : IsArtinianRing D') (_ : Algebra k D')
        (h : D →ₐ[k] D')
        (g' : D' →+* Localization.AtPrime q.asIdeal ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n),
        IsLocalHom g' ∧ g'.Flat ∧
        (letI : Algebra D D' := h.toRingHom.toAlgebra; EssentiallySmooth D D') ∧
        g'.comp h.toRingHom = g ∧
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n)
          (algebraMap Λ (Localization.AtPrime q.asIdeal) l) ∈ Set.range g' ∧
        (∀ j, Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n)
          (algebraMap Λ (Localization.AtPrime q.asIdeal) (ell j)) ∈ Set.range g') := by
  classical
  have _ := hgk
  let A := Localization.AtPrime q.asIdeal
  let K : Ideal A := IsLocalRing.maximalIdeal A ^ n
  let S := A ⧸ K
  let res : Λ →+* S := (Ideal.Quotient.mk K).comp (algebraMap Λ A)
  have hpprime : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right (by omega)
  have : Fact p.Prime := ⟨hpprime⟩
  have : CharP S p := charP_of_injective_algebraMap (algebraMap k S).injective p
  have : IsArtinianRing S := by
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing K
    have hrad : K.radical = IsLocalRing.maximalIdeal A := by
      dsimp only [K]
      rw [Ideal.radical_pow _ (by omega),
        (inferInstance : (IsLocalRing.maximalIdeal A).IsPrime).radical]
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  obtain ⟨w, hw, hwres⟩ := exists_popescu_localized_coefficient_relation
    q N n hN hn (uΛ i) (hu i) s z hpower D g hgflat b hb (hinc i)
  obtain ⟨s0, mu0, hs0, heq0, hmu0⟩ :=
    exists_cleared_relation q (2 * N) (by omega) (uΛ i) s z w hw
  obtain ⟨r, hr, D1, hD1, hlocal1, hart1, hkD1, h1, g1,
    hg1, hflat1, hsmooth1, hcomp1, hs0res⟩ := capture_power (k := k) p g hgflat (res s0)
  let : CommRing D1 := hD1
  have : IsLocalRing D1 := hlocal1
  have : IsArtinianRing D1 := hart1
  let : Algebra k D1 := hkD1
  have : IsLocalHom g1 := hg1
  have hge1 (x : D) : g1 (h1 x) = g x := congrArg (fun f ↦ f x) hcomp1
  have preserve1 {x : S} (hx : x ∈ Set.range g) : x ∈ Set.range g1 := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨h1 y, hge1 y⟩
  obtain ⟨r0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  let l0 := s0 ^ (r0 + 1)
  let mu1 : Fin s → Λ := fun j ↦ s0 ^ (2 * N * r0) * mu0 j
  have hl0 : l0 ∉ q.asIdeal := q.asIdeal.primeCompl.pow_mem hs0 _
  have hpow (a : Λ) : a ^ (2 * N * r0) * a ^ (2 * N) =
      (a ^ (r0 + 1)) ^ (2 * N) := by
    rw [← pow_add, ← pow_mul]
    congr 1
    ring
  have heq1 : (uΛ i * l0) ^ (2 * N) = ∑ j, mu1 j * z j := by
    calc
      _ = s0 ^ (2 * N * r0) * (uΛ i * s0) ^ (2 * N) := by
        simp only [l0, mul_pow]
        rw [← hpow]
        ring
      _ = ∑ j, mu1 j * z j := by
        rw [heq0, Finset.mul_sum]
        simp only [mu1, mul_assoc]
  have hl0res : res l0 ∈ Set.range g1 := by
    simpa only [l0, map_pow] using hs0res
  have hmu1res (j : Fin s) : res (mu1 j) ∈ Set.range g1 := by
    have hres : res (mu1 j) = res l0 ^ (2 * N) * Ideal.Quotient.mk K (w j) := by
      change Ideal.Quotient.mk K (algebraMap Λ A (mu1 j)) = _
      have hlocal : algebraMap Λ A (mu1 j) =
          algebraMap Λ A l0 ^ (2 * N) * w j := by
        dsimp only [mu1]
        rw [map_mul, map_pow, hmu0 j, ← mul_assoc, ← pow_add]
        simp only [l0, map_pow, ← pow_mul]
        congr 2
        ring
      rw [hlocal, map_mul, map_pow]
      rfl
    rw [hres]
    obtain ⟨a, ha⟩ := hl0res
    obtain ⟨b, hb⟩ := preserve1 (hwres j)
    exact ⟨a ^ (2 * N) * b, by rw [map_mul, map_pow, ha, hb]⟩
  let J : Ideal Λ := Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧
    y = (uΛ j * t j) ^ (c * 8)}
  obtain ⟨a, ha⟩ := ogoma_lemma (M := Λ ⧸ J) q.asIdeal.primeCompl (uΛ i * l0)
    (localized_kernel_eq q d (c * 8) (by omega) uΛ hsequence i t ht l0 hl0)
  obtain ⟨r, hr, D2, hD2, hlocal2, hart2, hkD2, h2, g2,
    hg2, hflat2, hsmooth2, hcomp2, hares⟩ := capture_power (k := k) p g1 hflat1 (res (a : Λ))
  let : CommRing D2 := hD2
  have : IsLocalRing D2 := hlocal2
  have : IsArtinianRing D2 := hart2
  let : Algebra k D2 := hkD2
  let h := h2.comp h1
  have hge2 (x : D1) : g2 (h2 x) = g1 x := congrArg (fun f ↦ f x) hcomp2
  have preserve2 {x : S} (hx : x ∈ Set.range g1) : x ∈ Set.range g2 := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨h2 y, hge2 y⟩
  let l := l0 * (a : Λ) ^ r
  let ell : Fin s → Λ := fun j ↦ mu1 j * ((a : Λ) ^ r) ^ (2 * N)
  refine ⟨l, ell, q.asIdeal.primeCompl.mul_mem hl0
    (q.asIdeal.primeCompl.pow_mem a.property r), ?_, ?_,
    D2, hD2, hlocal2, hart2, hkD2, h, g2, hg2, hflat2, ?_, ?_, ?_, ?_⟩
  · change (uΛ i * (l0 * (a : Λ) ^ r)) ^ (2 * N) = _
    rw [← mul_assoc, mul_pow, heq1, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [ell]
    ring
  · intro x
    have hker := Set.ext_iff.mp (ha r hr) x
    simpa only [Set.mem_ofPred_eq, l, mul_assoc, mul_comm, mul_left_comm] using hker
  · exact RingHom.essentiallySmooth_comp h1.toRingHom h2.toRingHom hsmooth1 hsmooth2
  · ext x
    exact (hge2 (h1 x)).trans (hge1 x)
  · change res l ∈ Set.range g2
    obtain ⟨x, hx⟩ := preserve2 hl0res
    obtain ⟨y, hy⟩ := hares
    refine ⟨x * y, ?_⟩
    simp only [map_mul, hx, hy, l, map_pow]
  · intro j
    change res (ell j) ∈ Set.range g2
    obtain ⟨x, hx⟩ := preserve2 (hmu1res j)
    obtain ⟨y, hy⟩ := hares
    refine ⟨x * y ^ (2 * N), ?_⟩
    simp only [map_mul, map_pow, hx, hy, ell]

end Algebra
