/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The completion of a flat local extension of the p-adic integers is a DVR

Source: Stacks Project, Algebra, proof of Lemma Tag 0328 and the factorization
argument in Lemma Tag 00PD.
(blueprint: lem-weil-pbc-cohen-completion-dvr).
-/

@[expose] public section

universe u

private theorem factor_of_bound {R : Type*} [CommRing R] [IsLocalRing R]
    (a : R) (hm : IsLocalRing.maximalIdeal R = Ideal.span {a}) (N : ℕ) :
    ∀ x : R, x ∉ IsLocalRing.maximalIdeal R ^ N →
      ∃ n : ℕ, ∃ y : R, IsUnit y ∧ x = a ^ n * y := by
  induction N with
  | zero => simp
  | succ N ih =>
    intro x hx
    by_cases hu : IsUnit x
    · exact ⟨0, x, hu, by simp⟩
    have hxmem : x ∈ IsLocalRing.maximalIdeal R := by
      simpa [IsLocalRing.mem_maximalIdeal] using hu
    rw [hm, Ideal.mem_span_singleton] at hxmem
    obtain ⟨y, hy⟩ := hxmem
    have hynot : y ∉ IsLocalRing.maximalIdeal R ^ N := by
      intro hyN
      apply hx
      rw [hy, pow_succ']
      exact Ideal.mul_mem_mul (by rw [hm]; exact Ideal.subset_span (by simp)) hyN
    obtain ⟨n, z, hz, hzy⟩ := ih y hynot
    refine ⟨n + 1, z, hz, ?_⟩
    rw [hy, hzy, pow_succ']
    ring

private theorem completion_regular {R : Type*} [CommRing R]
    (I : Ideal R) (a : R) (hI : I = Ideal.span {a}) (ha : IsLeftRegular a) :
    IsLeftRegular (algebraMap R (AdicCompletion I R) a) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro x hx
  apply AdicCompletion.ext
  intro n
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x.val (n + 1))
  have hzero : Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) (a * y) = 0 := by
    change Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) a *
      Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) y = 0
    have h := congrArg (fun z : AdicCompletion I R ↦ z.val (n + 1)) hx
    simpa [AdicCompletion.val_mul, AdicCompletion.algebraMap_apply,
      AdicCompletion.of_apply, ← hy, map_mul] using h
  have hmem : a * y ∈ I ^ (n + 1) := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hyz : y = a ^ n * z := ha (by change a * y = a * (a ^ n * z); rw [hz, pow_succ']; ring)
  have hyn : Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) y = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using
      (show a ^ n ∣ y from ⟨z, hyz⟩)
  have hcompat := x.property (Nat.le_succ n)
  rw [← hy] at hcompat
  change Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) y = x.val n at hcompat
  rw [← hcompat, hyn]
  rfl

private theorem factor_nonzero {R : Type*} [CommRing R] [IsLocalRing R]
    [IsHausdorff (IsLocalRing.maximalIdeal R) R]
    (a : R) (hm : IsLocalRing.maximalIdeal R = Ideal.span {a})
    (x : R) (hx : x ≠ 0) : ∃ n : ℕ, ∃ y : R, IsUnit y ∧ x = a ^ n * y := by
  have hex : ∃ N : ℕ, x ∉ IsLocalRing.maximalIdeal R ^ N := by
    by_contra! h
    apply hx
    apply IsHausdorff.haus' (I := IsLocalRing.maximalIdeal R)
    intro N
    apply SModEq.zero.mpr
    simpa using h N
  obtain ⟨N, hN⟩ := hex
  exact factor_of_bound a hm N x hN

/-- The fixed maximal-ideal completion of a flat local extension of the p-adic
integers with maximal ideal `(p)` is a domain and a discrete valuation ring.
Source: Stacks Project, Algebra, proof of Lemma Tag 0328; the final factorization
argument is the last assertion of Lemma Tag 00PD.
(blueprint: lem-weil-pbc-cohen-completion-dvr)

Proof:
1. Flatness over the domain `ℤ_[p]` makes multiplication by `p` injective on `S`:
   tensor the injective multiplication map on `ℤ_[p]` with `S`. Write `A` for the
   explicit completion `AdicCompletion (maximalIdeal S) S`.
2. The maximal ideal of `S` is the principal ideal `(p)`, hence finitely generated.
   The completion results of Tag 05GG make `A` complete and local, with maximal
   ideal `(p)` and nonzero field quotient `S/(p)`.
3. Multiplication by `p` is injective on `A` directly. If `p*x = 0`, choose a lift
   `y` of the component of `x` in `S/(p^(n+1))`. Then `p*y = p^(n+1)*z` for some
   `z` in `S`. Cancel `p` using step 1 to get `y = p^n*z`. Thus the component of
   `x` in `S/(p^n)` is zero for every `n`; componentwise equality gives `x = 0`.
4. Separatedness says that an element in every `(p)^n` is zero. For nonzero `x`,
   the set of `n` for which `x` belongs to `(p)^n` is a nonempty bounded initial
   segment of the natural numbers: choose a power not containing `x`, and use
   the decreasing filtration. Take its largest member `n` and write `x = p^n*u`.
   If `u` were a nonunit, locality would put it in `(p)`, contradicting maximality.
5. Products of two nonzero elements are `p^(n+m)` times a unit. They are nonzero
   by step 3 and nontriviality of `A`; hence `A` is a domain. The element `p` is
   nonzero by step 3 and is a nonunit since it is in the maximal ideal. Its
   principal ideal is maximal, so `p` is prime, hence irreducible in the domain.
6. Every nonzero ideal contains an element of least exponent in step 4. This
   element generates the ideal because all other elements are divisible by its
   power of `p`, and its unit factor is invertible. Thus every ideal is principal.
   The nonzero nonunit `p` shows that `A` is not a field. Together with locality
   and the domain property this is precisely a discrete valuation ring. -/
theorem adicCompletion_dvr_of_flat_padicInt (p : ℕ) [Fact p.Prime]
    (S : Type u) [CommRing S] [IsLocalRing S] (φ : ℤ_[p] →+* S)
    (hFlat : φ.Flat) (hMax : IsLocalRing.maximalIdeal S = Ideal.span {(p : S)}) :
    ∃ (_ : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal S) S)),
      IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
  let A := AdicCompletion (IsLocalRing.maximalIdeal S) S
  have hfg : (IsLocalRing.maximalIdeal S).FG := by
    rw [hMax]
    exact Submodule.fg_span_singleton _
  let : IsLocalRing A := AdicCompletion.isLocalRing_of_fg hfg
  let : IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
    AdicCompletion.isAdicComplete_of_fg hfg
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)} := by
    calc
      IsLocalRing.maximalIdeal A = (IsLocalRing.maximalIdeal S).map
          (algebraMap S A) := AdicCompletion.maximalIdeal_eq_map_of_fg hfg
      _ = (Ideal.span {(p : S)}).map (algebraMap S A) := congrArg
        (fun J : Ideal S ↦ J.map (algebraMap S A)) hMax
      _ = Ideal.span {(p : A)} := by rw [Ideal.map_span, Set.image_singleton, map_natCast]
  let : Algebra ℤ_[p] S := φ.toAlgebra
  let : Module.Flat ℤ_[p] S := hFlat
  have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hregS : IsLeftRegular (p : S) := by
    have h := Module.Flat.isSMulRegular_of_isRegular (M := S) (IsRegular.of_ne_zero hp)
    simpa [IsSMulRegular, IsLeftRegular, Algebra.smul_def] using h
  have hreg : IsLeftRegular (p : A) := by
    simpa only [map_natCast] using
      completion_regular (IsLocalRing.maximalIdeal S) (p : S) hMax hregS
  have : NoZeroDivisors A := by
    constructor
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    obtain ⟨n, u, hu, hxu⟩ := factor_nonzero (p : A) hm x hx
    right
    have hzero : (p : A) ^ n * (u * y) = (p : A) ^ n * 0 := by
      rw [← mul_assoc, ← hxu, hxy, mul_zero]
    have huy : u * y = 0 := (hreg.pow n) hzero
    exact hu.mul_right_eq_zero.mp huy
  let : IsDomain A := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr
    ⟨inferInstance, inferInstance⟩
  refine ⟨inferInstance, ?_⟩
  have hpA : (p : A) ≠ 0 := by
    intro h
    have : (1 : A) = 0 := hreg (by simp [h])
    exact one_ne_zero this
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨(p : A),
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (p : A) hpA hm, ?_⟩
  intro x hx
  obtain ⟨n, y, hy, hxy⟩ := factor_nonzero (p : A) hm x hx
  obtain ⟨u, hu⟩ := hy
  refine ⟨n, u, ?_⟩
  simpa [hu, mul_comm] using hxy.symm
