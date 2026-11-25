/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.LinearCombination

/-! # Exactness of the two-element localization row

Source: Stacks Project, algebra.tex, Tag 00EJ.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- The diagonal and difference form a short exact row for two comaximal elements.

Proof: A section killed in both localizations is killed by powers of both elements;
Bezout for those powers makes it zero. For a compatible pair of fractions, clear
both denominators and the power needed to clear equality on the overlap. Bezout
for the resulting powers gives a numerator realizing the pair. Every fraction
z/(fg)^n in the overlap is the difference of v*z/f^n and -u*z/g^n, where
u*f^n+v*g^n=1. This also includes the zero ring and zero denominators.

Source: Stacks Project, algebra.tex, Tag 00EJ, and the surjectivity argument in
algebraization.tex, Tag 0998.
(auxiliary; not a blueprint node). -/
theorem localization_two_exact
    {A : Type u} [CommRing A] (f g : A) (hc : IsCoprime f g)
    (S T P : Type u) [CommRing S] [CommRing T] [CommRing P]
    [Algebra A S] [Algebra A T] [Algebra A P]
    [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) P] :
    let F := IsLocalization.Away.awayToAwayRight
      (S := S) (P := P) f g
    let G := IsLocalization.Away.awayToAwayLeft
      (S := T) (P := P) g f
    Function.Injective (fun x : A ↦
      (algebraMap A (S) x, algebraMap A (T) x)) ∧
    Function.Exact (fun x : A ↦
      (algebraMap A (S) x, algebraMap A (T) x))
      (fun x : S × T ↦ F x.1 - G x.2) ∧
    Function.Surjective
      (fun x : S × T ↦ F x.1 - G x.2) := by
  let F := IsLocalization.Away.awayToAwayRight
    (S := S) (P := P) f g
  let G := IsLocalization.Away.awayToAwayLeft
    (S := T) (P := P) g f
  have hF (x : A) : F (algebraMap A _ x) = algebraMap A _ x :=
    IsLocalization.Away.awayToAwayRight_eq f g x
  have hG (x : A) : G (algebraMap A _ x) = algebraMap A _ x :=
    IsLocalization.Away.awayToAwayLeft_eq g f x
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq f (congrArg Prod.fst h)
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq g (congrArg Prod.snd h)
    obtain ⟨u, v, huv⟩ := (show IsCoprime (f ^ n) (g ^ m) from hc.pow)
    linear_combination u * hn + v * hm - (x - y) * huv
  · rintro ⟨x, y⟩
    constructor
    · intro hxy
      have he : F x = G y := sub_eq_zero.mp hxy
      obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f x
      obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj g y
      let N := n + m
      let a' := a * f ^ m
      let b' := b * g ^ n
      have hx : x * (algebraMap A (S) f) ^ N =
          algebraMap A _ a' := by
        dsimp only [N, a']
        rw [map_mul, map_pow, pow_add, ← mul_assoc, ha]
      have hy : y * (algebraMap A (T) g) ^ N =
          algebraMap A _ b' := by
        dsimp only [N, b']
        rw [map_mul, map_pow, Nat.add_comm n m, pow_add, ← mul_assoc, hb]
      have hx' : F x * (algebraMap A _ f) ^ N = algebraMap A _ a' := by
        simpa only [map_mul, map_pow, hF] using congrArg F hx
      have hy' : G y * (algebraMap A _ g) ^ N = algebraMap A _ b' := by
        simpa only [map_mul, map_pow, hG] using congrArg G hy
      have hz : algebraMap A (P) (a' * g ^ N) =
          algebraMap A _ (b' * f ^ N) := by
        simp only [map_mul, map_pow]
        rw [← hx', ← hy', he]
        ring
      obtain ⟨r, hr⟩ := IsLocalization.Away.exists_of_eq (f * g) hz
      let E := N + r
      let a'' := a' * f ^ r
      let b'' := b' * g ^ r
      have hcomp : a'' * g ^ E = b'' * f ^ E := by
        dsimp only [a'', b'', E]
        rw [pow_add, pow_add]
        rw [mul_pow] at hr
        linear_combination hr
      have hx'' : x * (algebraMap A (S) f) ^ E =
          algebraMap A _ a'' := by
        dsimp only [E, a'']
        rw [map_mul, map_pow, pow_add, ← mul_assoc, hx]
      have hy'' : y * (algebraMap A (T) g) ^ E =
          algebraMap A _ b'' := by
        dsimp only [E, b'']
        rw [map_mul, map_pow, pow_add, ← mul_assoc, hy]
      obtain ⟨u, v, huv⟩ := (show IsCoprime (f ^ E) (g ^ E) from hc.pow)
      let z := u * a'' + v * b''
      have hzf : z * f ^ E = a'' := by
        dsimp only [z]
        linear_combination a'' * huv - v * hcomp
      have hzg : z * g ^ E = b'' := by
        dsimp only [z]
        linear_combination b'' * huv + u * hcomp
      refine ⟨z, Prod.ext ?_ ?_⟩
      · apply ((IsLocalization.Away.algebraMap_isUnit f).pow E).mul_left_inj.mp
        change algebraMap A (S) z *
          (algebraMap A (S) f) ^ E = _
        rw [← map_pow, ← map_mul, hzf]
        simpa only [map_pow] using hx''.symm
      · apply ((IsLocalization.Away.algebraMap_isUnit g).pow E).mul_left_inj.mp
        change algebraMap A (T) z *
          (algebraMap A (T) g) ^ E = _
        rw [← map_pow, ← map_mul, hzg]
        simpa only [map_pow] using hy''.symm
    · rintro ⟨z, hz⟩
      rw [← hz]
      exact sub_eq_zero.mpr ((hF z).trans (hG z).symm)
  · intro z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (f * g) z
    obtain ⟨u, v, huv⟩ := (show IsCoprime (f ^ n) (g ^ n) from hc.pow)
    let x : S :=
      IsLocalization.mk' (M := Submonoid.powers f) _ (v * a) ⟨f ^ n, ⟨n, rfl⟩⟩
    let y : T :=
      IsLocalization.mk' (M := Submonoid.powers g) _ (-u * a) ⟨g ^ n, ⟨n, rfl⟩⟩
    have hx : F x * (algebraMap A _ f) ^ n = algebraMap A _ (v * a) := by
      have h := congrArg F (IsLocalization.mk'_spec (M := Submonoid.powers f) (S)
        (v * a) ⟨f ^ n, ⟨n, rfl⟩⟩)
      simpa only [x, map_mul, map_pow, hF] using h
    have hy : G y * (algebraMap A _ g) ^ n = algebraMap A _ (-u * a) := by
      have h := congrArg G (IsLocalization.mk'_spec (M := Submonoid.powers g) (T)
        (-u * a) ⟨g ^ n, ⟨n, rfl⟩⟩)
      simpa only [y, map_mul, map_pow, hG] using h
    refine ⟨(x, y), ?_⟩
    apply ((IsLocalization.Away.algebraMap_isUnit (f * g)).pow n).mul_right_inj.mp
    change (algebraMap A (P) (f * g)) ^ n * (F x - G y) = _
    rw [map_mul, mul_pow]
    have hb := congrArg (algebraMap A (P)) huv
    simp only [map_add, map_mul, map_pow, map_one] at hb
    simp only [map_mul, map_neg] at hx hy
    simp only [map_mul, mul_pow] at ha
    linear_combination (algebraMap A _ g) ^ n * hx -
      (algebraMap A _ f) ^ n * hy + algebraMap A _ a * hb - ha
