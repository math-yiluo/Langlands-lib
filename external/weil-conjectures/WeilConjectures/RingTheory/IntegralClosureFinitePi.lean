/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral closure in finite products of ring maps

Source: Stacks Project, Algebra, Tags 0CY8 and 0CY9
(blueprint: lem-weil-pbc-finite-product-integral-closure).
-/

@[expose] public section

universe w u v

/-- Coordinatewise integrality for finite products (Stacks Project, Algebra, Tag 0CY8). -/
private theorem integral_pi_iff {I : Type w} [Finite I]
    (R : I → Type u) (S : I → Type v) [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    [∀ i, Algebra (R i) (S i)] (x : ∀ i, S i) :
    IsIntegral (∀ i, R i) x ↔ ∀ i, IsIntegral (R i) (x i) := by
  classical
  constructor
  · intro hx i
    exact hx.map_of_comp_eq (Pi.evalRingHom R i) (Pi.evalRingHom S i) rfl
  · intro hx
    let _ : Fintype I := Fintype.ofFinite I
    choose p hp he using hx
    let D := Finset.univ.sup fun i ↦ (p i).natDegree
    have hd (i : I) : (p i).natDegree ≤ D := Finset.le_sup (f := fun i ↦ (p i).natDegree)
      (Finset.mem_univ i)
    let q (i : I) := Polynomial.X ^ (D - (p i).natDegree) * p i
    have hqdeg (i : I) : (q i).natDegree ≤ D := by
      calc
        (q i).natDegree ≤ (D - (p i).natDegree) + (p i).natDegree :=
          (Polynomial.natDegree_mul_le).trans
            (Nat.add_le_add_right (Polynomial.natDegree_X_pow_le _) _)
        _ = D := Nat.sub_add_cancel (hd i)
    have hqcoeff (i : I) : (q i).coeff D = 1 := by
      simp only [q, Polynomial.coeff_X_pow_mul']
      rw [ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self (hd i)]
      exact (hp i).coeff_natDegree
    let Q := (Polynomial.piEquiv R).symm q
    have hmap (i : I) : Q.map (Pi.evalRingHom R i) = q i :=
      congrFun ((Polynomial.piEquiv R).apply_symm_apply q) i
    have hc (n : ℕ) (i : I) : Q.coeff n i = (q i).coeff n := by
      simpa using congrArg (fun t ↦ t.coeff n) (hmap i)
    refine ⟨Q, ?_, ?_⟩
    · apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one D
      · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro n hn
        funext i
        rw [hc, Polynomial.coeff_eq_zero_of_natDegree_lt ((hqdeg i).trans_lt hn)]
        rfl
      · funext i
        exact (hc D i).trans (hqcoeff i)
    · funext i
      have hev : (q i).eval₂ (algebraMap (R i) (S i)) (x i) = 0 := by
        simp [q, Polynomial.eval₂_mul, he i]
      change (Pi.evalRingHom S i) (Q.eval₂ (algebraMap (∀ i, R i) (∀ i, S i)) x) = 0
      rw [Polynomial.hom_eval₂]
      have hcmap : (Pi.evalRingHom S i).comp (algebraMap (∀ i, R i) (∀ i, S i)) =
          (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i) := rfl
      rw [hcmap, ← Polynomial.eval₂_map, hmap]
      exact hev

/-- The integral closure of a finite product of ring maps is the product of the component
integral closures. For injective component maps, the product is integrally closed if and only
if every component is integrally closed. Source: Stacks Project, Algebra, Tag 0CY9, using 0CY8
(blueprint: lem-weil-pbc-finite-product-integral-closure).

Proof: project a monic polynomial annihilating a tuple to each coordinate to prove that its
coordinates are integral (def-weil-pbc-integral-closure). Conversely, choose monic annihilating
polynomials in each coordinate. Finiteness permits a common degree D at least one; multiply
each polynomial of degree d by T^(D-d), and assemble the coefficients coordinatewise. This
produces a monic polynomial over the product ring annihilating the tuple. For the empty
product both rings are zero rings and T suffices. The coordinatewise integrality criterion
identifies the integral-closure subring with the intersection of the inverse images of the
component closures under evaluation. If the component maps are injective, their product is
injective, and this equality identifies the closure with the base ring exactly when every
component closure equals its base ring, also for the empty product. -/
theorem integralClosure_finite_pi {I : Type w} [Finite I]
    (R : I → Type u) (S : I → Type v) [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (φ : ∀ i, R i →+* S i) :
    letI : ∀ i, Algebra (R i) (S i) := fun i ↦ (φ i).toAlgebra
    (integralClosure (∀ i, R i) (∀ i, S i)).toSubring =
        ⨅ i, (integralClosure (R i) (S i)).toSubring.comap (Pi.evalRingHom S i) ∧
      ((∀ i, Function.Injective (φ i)) →
        (IsIntegrallyClosedIn (∀ i, R i) (∀ i, S i) ↔
          ∀ i, IsIntegrallyClosedIn (R i) (S i))) := by
  classical
  let : ∀ i, Algebra (R i) (S i) := fun i ↦ (φ i).toAlgebra
  have hint (x : ∀ i, S i) := integral_pi_iff R S x
  constructor
  · ext x
    simpa only [Subring.mem_iInf, Subring.mem_comap, Subalgebra.mem_toSubring,
      mem_integralClosure_iff, Pi.evalRingHom_apply] using hint x
  · intro hinj
    rw [isIntegrallyClosedIn_iff]
    constructor
    · rintro ⟨_, hcl⟩ i
      rw [isIntegrallyClosedIn_iff]
      refine ⟨hinj i, ?_⟩
      intro x hx
      let y : ∀ j, S j := Pi.single i x
      have hy : IsIntegral (∀ j, R j) y := by
        apply (hint y).mpr
        intro j
        by_cases h : j = i
        · subst j
          simpa [y] using hx
        · simpa [y, Pi.single_eq_of_ne h] using (isIntegral_zero : IsIntegral (R j) (0 : S j))
      obtain ⟨r, hr⟩ := hcl hy
      refine ⟨r i, ?_⟩
      have hri : algebraMap (R i) (S i) (r i) = y i := congrFun hr i
      simpa [y] using hri
    · intro hcl
      refine ⟨?_, ?_⟩
      · intro a b hab
        funext i
        exact hinj i (congrFun hab i)
      · intro x hx
        have hc (i : I) : ∃ r : R i, algebraMap (R i) (S i) r = x i :=
          ((isIntegrallyClosedIn_iff.mp (hcl i)).2 ((hint x).mp hx i))
        choose r hr using hc
        exact ⟨r, funext hr⟩
