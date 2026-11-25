/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

import WeilConjectures.RingTheory.FiniteRankDefectDerivation

/-!
# Finite-rank correction of a lifted coefficient section

Source: Stacks Project, Tag 07FG, the derivation and Jacobi--Zariski paragraphs.
(blueprint: lem-weil-pbc-finite-rank-coefficient-correction)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- Given two structure maps agreeing modulo an annihilated ideal, adjust an existing
residue section so their discrepancy has finite rank over the base field. The fixed
coefficient field is not enlarged here; the finite error generators still lie in I.

Source: Stacks Project, Tag 07FG, from "These maps agree modulo I" through the formula
expressing theta(a) as a finite sum of a_j f_j.
(blueprint: lem-weil-pbc-finite-rank-coefficient-correction).

Proof:
1. Give I its K-vector-space structure through r; this is well defined because ker(r)I=0.
   The difference theta = algebraMap k Lambda - psi takes values in I. The product
   identity for two ring maps, and the fact their difference belongs to I, show that
   theta is a derivation over the prime field, with scalar action through k -> K.
2. The differentials dy for y in k span Omega_{k/F_p}; choose a basis dy_j from them.
   They remain a basis after extension of scalars to K. Jacobi--Zariski exactness at
   K tensor Omega_k identifies the kernel of its map to Omega_K with the image of
   H1(K/k). Its finite dimension puts this kernel in the span of a finite subset J0
   of the extended basis. The remaining dy_j have independent images in Omega_K.
3. Extend those images to a basis of Omega_K. Define a K-linear map to I agreeing with
   theta on these basis vectors and zero on the added vectors. Its universal
   derivation D : K -> I makes theta - D restricted to k vanish on all dy_j outside
   J0. Put f_j equal to its values on dy_j for j in J0. Every value of the corrected
   derivation lies in the k-span of this finite family, all of which belong to I.
4. Set sigma = sigma0 + D. The identities I^2 = 0 and ker(r)I = 0 show it is a ring
   map, a section of r, and unchanged modulo I. For each a choose a polynomial
   expression for psi(a) in t and sigma0(k(c0)), which exists by the ring-closure
   hypothesis. Reevaluate it using sigma instead. Every positive-degree term has
   the same value, since t lies in ker(r) and D takes values in I. The change in
   its constant coefficient is D(r(psi(a))) = D(algebraMap k K a). The new value b
   lies in the closure using sigma and the same c0. Thus algebraMap k Lambda a - b
   is precisely the corrected derivation value, in the k-span of the finite f_j.
   Ring closure allows integer constants as well; D vanishes on them. -/
theorem exists_finite_rank_coefficient_correction
    (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]
    (Λ : Type v) [CommRing Λ] [Algebra k Λ] [IsLocalRing Λ]
    (r : Λ →+* K) (hker : RingHom.ker r = IsLocalRing.maximalIdeal Λ)
    (hcomm : r.comp (algebraMap k Λ) = algebraMap k K)
    (t : Finset Λ) (ht : Ideal.span (t : Set Λ) = IsLocalRing.maximalIdeal Λ)
    (I : Ideal Λ) (hI : I ≤ RingHom.ker r)
    (hkill : IsLocalRing.maximalIdeal Λ * I = ⊥)
    (σ0 : K →+* Λ) (hσ0 : r.comp σ0 = RingHom.id K) (c0 : Finset K)
    (ψ : k →+* Λ)
    (hψ : (Ideal.Quotient.mk I).comp ψ =
      (Ideal.Quotient.mk I).comp (algebraMap k Λ))
    (hψmem : ∀ a : k, ψ a ∈ Subring.closure ((t : Set Λ) ∪
      σ0 '' (IntermediateField.adjoin k (c0 : Set K) : Set K)))
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (hH : Module.Finite K (H1Cotangent k K)) :
    ∃ (σ : K →+* Λ) (f : Finset Λ),
      r.comp σ = RingHom.id K ∧
      (Ideal.Quotient.mk I).comp σ = (Ideal.Quotient.mk I).comp σ0 ∧
      (f : Set Λ) ⊆ I ∧
      (∀ a : k, ∃ b : Λ,
        b ∈ Subring.closure ((t : Set Λ) ∪
          σ '' (IntermediateField.adjoin k (c0 : Set K) : Set K)) ∧
        algebraMap k Λ a - b ∈ Submodule.span k (f : Set Λ)) := by
  classical
  have hkill' : RingHom.ker r * I = ⊥ := by simpa [hker] using hkill
  have hzero {x y : Λ} (hx : x ∈ RingHom.ker r) (hy : y ∈ I) : x * y = 0 := by
    have hm := Ideal.mul_mem_mul hx hy
    rw [hkill'] at hm
    exact hm
  let theta : k →+ Λ := (algebraMap k Λ).toAddMonoidHom - ψ.toAddMonoidHom
  have htheta (a : k) : theta a ∈ I := by
    change algebraMap k Λ a - ψ a ∈ I
    apply Ideal.Quotient.eq.mp
    exact (RingHom.congr_fun hψ a).symm
  have htheta_one : theta 1 = 0 := by simp [theta]
  have htheta_mul (a b : k) :
      theta (a * b) = algebraMap k Λ a * theta b + algebraMap k Λ b * theta a := by
    have hz := hzero (hI (htheta a)) (htheta b)
    dsimp [theta] at hz ⊢
    simp only [map_mul]
    linear_combination -hz
  obtain ⟨D, f, hD1, hDmul, hDI, hfI, herr⟩ := exists_finite_rank_defect_derivation
    k K Λ r hcomm I hI hkill' σ0 hσ0 theta htheta htheta_one htheta_mul p hp hH
  have hrσ (x : K) : r (σ0 x) = x := RingHom.congr_fun hσ0 x
  have hrD (x : K) : r (D x) = 0 := RingHom.mem_ker.mp (hI (hDI x))
  have hact (x y : Λ) : σ0 (r x) * D (r y) = x * D (r y) := by
    have hx : σ0 (r x) - x ∈ RingHom.ker r := by
      rw [RingHom.mem_ker, map_sub, hrσ, sub_self]
    have hz := hzero hx (hDI (r y))
    linear_combination hz
  -- This ring endomorphism simultaneously adjusts every coefficient expression.
  let β : Λ →+* Λ :=
    { toFun := fun x ↦ x + D (r x)
      map_one' := by simp [hD1]
      map_zero' := by simp
      map_add' := by intros; simp only [map_add]; abel
      map_mul' := by
        intro x y
        have hz := hzero (hI (hDI (r x))) (hDI (r y))
        simp only [map_mul, hDmul]
        rw [hact x y, hact y x]
        linear_combination -hz }
  let σ := β.comp σ0
  have hσ_apply (x : K) : σ x = σ0 x + D x := by
    change σ0 x + D (r (σ0 x)) = _
    rw [hrσ]
  have hσ : r.comp σ = RingHom.id K := by
    ext x
    simp [hσ_apply, hrσ, hrD]
  have hσq : (Ideal.Quotient.mk I).comp σ = (Ideal.Quotient.mk I).comp σ0 := by
    ext x
    simp only [RingHom.comp_apply, hσ_apply, map_add]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hDI x), add_zero]
  refine ⟨σ, f, hσ, hσq, hfI, ?_⟩
  intro a
  have hrψ (a : k) : r (ψ a) = algebraMap k K a := by
    have hz := RingHom.mem_ker.mp (hI (htheta a))
    change r (algebraMap k Λ a - ψ a) = 0 at hz
    have hc := RingHom.congr_fun hcomm a
    simp only [RingHom.comp_apply] at hc
    rw [map_sub, hc, sub_eq_zero] at hz
    exact hz.symm
  let S := Subring.closure ((t : Set Λ) ∪
    σ '' (IntermediateField.adjoin k (c0 : Set K) : Set K))
  have hβmem {x : Λ}
      (hx : x ∈ Subring.closure ((t : Set Λ) ∪
        σ0 '' (IntermediateField.adjoin k (c0 : Set K) : Set K))) : β x ∈ S := by
    change x ∈ S.comap β
    apply (Subring.closure_le (t := S.comap β)).mpr ?_ hx
    intro x hx
    change β x ∈ S
    rcases hx with hx | ⟨y, hy, rfl⟩
    · have hxt : x ∈ RingHom.ker r := by
        rw [hker, ← ht]
        exact Ideal.subset_span hx
      have hβx : β x = x := by
        change x + D (r x) = x
        simp [RingHom.mem_ker.mp hxt]
      rw [hβx]
      exact Subring.subset_closure (Or.inl hx)
    · exact Subring.subset_closure (Or.inr ⟨y, hy, rfl⟩)
  refine ⟨β (ψ a), hβmem (hψmem a), ?_⟩
  have he := herr a
  change algebraMap k Λ a - (ψ a + D (r (ψ a))) ∈ Submodule.span k (f : Set Λ)
  rw [hrψ]
  convert he using 1
  dsimp [theta]
  abel

end Algebra
