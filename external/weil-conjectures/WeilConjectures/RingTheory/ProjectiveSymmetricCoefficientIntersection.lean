/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Cotangent

/-! # The coefficient ideal intersection in a projective symmetric presentation

Source: Stacks Project, Smoothing Ring Maps, Tag 07CE, equation-sequence;
More on Algebra, Tags 07CX and 07D4, specialized to a split symmetric presentation.
(blueprint: lem-weil-pbc-projective-symmetric-coefficient-intersection)
-/

@[expose] public section

universe u

namespace Algebra

/-- The square of the presentation kernel intersects the coefficient ideal in their product.
Source: Stacks Project, More on Algebra, Tags 07CX and 07D4, as used in the proof of
Smoothing Ring Maps, Tag 07CE, equation-sequence.
(blueprint: lem-weil-pbc-projective-symmetric-coefficient-intersection)

Proof (direct algebraic argument, F4). Put A = P/I, M = I/I², Q = P[y],
B = A[y], π : Q → B, H = ker π, and J = ker φ. Projectivity splits q by a
linear section s. The linear map k : A^m → B taking basis vectors to variables
satisfies αk = ιq. The symmetric-algebra universal property therefore extends ks
to σ : Sym_A M → B with ασ = id. Lift each σ(α(y_j)) through the surjective
coefficient reduction π, and substitute these lifts to define β : Q → Q, fixing
coefficients. Then πβ = σαπ and φβ = φ. Hence β(J) is contained in H, H is
contained in J, and β(x) - x is in J for every x in Q.
If x is in H, all its coefficients reduce to zero. Expanding x as a finite sum
of coefficient constants times monomials shows β(x) - x is in HJ: β fixes the
constants, and the difference on each monomial belongs to J.
For x in H ∩ J², β(x) belongs to H², hence HJ. Subtracting β(x) - x shows
x belongs to HJ. Conversely HJ is contained in H and in J² because H ≤ J.
No nonzero-ring hypothesis or nonempty basis is used, so the proof includes
I = P and m = 0. -/
theorem projective_symmetric_coefficient_intersection
    (P : Type u) [CommRing P] (I : Ideal P) (m : ℕ)
    [Module.Projective (P ⧸ I) I.Cotangent]
    (q : (Fin m → P ⧸ I) →ₗ[P ⧸ I] I.Cotangent) (hq : Function.Surjective q)
    (α : MvPolynomial (Fin m) (P ⧸ I) →ₐ[P ⧸ I] SymmetricAlgebra (P ⧸ I) I.Cotangent)
    (hαX : ∀ j, α (MvPolynomial.X j) =
      SymmetricAlgebra.ι (P ⧸ I) I.Cotangent (q (Pi.single j 1)))
    (φ : MvPolynomial (Fin m) P →+* SymmetricAlgebra (P ⧸ I) I.Cotangent)
    (hφeq : φ = α.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk I))) :
    RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m)) ⊓
        (RingHom.ker φ) ^ 2 =
      RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m)) *
        RingHom.ker φ := by
  classical
  let A := P ⧸ I
  let M := I.Cotangent
  let Q := MvPolynomial (Fin m) P
  let B := MvPolynomial (Fin m) A
  let π : Q →+* B := MvPolynomial.map (Ideal.Quotient.mk I)
  let H : Ideal Q := RingHom.ker π
  let J : Ideal Q := RingHom.ker φ
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  let k : (Fin m → A) →ₗ[A] B :=
    (Pi.basisFun A (Fin m)).constr A MvPolynomial.X
  have hk : α.toLinearMap.comp k = (SymmetricAlgebra.ι A M).comp q := by
    apply (Pi.basisFun A (Fin m)).ext
    intro j
    change α (k ((Pi.basisFun A (Fin m)) j)) = _
    rw [show k ((Pi.basisFun A (Fin m)) j) = MvPolynomial.X j from
      (Pi.basisFun A (Fin m)).constr_basis A MvPolynomial.X j]
    rw [LinearMap.comp_apply, Pi.basisFun_apply]
    exact hαX j
  let σ : SymmetricAlgebra A M →ₐ[A] B := SymmetricAlgebra.lift (k.comp s)
  have hασ : α.comp σ = AlgHom.id A _ := by
    apply SymmetricAlgebra.algHom_ext
    ext x
    change α (σ (SymmetricAlgebra.ι A M x)) = SymmetricAlgebra.ι A M x
    rw [SymmetricAlgebra.lift_ι_apply]
    change (α.toLinearMap.comp k) (s x) = _
    rw [hk]
    change SymmetricAlgebra.ι A M (q (s x)) = _
    rw [show q (s x) = x from LinearMap.congr_fun hs x]
  have hπ : Function.Surjective π :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  choose y hy using fun j : Fin m ↦ hπ (σ (α (MvPolynomial.X j)))
  let β : Q →+* Q := MvPolynomial.eval₂Hom MvPolynomial.C y
  have hπβ : π.comp β = σ.toRingHom.comp (α.toRingHom.comp π) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change π (β (MvPolynomial.C a)) = σ (α (π (MvPolynomial.C a)))
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
      change MvPolynomial.C (Ideal.Quotient.mk I a) =
        σ (α (MvPolynomial.C (Ideal.Quotient.mk I a)))
      rw [show α (MvPolynomial.C (Ideal.Quotient.mk I a)) =
        algebraMap A (SymmetricAlgebra A M) (Ideal.Quotient.mk I a) from
          α.commutes (Ideal.Quotient.mk I a), σ.commutes]
      rfl
    · intro j
      change π (β (MvPolynomial.X j)) = σ (α (π (MvPolynomial.X j)))
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.map_X]
      exact hy j
  have hφβ : φ.comp β = φ := by
    rw [hφeq, RingHom.comp_assoc, hπβ]
    have hασ' : α.toRingHom.comp σ.toRingHom = RingHom.id _ :=
      congrArg AlgHom.toRingHom hασ
    rw [← RingHom.comp_assoc, hασ', RingHom.id_comp]
  have hβJ : J.map β ≤ H := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change π (β x) = 0
    have he := RingHom.congr_fun hπβ x
    change π (β x) = σ (α (π x)) at he
    rw [he, show α (π x) = φ x from (RingHom.congr_fun hφeq x).symm]
    rw [show φ x = 0 from hx, map_zero]
  have hdiff : ∀ x : Q, β x - x ∈ J := by
    intro x
    change φ (β x - x) = 0
    rw [map_sub, show φ (β x) = φ x from RingHom.congr_fun hφβ x, sub_self]
  have hHJ : H ≤ J := by
    intro x hx
    change φ x = 0
    rw [hφeq]
    change α (π x) = 0
    rw [show π x = 0 from hx, map_zero]
  have hcoeff : ∀ x : Q, x ∈ H → ∀ d, MvPolynomial.C (AddMonoidAlgebra.coeff x d) ∈ H := by
    intro x hx d
    change π (MvPolynomial.C (AddMonoidAlgebra.coeff x d)) = 0
    have hc := congrArg (fun p ↦ AddMonoidAlgebra.coeff p d) (show π x = 0 from hx)
    have hc' : Ideal.Quotient.mk I (AddMonoidAlgebra.coeff x d) = 0 := by
      rw [← MvPolynomial.coeff_map (Ideal.Quotient.mk I) x d]
      exact hc
    rw [MvPolynomial.map_C, hc', MvPolynomial.C_0]
  have hHdiff : ∀ x : Q, x ∈ H → β x - x ∈ H * J := by
    intro x hx
    have hxsum := x.as_sum
    rw [hxsum]
    rw [map_sum, ← Finset.sum_sub_distrib]
    apply Ideal.sum_mem
    intro d hd
    have hmono : MvPolynomial.monomial d (AddMonoidAlgebra.coeff x d) =
        MvPolynomial.C (AddMonoidAlgebra.coeff x d) * MvPolynomial.monomial d 1 := by
      simp [MvPolynomial.monomial_eq]
    rw [hmono, map_mul, show β (MvPolynomial.C (AddMonoidAlgebra.coeff x d)) =
      MvPolynomial.C (AddMonoidAlgebra.coeff x d) from MvPolynomial.eval₂Hom_C _ _ _,
      ← mul_sub]
    exact Ideal.mul_mem_mul (hcoeff x hx d) (hdiff _)
  change H ⊓ J ^ 2 = H * J
  apply le_antisymm
  · intro x hx
    have hβx : β x ∈ H ^ 2 := by
      have hmap : (J ^ 2).map β ≤ H ^ 2 := by
        rw [Ideal.map_pow]
        exact pow_le_pow_left' hβJ 2
      exact hmap (Ideal.mem_map_of_mem β hx.2)
    have hβx' : β x ∈ H * J := by
      apply (Ideal.mul_mono le_rfl hHJ)
      simpa only [pow_two] using hβx
    have he := (H * J).sub_mem hβx' (hHdiff x hx.1)
    simpa using he
  · exact le_inf Ideal.mul_le_left (by
      rw [pow_two]
      exact Ideal.mul_mono hHJ le_rfl)

end Algebra
