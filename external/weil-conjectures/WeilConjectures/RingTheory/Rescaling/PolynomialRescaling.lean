/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Inductions

/-! # Polynomial rescaling at the origin

The parameter is the outer univariate polynomial variable. This keeps division by
that variable an explicit polynomial operation.
-/

@[expose] public noncomputable section
set_option autoImplicit false

namespace MvPolynomial.Rescaling

variable {R σ : Type*} [CommRing R]

private abbrev P := MvPolynomial σ R
private abbrev Q := Polynomial (P (R := R) (σ := σ))

/-- Substitute `t*x` into a polynomial, keeping its coefficients constant. -/
private def scale : P (R := R) (σ := σ) →+* Q (R := R) (σ := σ) :=
  eval₂Hom (Polynomial.C.comp C) (fun i ↦ Polynomial.X * Polynomial.C (X i))

/-- Substitute a polynomial tuple, keeping the outer parameter fixed. -/
private def subst (v : σ → Q (R := R) (σ := σ)) :
    Q (R := R) (σ := σ) →+* Q (R := R) (σ := σ) :=
  Polynomial.eval₂RingHom (eval₂Hom (Polynomial.C.comp C) v) Polynomial.X

/-- Remove the parameter factor after scaling a polynomial vanishing at zero. -/
private def divide (p : P (R := R) (σ := σ)) : Q (R := R) (σ := σ) :=
  (scale p).divX

private lemma scale_zero (p : P (R := R) (σ := σ)) :
    (scale p).coeff 0 = C (constantCoeff p) := by
  change Polynomial.constantCoeff (scale p) = _
  rw [scale, map_eval₂Hom]
  simp

private lemma scale_one (p : P (R := R) (σ := σ)) :
    (scale p).eval 1 = p := by
  change Polynomial.evalRingHom 1 (scale p) = _
  rw [scale, map_eval₂Hom]
  have hC : (Polynomial.evalRingHom (1 : P (R := R) (σ := σ))).comp
      (Polynomial.C.comp C) = C := by
    ext r
    simp
  simpa only [hC, coe_eval₂Hom, Polynomial.coe_evalRingHom, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, one_mul] using eval₂_eta p

private lemma mul_divide (p : P (R := R) (σ := σ)) (hp : constantCoeff p = 0) :
    Polynomial.X * divide p = scale p := by
  have h := Polynomial.X_mul_divX_add (scale p)
  simpa only [divide, scale_zero, hp, map_zero, add_zero] using h

private lemma subst_X (v : σ → Q (R := R) (σ := σ)) :
    subst v Polynomial.X = Polynomial.X := by simp [subst]

private lemma subst_C (v : σ → Q (R := R) (σ := σ)) (p : P (R := R) (σ := σ)) :
    subst v (Polynomial.C p) = eval₂Hom (Polynomial.C.comp C) v p := by
  simp [subst]

private lemma subst_scale (v : σ → Q (R := R) (σ := σ))
    (p : P (R := R) (σ := σ)) :
    subst v (scale p) =
      eval₂Hom (Polynomial.C.comp C) (fun i ↦ Polynomial.X * v i) p := by
  rw [scale, map_eval₂Hom]
  apply eval₂Hom_congr ?_ ?_ rfl
  · apply RingHom.ext
    intro r
    simp [subst_C]
  · funext i
    simp only [map_mul, subst_X, subst_C, eval₂Hom_X']

private lemma scale_eval (v : σ → P (R := R) (σ := σ))
    (p : P (R := R) (σ := σ)) :
    scale (eval₂Hom C v p) = eval₂Hom (Polynomial.C.comp C) (fun i ↦ scale (v i)) p := by
  rw [map_eval₂Hom]
  apply eval₂Hom_congr ?_ rfl rfl
  apply RingHom.ext
  intro r
  simp [scale]

/-- Rescaling commutes with substitution when each substituted polynomial fixes zero. -/
private theorem subst_divide (v : σ → P (R := R) (σ := σ))
    (hv : ∀ i, constantCoeff (v i) = 0) (p : P (R := R) (σ := σ))
    (hp : constantCoeff p = 0)
    (hvp : constantCoeff (eval₂Hom C v p) = 0) :
    subst (fun i ↦ divide (v i)) (divide p) = divide (eval₂Hom C v p) := by
  apply Polynomial.isRegular_X.left
  change Polynomial.X * subst (fun i ↦ divide (v i)) (divide p) =
    Polynomial.X * divide (eval₂Hom C v p)
  calc
    _ = subst (fun i ↦ divide (v i)) (Polynomial.X * divide p) := by
      rw [map_mul, subst_X]
    _ = subst (fun i ↦ divide (v i)) (scale p) := by rw [mul_divide p hp]
    _ = eval₂Hom (Polynomial.C.comp C) (fun i ↦ Polynomial.X * divide (v i)) p :=
      subst_scale _ _
    _ = scale (eval₂Hom C v p) := by
      rw [scale_eval]
      apply eval₂Hom_congr rfl ?_ rfl
      funext i
      exact mul_divide (v i) (hv i)
    _ = _ := (mul_divide _ hvp).symm

private lemma divide_X (i : σ) : divide (X i : P (R := R)) = Polynomial.C (X i) := by
  apply Polynomial.isRegular_X.left
  change Polynomial.X * divide (X i : P (R := R)) = _
  rw [mul_divide _ (by simp)]
  simp [scale]

private lemma divide_one (p : P (R := R) (σ := σ)) (hp : constantCoeff p = 0) :
    (divide p).eval 1 = p := by
  have h := congrArg (Polynomial.eval (1 : P (R := R) (σ := σ))) (mul_divide p hp)
  simpa only [Polynomial.eval_mul, Polynomial.eval_X, one_mul, scale_one] using h

private lemma scale_coeff_one [Fintype σ] (p : P (R := R) (σ := σ)) :
    (scale p).coeff 1 = ∑ i : σ, C (constantCoeff (pderiv i p)) * X i := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [scale]
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, hp, hq, map_add, Finset.sum_add_distrib,
      add_mul]
  | mul_X p j hp =>
    simp only [map_mul, scale, eval₂Hom_X', Polynomial.mul_coeff_one,
      zero_add, Polynomial.coeff_C_zero, Polynomial.coeff_C_succ, mul_zero]
    rw [← show scale p = eval₂Hom (Polynomial.C.comp C)
      (fun i ↦ Polynomial.X * Polynomial.C (X i)) p from rfl, scale_zero]
    simp only [Derivation.leibniz, map_add, map_mul, constantCoeff_X, mul_zero,
      smul_eq_mul, pderiv_X, Pi.single_apply, mul_one, zero_mul, add_zero,
      apply_ite, map_zero, ite_mul]
    simp

private lemma divide_zero [Fintype σ] (p : P (R := R) (σ := σ)) :
    (divide p).eval 0 = ∑ i : σ, C (constantCoeff (pderiv i p)) * X i := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, divide, Polynomial.coeff_divX]
  exact scale_coeff_one p

private def shift (b : σ → R) : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ) :=
  AlgEquiv.ofAlgHom (aeval (fun i ↦ X i + C (b i)))
    (aeval (fun i ↦ X i - C (b i)))
    (by ext i; simp) (by ext i; simp)

private lemma shift_X (b : σ → R) (i : σ) : shift b (X i) = X i + C (b i) := by
  simp [shift]

private lemma equiv_eval (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ))
    (p : P (R := R) (σ := σ)) : eval₂Hom C (fun i ↦ e (X i)) p = e p := by
  have h : eval₂Hom C (fun i ↦ e (X i)) = e.toRingHom :=
    MvPolynomial.ringHom_ext (fun r ↦ by
      rw [eval₂Hom_C]
      exact (e.commutes r).symm) (fun i ↦ by simp)
  exact DFunLike.congr_fun h p

private lemma equiv_zero (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ))
    (he : ∀ i, constantCoeff (e (X i)) = 0) (p : P (R := R) (σ := σ)) :
    constantCoeff (e p) = constantCoeff p := by
  have h : constantCoeff.comp e.toRingHom = constantCoeff :=
    MvPolynomial.ringHom_ext (fun r ↦ by
      change constantCoeff (e (C r)) = constantCoeff (C r)
      rw [show e (C r) = C r from e.commutes r])
      (fun i ↦ by simpa using he i)
  exact DFunLike.congr_fun h p

private lemma subst_comp (v w : σ → Q (R := R) (σ := σ)) :
    (subst v).comp (subst w) = subst (fun i ↦ subst v (w i)) := by
  apply Polynomial.ringHom_ext'
  · apply MvPolynomial.ringHom_ext
    · intro r
      simp [subst_C]
    · intro i
      simp [subst_C]
  · simp [subst_X]

private lemma subst_id :
    subst (fun i ↦ Polynomial.C (X i : P (R := R) (σ := σ))) = RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply MvPolynomial.ringHom_ext
    · intro r
      simp [subst_C]
    · intro i
      simp [subst_C]
  · simp [subst_X]

private lemma inverse_zero (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ))
    (he : ∀ i, constantCoeff (e (X i)) = 0) (i : σ) :
    constantCoeff (e.symm (X i)) = 0 := by
  rw [← equiv_zero e he (e.symm (X i)), e.apply_symm_apply]
  simp

private lemma divide_inverse (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ))
    (he : ∀ i, constantCoeff (e (X i)) = 0) :
    (subst (fun i ↦ divide (e (X i)))).comp
      (subst (fun i ↦ divide (e.symm (X i)))) = RingHom.id _ := by
  rw [subst_comp]
  rw [← subst_id (R := R) (σ := σ)]
  congr 1
  funext i
  rw [subst_divide _ he _ (inverse_zero e he i)]
  · rw [equiv_eval, e.apply_symm_apply, divide_X]
  · rw [equiv_eval, e.apply_symm_apply]
    simp

private def centeredFamily
    (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ))
    (he : ∀ i, constantCoeff (e (X i)) = 0) :
    Q (R := R) (σ := σ) ≃+* Q (R := R) (σ := σ) :=
  { (subst (fun i ↦ divide (e (X i)))) with
    invFun := subst (fun i ↦ divide (e.symm (X i)))
    left_inv := fun p ↦ DFunLike.congr_fun (divide_inverse e.symm (inverse_zero e he)) p
    right_inv := fun p ↦ DFunLike.congr_fun (divide_inverse e he) p }

private lemma subst_eval (v : σ → Q (R := R) (σ := σ)) (a : R)
    (p : Q (R := R) (σ := σ)) :
    (subst v p).eval (C a) =
      eval₂Hom C (fun i ↦ (v i).eval (C a)) (p.eval (C a)) := by
  have h : (Polynomial.evalRingHom (C a)).comp (subst v) =
      (eval₂Hom C (fun i ↦ (v i).eval (C a))).comp (Polynomial.evalRingHom (C a)) := by
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r
        simp [subst_C]
      · intro i
        simp [subst_C]
    · simp [subst_X]
  exact DFunLike.congr_fun h p

private def translation (b : σ → Q (R := R) (σ := σ))
    (hb : ∀ i v, subst v (b i) = b i) :
    Q (R := R) (σ := σ) ≃+* Q (R := R) (σ := σ) :=
  { subst (fun i ↦ Polynomial.C (X i) + b i) with
    invFun := subst (fun i ↦ Polynomial.C (X i) - b i)
    left_inv := by
      intro p
      have h : (subst (fun i ↦ Polynomial.C (X i) - b i)).comp
          (subst (fun i ↦ Polynomial.C (X i) + b i)) = RingHom.id _ := by
        rw [subst_comp, ← subst_id (R := R) (σ := σ)]
        congr 1
        funext i
        simp [subst_C, hb]
      exact DFunLike.congr_fun h p
    right_inv := by
      intro p
      have h : (subst (fun i ↦ Polynomial.C (X i) + b i)).comp
          (subst (fun i ↦ Polynomial.C (X i) - b i)) = RingHom.id _ := by
        rw [subst_comp, ← subst_id (R := R) (σ := σ)]
        congr 1
        funext i
        simp [subst_C, hb]
      exact DFunLike.congr_fun h p }

private def center (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ)) :
    P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ) :=
  (shift (fun i ↦ -constantCoeff (e (X i)))).trans e

private lemma center_X (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ))
    (i : σ) : center e (X i) = e (X i) - C (constantCoeff (e (X i))) := by
  have h (r : R) : e (C r) = C r := e.commutes r
  simp [center, shift_X, h, sub_eq_add_neg]

private lemma center_zero (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ))
    (i : σ) : constantCoeff (center e (X i)) = 0 := by
  simp [center_X]

/-- The actual translated rescaling family, with both inverse identities proved by
cancellation of the outer polynomial variable. -/
private def family (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ)) :
    Q (R := R) (σ := σ) ≃+* Q (R := R) (σ := σ) :=
  (translation (fun i ↦ Polynomial.X * Polynomial.C (C (constantCoeff (e (X i)))))
    (by intro i v; simp [map_mul, subst_X, subst_C])).trans
      (centeredFamily (center e) (center_zero e))

private lemma family_X (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ))
    (i : σ) : family e (Polynomial.C (X i)) =
      divide (center e (X i)) +
        Polynomial.X * Polynomial.C (C (constantCoeff (e (X i)))) := by
  simp [family, translation, centeredFamily, subst_C, subst_X]

/-- The rescaling is an automorphism over the parameter ring. -/
private theorem family_parameter (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ)) :
    family e Polynomial.X = Polynomial.X := by
  simp [family, translation, centeredFamily, subst_X]

/-- The rescaling fixes the original coefficient ring. -/
private theorem family_C (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ)) (r : R) :
    family e (Polynomial.C (C r)) = Polynomial.C (C r) := by
  simp [family, translation, centeredFamily, subst_C]

/-- The endpoint at one recovers the given polynomial automorphism. -/
private theorem family_one (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ)) (i : σ) :
    (family e (Polynomial.C (X i))).eval 1 = e (X i) := by
  rw [family_X, Polynomial.eval_add, divide_one _ (center_zero e i)]
  simp [center_X]

/-- The endpoint at zero is a homogeneous linear polynomial. -/
private theorem family_zero [Fintype σ]
    (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ)) (i : σ) :
    (family e (Polynomial.C (X i))).eval 0 =
      ∑ j : σ, C (constantCoeff (pderiv j (center e (X i)))) * X j := by
  simp [family_X, divide_zero]

private def jac [Fintype σ]
    (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ)) : Matrix σ σ R :=
  fun i j ↦ constantCoeff (pderiv j (e (X i)))

private lemma jac_inverse [Fintype σ] [DecidableEq σ]
    (e : P (R := R) (σ := σ) ≃ₐ[R] P (R := R) (σ := σ))
    (he : ∀ i, constantCoeff (e (X i)) = 0) : jac e.symm * jac e = 1 := by
  classical
  ext i j
  have h := DFunLike.congr_fun (divide_inverse e he) (Polynomial.C (X i))
  change subst (fun i ↦ divide (e (X i)))
    (subst (fun i ↦ divide (e.symm (X i))) (Polynomial.C (X i))) = Polynomial.C (X i) at h
  simp only [subst_C, eval₂Hom_X'] at h
  have h0 := congrArg (Polynomial.eval (0 : P (R := R) (σ := σ))) h
  rw [show (0 : P (R := R) (σ := σ)) = C (0 : R) by simp,
    subst_eval] at h0
  simp only [map_zero, divide_zero, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X',
    Polynomial.eval_C] at h0
  have h1 := congrArg (fun p : P (R := R) (σ := σ) ↦ constantCoeff (pderiv j p)) h0
  simp only [map_sum, pderiv_C_mul, map_mul, pderiv_X, Pi.single_apply,
    apply_ite, map_one, map_zero, mul_one, mul_zero] at h1
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  by_cases hij : i = j
  · simpa only [jac, Matrix.mul_apply, Matrix.one_apply, constantCoeff_C, hij,
      ite_true] using h1
  · simpa only [jac, Matrix.mul_apply, Matrix.one_apply, constantCoeff_C, hij,
      ite_false] using h1

/-- Translation followed by rescaling joins any polynomial automorphism to an
invertible linear map. Source: Furter--Poloni, Lemma 3.1, proof, pp. 5--6.
Proof: subtract the constant tuple, substitute t*x and divide by t. The inverse
is obtained by the same operation on the centered inverse; multiplication by t
reduces both inverse identities to those of the original automorphism. Add t*b
to restore the endpoint at one. The coefficient of t of a scaled polynomial is
its linear part. Applying the inverse identities at zero makes its matrix a unit.
(blueprint: lem-pur-polynomial-rescaling-family). -/
theorem exists_deformation [Fintype σ] [DecidableEq σ]
    (e : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) :
    ∃ (g : Matrix.GeneralLinearGroup σ R)
      (E : Polynomial (MvPolynomial σ R) ≃+* Polynomial (MvPolynomial σ R)),
      E Polynomial.X = Polynomial.X ∧
      (∀ r : R, E (Polynomial.C (C r)) = Polynomial.C (C r)) ∧
      (∀ i, (E (Polynomial.C (X i))).eval 1 = e (X i)) ∧
      (∀ i, (E (Polynomial.C (X i))).eval 0 = ∑ j : σ, C (g i j) * X j) := by
  classical
  let f := center e
  let g : Matrix.GeneralLinearGroup σ R :=
    ⟨jac f, jac f.symm,
      jac_inverse f.symm (inverse_zero f (center_zero e)), jac_inverse f (center_zero e)⟩
  exact ⟨g, family e, family_parameter e, family_C e, family_one e, family_zero e⟩

end MvPolynomial.Rescaling
