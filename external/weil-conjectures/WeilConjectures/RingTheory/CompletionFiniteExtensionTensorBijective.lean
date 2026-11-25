/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.CompletionFiniteExtensionTensorMap
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

private theorem finiteTensorBijective
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Function.Bijective (ofTensorProduct I M) := by
  let : Small.{u} M := Module.Finite.small A M
  let e := Shrink.linearEquiv A M
  have h := ofTensorProduct_bijective_of_finite_of_isNoetherian I (Shrink.{u} M)
  let t := TensorProduct.congr (LinearEquiv.refl A (AdicCompletion I A)) e
  let c := congr I e
  have heq : (ofTensorProduct I M : _ → _) ∘ t = c ∘ ofTensorProduct I (Shrink.{u} M) := by
    funext x
    change (ofTensorProduct I M) (t x) = c ((ofTensorProduct I (Shrink.{u} M)) x)
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [t, c, congr_apply, map_of]
    | add x y hx hy => simp_all
  exact (Function.Bijective.of_comp_iff _ t.bijective).mp (heq ▸ c.bijective.comp h)

private def completionQuotientEquiv
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) :
    (B ⧸ (I ^ n • ⊤ : Submodule A B)) ≃ₗ[A]
      B ⧸ ((I.map (algebraMap A B)) ^ n • ⊤ : Ideal B) :=
  (Submodule.quotEquivOfEq _ _ (by
    simp only [Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow, Ideal.smul_top_eq_map])).trans
    (Submodule.Quotient.restrictScalarsEquiv A _)

private theorem completionQuotientEquiv_mk
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) (b : B) :
    completionQuotientEquiv A B I n (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk b := by
  simp [completionQuotientEquiv]
  rfl

private theorem completionQuotientEquiv_transition
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {i j : ℕ} (h : i ≤ j)
    (x : B ⧸ (I ^ j • ⊤ : Submodule A B)) :
    transitionMap (I.map (algebraMap A B)) B h (completionQuotientEquiv A B I j x) =
      completionQuotientEquiv A B I i (transitionMap I B h x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ b => simp only [completionQuotientEquiv_mk]; rfl

private def mapCompletionEquiv
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) : AdicCompletion I B ≃ₗ[A] AdicCompletion (I.map (algebraMap A B)) B where
  toFun x := ⟨fun n ↦ completionQuotientEquiv A B I n (x.val n), by
    intro i j h
    rw [completionQuotientEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n ↦ (completionQuotientEquiv A B I n).symm (x.val n), by
    intro i j h
    apply (completionQuotientEquiv A B I i).injective
    rw [← completionQuotientEquiv_transition]
    simp only [LinearEquiv.apply_symm_apply, x.property h]⟩
  left_inv x := by ext n; exact LinearEquiv.symm_apply_apply _ _
  right_inv x := by ext n; exact LinearEquiv.apply_symm_apply _ _
  map_add' x y := by ext n; exact map_add _ _ _
  map_smul' a x := by
    ext n
    exact (completionQuotientEquiv A B I n).map_smul a (x.val n)

private theorem mapCompletionEquiv_eval_smul_of
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) (c : AdicCompletion I A) (b : B) :
    evalₐ (I.map (algebraMap A B)) n (mapCompletionEquiv A B I (c • of I B b)) =
      Ideal.quotientMapₐ ((I.map (algebraMap A B)) ^ n) (Algebra.ofId A B)
        (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
        (evalₐ I n c) * Ideal.Quotient.mk _ b := by
  change (Ideal.quotientEquivAlgOfEq B (by simp)) (completionQuotientEquiv A B I n
      ((c • of I B b).val n)) =
    Ideal.quotientMapₐ _ (Algebra.ofId A B)
      (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
      ((Ideal.quotientEquivAlgOfEq A (by simp)) (c.val n)) * Ideal.Quotient.mk _ b
  rw [smul_eval, of_apply]
  generalize c.val n = z
  induction z using Submodule.Quotient.induction_on with
  | _ a =>
    change (Ideal.quotientEquivAlgOfEq B (by simp)) (completionQuotientEquiv A B I n
      (Submodule.Quotient.mk (a • b))) = _
    rw [completionQuotientEquiv_mk]
    simp [Algebra.smul_def]
    congr 1

private def mapCompletionEquivOfEq
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (J : Ideal B) (h : I.map (algebraMap A B) = J) :
    AdicCompletion I B ≃ₗ[A] AdicCompletion J B := by
  subst J
  exact mapCompletionEquiv A B I

private theorem mapCompletionEquivOfEq_eval_smul_of
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (J : Ideal B) (h : I.map (algebraMap A B) = J)
    (n : ℕ) (c : AdicCompletion I A) (b : B) :
    evalₐ J n (mapCompletionEquivOfEq A B I J h (c • of I B b)) =
      Ideal.quotientMapₐ (J ^ n) (Algebra.ofId A B)
        (by rw [← h, ← Ideal.map_pow]; exact Ideal.le_comap_map)
        (evalₐ I n c) * Ideal.Quotient.mk _ b := by
  subst J
  exact mapCompletionEquiv_eval_smul_of A B I n c b

/-- The explicitly constructed completed tensor map is bijective.
Source: Stacks Project, Algebra, Lemma 10.97.8 (Tag 07N9), first equality, using
Lemma 10.97.1 (Tag 00MA), part (3).
(blueprint: new-completion-finite-extension-tensor-bijective)

Proof: Put A = R_p, m = pA, C = the m-adic completion of A, and B = A tensor_R S.
Localization preserves Noetherianity, so A is Noetherian. Base change of a finite
module is finite, so B is finite over A. The finite-module completion theorem
(`AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`) identifies
C tensor_A B with the m-adic module completion of B (first shrink the finite
A-module B into the universe of A if needed by the Mathlib theorem). Tensor associativity and
C tensor_A A = C identify C tensor_A (A tensor_R S) with C tensor_R S.
For every n, the submodule m^n B is the underlying A-submodule of the ideal J^n,
since m = pA and J = pB = mB, and extension of ideals commutes with powers.
Thus the identity on B induces compatible bijections between the quotients
B/(m^n B) and B/J^n. Their inverse limits give a bijection from the m-adic module
completion of B to the J-adic ring completion of B. The composite of these three
bijections is the map in the conclusion: on a pure tensor c tensor s, its nth
coordinate is the image of c_n multiplied by the image of 1 tensor s in B/J^n,
which is exactly the quotient-level construction of completionFiniteExtensionTensorMap.
Pure tensors generate the tensor product additively, so the maps agree everywhere.
The displayed map is therefore bijective. -/
theorem completion_finite_extension_tensor_bijective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    Function.Bijective (completionFiniteExtensionTensorMap R S p) := by
  let A := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal A
  let C := AdicCompletion m A
  let B := A ⊗[R] S
  let J := p.map (algebraMap R B)
  have hJ : m.map (algebraMap A B) = J := by
    rw [show m = p.map (algebraMap R A) from
      (Localization.AtPrime.map_eq_maximalIdeal (I := p)).symm, Ideal.map_map]
    congr 1
  let e := mapCompletionEquivOfEq A B m J hJ
  let t := (TensorProduct.AlgebraTensorModule.cancelBaseChange R A C C S).symm
  have heq : (completionFiniteExtensionTensorMap R S p : _ → _) =
      fun x ↦ e (ofTensorProduct m B (t x)) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp_all only [map_add]
    | tmul c s =>
      apply ext_evalₐ
      intro n
      dsimp only [t, e]
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
        ofTensorProduct_tmul, mapCompletionEquivOfEq_eval_smul_of]
      simp only [completionFiniteExtensionTensorMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        Algebra.TensorProduct.commRight_symm_tmul, AlgHom.liftEquiv_tmul,
        Algebra.smul_def, map_mul, evalₐ_liftAlgHom]
      rw [algebraMap_apply, evalₐ_of]
      change Ideal.Quotient.mk (J ^ n) (1 ⊗ₜ[R] s) *
          Ideal.quotientMapₐ (J ^ n) (Algebra.ofId A B)
            (by rw [← hJ, ← Ideal.map_pow]; exact Ideal.le_comap_map)
            (evalₐ m n c) = _
      exact mul_comm _ _
  rw [heq]
  exact e.bijective.comp ((finiteTensorBijective A m B).comp t.bijective)

end AdicCompletion
