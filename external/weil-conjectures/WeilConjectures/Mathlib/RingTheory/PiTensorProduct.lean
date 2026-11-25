/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PiTensorProduct

/-!
# Algebra homomorphisms out of finite tensor products into commutative algebras

Given a finite family of `R`-algebras `Aᵢ`, a commutative `R`-algebra `S` and algebra
homomorphisms `fᵢ : Aᵢ → S`, we construct the induced algebra homomorphism `⨂ᵢ Aᵢ → S`,
`⨂ᵢ aᵢ ↦ ∏ᵢ fᵢ aᵢ`.
-/

@[expose] public section

open TensorProduct

namespace PiTensorProduct

variable {ι R S : Type*} {A : ι → Type*} [Fintype ι] [CommSemiring R] [∀ i, Semiring (A i)]
  [∀ i, Algebra R (A i)] [CommSemiring S] [Algebra R S]

/-- The algebra homomorphism `⨂ᵢ Aᵢ → S` into a commutative algebra `S` induced by a family of
algebra homomorphisms `Aᵢ → S`, sending `⨂ᵢ aᵢ` to `∏ᵢ fᵢ aᵢ`. -/
noncomputable def liftCommAlgHom (f : ∀ i, A i →ₐ[R] S) : (⨂[R] i, A i) →ₐ[R] S :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra R ι S).compLinearMap fun i ↦ (f i).toLinearMap)
    (by simp) (fun x y ↦ by simp [Finset.prod_mul_distrib])

@[simp]
lemma liftCommAlgHom_tprod (f : ∀ i, A i →ₐ[R] S) (x : Π i, A i) :
    liftCommAlgHom f (tprod R x) = ∏ i, f i (x i) := by
  simp [liftCommAlgHom]

@[simp]
lemma liftCommAlgHom_singleAlgHom [DecidableEq ι] (f : ∀ i, A i →ₐ[R] S) (i : ι) (a : A i) :
    liftCommAlgHom f (singleAlgHom i a) = f i a := by
  rw [singleAlgHom_apply, liftCommAlgHom_tprod, Fintype.prod_eq_single i fun j hj ↦ by
    simp [Pi.mulSingle_eq_of_ne hj]]
  simp

@[simp]
lemma liftCommAlgHom_comp_singleAlgHom [DecidableEq ι] (f : ∀ i, A i →ₐ[R] S) (i : ι) :
    (liftCommAlgHom f).comp (singleAlgHom i) = f i :=
  AlgHom.ext fun a ↦ liftCommAlgHom_singleAlgHom f i a

end PiTensorProduct

end
