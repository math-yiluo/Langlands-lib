/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.RingTheory.FiniteGabberUpstairsRelation

@[expose] public section

universe u v w z

open scoped BigOperators

namespace Algebra

/-- Gabber's relation vanishes after a faithfully flat base change, in the quotient
by the finite coefficient submodule.
Source: Stacks Project, More on Algebra, Lemma Tag 0EM0, construction before descent.
(blueprint: lem-weil-pbc-zariski-pair-finite-gabber-polynomial-upstairs-relation)

Proof: Apply Tag 07M4 to lift the idempotent (1,0) over an etale A-algebra A' preserving
A/I. Split the finite base change of B using this idempotent. The first factor has
surjective structure map modulo IA'. Its finite cokernel is equal to IA' times itself;
Nakayama (00DV) gives g in 1+IA' annihilating it. Localize A' at g to obtain C, so the
first factor is a quotient of C and C/IC is still A/I. Lift the image of b-1 in that
factor to a' in IC. In the second factor the image of b belongs to the extended ideal;
00H5 gives a monic annihilator G congruent to a power of X. Multiply G by X to ensure
its degree d is positive, including when that factor is zero. Then (X-1-a')G
annihilates both components. Its difference from (X-1)X^d has degree at most d and
coefficients in IC. Thus the image of (b-1)b^d belongs to the C-submodule generated
by the images of i b^j, i in I, j at most d. This is the image of the base change of
the range of the coefficient map displayed below. Right exactness of tensor product
therefore kills the displayed class in C tensor (B/N). Finally C is flat over A
(etale followed by localization), and every maximal ideal contains I and has nonzero
fibre since C/IC is A/I. The maximal-ideal criterion (00HP) makes C faithfully flat.
No descent to B is asserted here; that is proved in the importing module. -/
theorem exists_gabber_relation_after_base_change
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (B₁ : Type w) (B₂ : Type z) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* (B₁ × B₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a)) =
      (algebraMap (A ⧸ I) B₁ (Ideal.Quotient.mk I a),
        algebraMap (A ⧸ I) B₂ (Ideal.Quotient.mk I a)))
    (h₁ : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B) (hb : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0)) :
    ∃ (C : CommRingCat.{u}) (f : A →+* C),
      letI : Algebra A C := f.toAlgebra;
      Module.FaithfullyFlat A C ∧ ∃ d : ℕ, 1 ≤ d ∧
        let L : (Fin (d + 1) → I) →ₗ[A] B :=
          ∑ j : Fin (d + 1), (I.subtype.comp (LinearMap.proj j)).smulRight (b ^ (j : ℕ));
        TensorProduct.mk A C (B ⧸ LinearMap.range L) 1
          ((LinearMap.range L).mkQ ((b - 1) * b ^ d)) = 0 := by
  classical
  obtain ⟨C, f, hC, d, hd, c, hc⟩ :=
    exists_gabber_upstairs_tensor_relation I hI B₁ B₂ e he h₁ b hb
  let : Algebra A C := f.toAlgebra
  refine ⟨C, f, hC, d, hd, ?_⟩
  let L : (Fin (d + 1) → I) →ₗ[A] B :=
    ∑ j : Fin (d + 1), (I.subtype.comp (LinearMap.proj j)).smulRight (b ^ (j : ℕ))
  let q := (LinearMap.range L).mkQ
  change q.lTensor C (TensorProduct.tmul A (1 : C) ((b - 1) * b ^ d)) = 0
  rw [hc, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hq : q.comp (I.subtype.smulRight (b ^ (j : ℕ))) = 0 := by
    ext i
    change Submodule.Quotient.mk _ = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    refine ⟨Pi.single j i, ?_⟩
    simp only [L, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [hkj]
    · simp
  rw [← LinearMap.lTensor_comp_apply, hq, LinearMap.lTensor_zero]
  rfl

end Algebra
