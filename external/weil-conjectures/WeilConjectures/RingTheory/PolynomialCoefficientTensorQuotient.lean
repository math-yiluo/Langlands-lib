/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Polynomial coefficient tensors as a quotient of the coefficient kernel

Source: Stacks Project, Algebra, Tag 00S2, proof of lemma-exact-sequence-NL;
More on Algebra, Tag 07D4, proof of lemma-transitive-lci-at-end.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

private theorem coefficient_tensor_bijective
    (P : Type u) [CommRing P] (I : Ideal P) (m : ℕ) :
    Function.Bijective ((Algebra.idealMap (MvPolynomial (Fin m) P) I).liftBaseChange
      (MvPolynomial (Fin m) P)) := by
  let Q := MvPolynomial (Fin m) P
  let F := (Algebra.idealMap Q I).liftBaseChange Q
  have hinj : Function.Injective F := by
    let t := (TensorProduct.AlgebraTensorModule.rid P Q Q).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor Q Q I.subtype)
    have ht : (I.map (algebraMap P Q)).subtype.comp F = t := by
      ext q x
      simp [F, t, Algebra.smul_def]
    apply Function.Injective.of_comp (f := (I.map (algebraMap P Q)).subtype)
    rw [← LinearMap.coe_comp, ht, LinearMap.coe_comp]
    exact (TensorProduct.AlgebraTensorModule.rid P Q Q).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap I.subtype I.subtype_injective)
  refine ⟨hinj, ?_⟩
  intro x
  have hx : x.1 ∈ Ideal.span ((algebraMap P Q) '' (I : Set P)) := x.2
  have hr : ∀ q ∈ Ideal.span ((algebraMap P Q) '' (I : Set P)),
      ∀ hq : q ∈ I.map (algebraMap P Q), (⟨q, hq⟩ : I.map (algebraMap P Q)) ∈ F.range := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨x, hx, rfl⟩
      intro _
      exact ⟨1 ⊗ₜ[P] (⟨x, hx⟩ : I), by simp [F]; rfl⟩
    | zero =>
      intro _
      exact ⟨0, by simp; rfl⟩
    | add q r hq hr hqr hrr =>
      intro h
      obtain ⟨a, ha⟩ := hqr hq
      obtain ⟨b, hb⟩ := hrr hr
      exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
    | smul a q hq hqr =>
      intro _
      obtain ⟨b, hb⟩ := hqr hq
      exact ⟨a • b, by rw [map_smul, hb]; rfl⟩
  exact hr x x.2 x.2

/-- The coefficient expansion and quotient tensor identifications identify the base changed
conormal module with the coefficient kernel modulo its product with the presentation kernel.
Source: Stacks Project, Algebra, Tag 00S2, proof of lemma-exact-sequence-NL;
More on Algebra, Tag 07D4, proof of lemma-transitive-lci-at-end.
(blueprint: lem-weil-pbc-polynomial-coefficient-tensor-quotient)

Proof. Write Q = P[y], A = P/I, H = ker(Q → A[y]), and J = ker φ.
A polynomial belongs to H precisely when all its coefficients belong to I.
The map Q tensor_P I → H sends q tensor x to q C(x); its inverse sends a
polynomial to the finite sum of its monomials tensor their coefficients in I.
These are inverse Q-linear maps, by coefficient comparison and tensor balancing.
Tensor this equivalence with C over Q. Tensor associativity and cancellation identify
C tensor_Q H with C tensor_P I. Since C is an A-module, cancellation over A and
the quotient tensor equivalence A tensor_P I = I/I² identify the latter with
C tensor_A (I/I²). Finally Q/J = C via φ, so the quotient tensor equivalence identifies
C tensor_Q H with H/JH. All maps send c tensor [x] to the class of a lift of c
multiplied by C(x). Two lifts differ in J and give the same class modulo JH.
These computations prove the displayed formula and Q-linearity. They require neither
flatness of C nor projectivity of I. For I = P, compatibility forces C to be the zero
ring and both sides vanish; for no variables, coefficient expansion is the identity. -/
theorem polynomial_coefficient_tensor_quotient
    (P : Type u) [CommRing P] (I : Ideal P) (m : ℕ)
    (C : Type v) [CommRing C] [Algebra (P ⧸ I) C]
    (α : MvPolynomial (Fin m) (P ⧸ I) →ₐ[P ⧸ I] C)
    (φ : MvPolynomial (Fin m) P →+* C)
    (hφeq : φ = α.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk I)))
    (hφ : Function.Surjective φ) :
    let E := Extension.ofSurjective φ.toIntAlgHom hφ
    let H := RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m))
    ∃ (e : C ⊗[P ⧸ I] I.Cotangent ≃ₗ[E.Ring]
        H ⧸ (E.ker • (⊤ : Submodule E.Ring H))),
      ∀ (c : C) (x : I) (y : H), y.1 = MvPolynomial.C x.1 →
        e (c ⊗ₜ I.toCotangent x) = Submodule.Quotient.mk (E.σ c • y) := by
  classical
  let E := Extension.ofSurjective φ.toIntAlgHom hφ
  let Q := MvPolynomial (Fin m) P
  let A := P ⧸ I
  let J : Ideal Q := RingHom.ker φ
  let H : Ideal Q := RingHom.ker
    (MvPolynomial.map (Ideal.Quotient.mk I) (σ := Fin m))
  let : Algebra Q C := E.algebra₂
  let : Algebra P C := Algebra.compHom C (Ideal.Quotient.mk I)
  let : IsScalarTower P A C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P Q C := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap A C (Ideal.Quotient.mk I x) = φ (MvPolynomial.C x)
    symm
    rw [hφeq]
    simp
    rfl
  have hH : I.map (algebraMap P Q) = H := by
    dsimp [H, Q, E]
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  let eH : Q ⊗[P] I ≃ₗ[Q] H :=
    (LinearEquiv.ofBijective ((Algebra.idealMap Q I).liftBaseChange Q)
      (coefficient_tensor_bijective P I m)) ≪≫ₗ LinearEquiv.ofEq _ _ hH
  let eI : A ⊗[P] I ≃ₗ[A] I.Cotangent :=
    (TensorProduct.quotTensorEquivQuotSMul I I).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let eP : C ⊗[A] I.Cotangent ≃ₗ[C] C ⊗[P] I :=
    TensorProduct.AlgebraTensorModule.congr (.refl C C) eI.symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange P A C C I
  let eCH : C ⊗[Q] H ≃ₗ[C] C ⊗[P] I :=
    TensorProduct.AlgebraTensorModule.congr (.refl C C) eH.symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange P Q C C I
  let eQC : (Q ⧸ J) ≃ₗ[Q] C :=
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId Q C) E.algebraMap_surjective).toLinearEquiv
  let eQ : C ⊗[Q] H ≃ₗ[Q] H ⧸ (J • (⊤ : Submodule Q H)) :=
    _root_.TensorProduct.congr eQC.symm (LinearEquiv.refl Q H) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul H J
  let e := (eP ≪≫ₗ eCH.symm).restrictScalars Q ≪≫ₗ eQ
  refine ⟨e, ?_⟩
  intro c x y hy
  have heI : eI.symm (I.toCotangent x) = 1 ⊗ₜ[P] x := by
    exact TensorProduct.quotTensorEquivQuotSMul_symm_mk I x
  have heH : eH (1 ⊗ₜ[P] x) = y := by
    apply Subtype.ext
    dsimp only [eH, LinearEquiv.trans_apply]
    rw [LinearEquiv.coe_ofEq_apply]
    change ((Algebra.idealMap Q I).liftBaseChange Q (1 ⊗ₜ[P] x)).1 = y.1
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    exact hy.symm
  have heP : eP (c ⊗ₜ I.toCotangent x) = c ⊗ₜ[P] x := by
    simp [eP, heI]
  have heCH : eCH (c ⊗ₜ[Q] y) = c ⊗ₜ[P] x := by
    have h : eH.symm y = 1 ⊗ₜ[P] x := eH.symm_apply_eq.mpr heH.symm
    simp [eCH, h]
  have heQC : eQC.symm c = Ideal.Quotient.mk J (E.σ c) := by
    apply eQC.injective
    rw [eQC.apply_symm_apply]
    change c = φ (E.σ c)
    exact (E.algebraMap_σ c).symm
  change eQ ((eCH.symm) (eP (c ⊗ₜ I.toCotangent x))) = _
  rw [heP, ← heCH, eCH.symm_apply_apply]
  simp [eQ, heQC]
  rfl

end Algebra
