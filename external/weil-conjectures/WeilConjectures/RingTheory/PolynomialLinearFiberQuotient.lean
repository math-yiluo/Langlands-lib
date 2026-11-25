/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Linear polynomial fibres after arbitrary base change

Source: Stacks Project, More on Algebra, Tag 07PU, second paragraph of the proof.
(blueprint: lem-weil-pbc-polynomial-linear-fibre-quotient)
-/

@[expose] public section

universe u

namespace Polynomial

set_option backward.isDefEq.respectTransparency false in
/-- The fibre of a polynomial prime whose residue field is the coefficient fraction field
is the quotient of the coefficient generic fibre by the explicit linear relation.
Source: Stacks Project, More on Algebra, Tag 07PU, second paragraph of the proof.
(blueprint: lem-weil-pbc-polynomial-linear-fibre-quotient)

Proof:
Put K = κ(0_A), and identify κ(r) with K by the unique A-algebra isomorphism
of fraction fields. Let ξ be the image of X under this isomorphism. Put R = K tensor
with S over A, and Q = R/(1 tensor X - ξ tensor 1). The canonical maps κ(r) to Q
and S to Q agree on A. They agree on X by the defining relation of Q, so polynomial
algebra-map extensionality says that they agree on all of A[X]. The tensor universal
property therefore gives a map κ(r) tensor over A[X] with S to Q. Conversely, the
fraction-field isomorphism and the canonical map from S give a map from R to that
fibre. The balancing relation for X kills the displayed generator, so this map
descends to Q. The maps are inverse: check on pure tensors, using the inverse laws
of the fraction-field isomorphism, and then use additivity and quotient induction.
This proves the presentation even for the zero ring S or a zero fibre; no regularity,
completion or derivation is involved. -/
theorem linear_fiber_quotient
    (A : Type u) [CommRing A] [IsDomain A]
    (r : Ideal (Polynomial A)) [r.IsPrime] [IsFractionRing A r.ResidueField]
    (S : Type u) [CommRing S] [Algebra (Polynomial A) S] [Algebra A S]
    [IsScalarTower A (Polynomial A) S] :
    let K := (⊥ : Ideal A).ResidueField
    let R := (⊥ : Ideal A).Fiber S
    let e : r.ResidueField ≃ₐ[A] K :=
      IsLocalization.algEquiv (nonZeroDivisors A) r.ResidueField K
    let ξ := e (algebraMap (Polynomial A) r.ResidueField X)
    let f : R := Algebra.TensorProduct.includeRight (algebraMap (Polynomial A) S X) -
      Algebra.TensorProduct.includeLeft (S := A) ξ
    Nonempty ((R ⧸ Ideal.span ({f} : Set R)) ≃+* r.Fiber S)  := by
  classical
  let K := (⊥ : Ideal A).ResidueField
  let R := (⊥ : Ideal A).Fiber S
  let T := r.Fiber S
  let e : r.ResidueField ≃ₐ[A] K :=
    IsLocalization.algEquiv (nonZeroDivisors A) r.ResidueField K
  let ξ := e (algebraMap (Polynomial A) r.ResidueField X)
  let f : R := Algebra.TensorProduct.includeRight (algebraMap (Polynomial A) S X) -
    Algebra.TensorProduct.includeLeft (S := A) ξ
  let I := Ideal.span ({f} : Set R)
  let Q := R ⧸ I
  let il : K →ₐ[A] R := Algebra.TensorProduct.includeLeft
  let ir : S →ₐ[A] R := Algebra.TensorProduct.includeRight
  let tl : r.ResidueField →ₐ[A] T := Algebra.TensorProduct.includeLeft
  let tr : S →ₐ[A] T := Algebra.TensorProduct.includeRight.restrictScalars A
  let g : R →ₐ[A] T := Algebra.TensorProduct.lift
    (tl.comp e.symm.toAlgHom) tr (fun _ _ ↦ .all _ _)
  have gg (k : K) (s : S) : g (k ⊗ₜ[A] s) = tl (e.symm k) * tr s := by
    exact Algebra.TensorProduct.lift_tmul _ _ _ k s
  have gf : g f = 0 := by
    simp only [f, map_sub]
    simp only [Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.includeLeft_apply, gg, map_one, mul_one, one_mul]
    change tr (algebraMap (Polynomial A) S X) -
      tl (e.symm (e (algebraMap (Polynomial A) r.ResidueField X))) = 0
    rw [e.symm_apply_apply]
    change (1 : r.ResidueField) ⊗ₜ[Polynomial A] (algebraMap (Polynomial A) S X) -
      (algebraMap (Polynomial A) r.ResidueField X) ⊗ₜ[Polynomial A] (1 : S) = 0
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, sub_self]
  let gq : Q →ₐ[A] T := Ideal.Quotient.liftₐ I g (by
    intro z hz
    exact (show I ≤ RingHom.ker g.toRingHom from
      Ideal.span_le.mpr (by
        intro z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        change g f = 0
        exact gf)) hz)
  let ql : K →ₐ[A] Q := (Ideal.Quotient.mkₐ A I).comp il
  let qr : S →ₐ[A] Q := (Ideal.Quotient.mkₐ A I).comp ir
  have rel : qr (algebraMap (Polynomial A) S X) =
      ql (e (algebraMap (Polynomial A) r.ResidueField X)) := by
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk I f = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))
  let : Algebra (Polynomial A) Q :=
    ((Ideal.Quotient.mk I).comp ir.toRingHom |>.comp (algebraMap (Polynomial A) S)).toAlgebra
  have : IsScalarTower A (Polynomial A) Q := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change _ = qr (algebraMap (Polynomial A) S (C a))
    rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply A (Polynomial A) S]
    exact (qr.commutes a).symm
  let η : r.ResidueField →ₐ[Polynomial A] Q :=
    { toRingHom := (ql.comp e.toAlgHom).toRingHom
      commutes' := by
        intro p
        have h : (ql.comp e.toAlgHom).comp (IsScalarTower.toAlgHom A (Polynomial A)
            r.ResidueField) = qr.comp (IsScalarTower.toAlgHom A (Polynomial A) S) := by
          apply Polynomial.algHom_ext
          exact rel.symm
        exact congrArg (fun h : Polynomial A →ₐ[A] Q ↦ h p) h }
  let σ : S →ₐ[Polynomial A] Q :=
    { toRingHom := qr.toRingHom
      commutes' := fun _ ↦ rfl }
  let h : T →ₐ[Polynomial A] Q :=
    Algebra.TensorProduct.lift η σ (fun _ _ ↦ .all _ _)
  have hh (k : r.ResidueField) (s : S) :
      h (k ⊗ₜ[Polynomial A] s) = ql (e k) * qr s := by
    exact Algebra.TensorProduct.lift_tmul _ _ _ k s
  have gq_mk (z : R) : gq (Ideal.Quotient.mk I z) = g z := rfl
  refine ⟨{ gq.toRingHom with
    invFun := h
    left_inv := ?_
    right_inv := ?_ }⟩
  · intro z
    induction z using Quotient.inductionOn' with
    | _ z =>
      change h (gq (Ideal.Quotient.mk I z)) = Ideal.Quotient.mk I z
      change h (g z) = Ideal.Quotient.mk I z
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simp [hz, hw]
      | tmul k s =>
        rw [gg]
        change h ((e.symm k ⊗ₜ[Polynomial A] 1) * (1 ⊗ₜ[Polynomial A] s)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hh]
        rw [e.apply_symm_apply]
        change Ideal.Quotient.mk I (k ⊗ₜ[A] 1) *
          Ideal.Quotient.mk I (1 ⊗ₜ[A] s) = _
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  · intro z
    change gq (h z) = z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul k s =>
      rw [hh]
      change gq (Ideal.Quotient.mk I (e k ⊗ₜ[A] 1) *
        Ideal.Quotient.mk I (1 ⊗ₜ[A] s)) = _
      rw [← map_mul, gq_mk, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, gg]
      rw [e.symm_apply_apply]
      change (k ⊗ₜ[Polynomial A] 1) * (1 ⊗ₜ[Polynomial A] s) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Polynomial
