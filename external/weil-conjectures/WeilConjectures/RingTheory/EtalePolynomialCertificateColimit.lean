/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EtalePolynomialCertificate
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.TensorPolynomialEquationsColimit
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Descent of finite polynomial inverse certificates

Source: Stacks Project, Algebra, proof of Tag 07RI, descent of inverse identities.
(blueprint: lem-weil-pbc-etale-polynomial-certificate-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

private theorem square_span_range {R : Type*} [CommRing R] {ι : Type*}
    (f : ι → R) :
    (Ideal.span (Set.range f)) ^ 2 =
      Ideal.span (Set.range (fun ab : ι × ι ↦ f ab.1 * f ab.2)) := by
  rw [pow_two, Ideal.span_mul_span]
  congr 1
  ext x
  simp only [Set.mem_mul, Set.mem_range, Prod.exists]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    exact ⟨i, j, rfl⟩
  · rintro ⟨i, j, rfl⟩
    exact ⟨f i, ⟨i, rfl⟩, f j, ⟨j, rfl⟩, rfl⟩

private theorem certificate_iff_equations {R : Type*} [CommRing R] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) R) :
    EtalePolynomialCertificate f ↔
      ∃ (c : Fin m → Fin n → MvPolynomial (Fin n) R)
        (e : Fin n → Fin n → Fin m → MvPolynomial (Fin n) R)
        (h : Fin m → (Fin m × Fin m) → MvPolynomial (Fin n) R),
        (∀ k l, (∑ j, c j k * MvPolynomial.pderiv l (f j)) -
          (if k = l then 1 else 0) - ∑ j, e k l j * f j = 0) ∧
        (∀ j, (∑ k, MvPolynomial.pderiv k (f j) * ∑ j', c j' k * f j') - f j -
          ∑ ab, h j ab * (f ab.1 * f ab.2) = 0) := by
  classical
  unfold EtalePolynomialCertificate
  simp_rw [square_span_range, Ideal.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, he, hh⟩
    choose e he using he
    choose h hh using hh
    exact ⟨c, e, h, fun k l ↦ sub_eq_zero.mpr (he k l).symm,
      fun j ↦ sub_eq_zero.mpr (hh j).symm⟩
  · rintro ⟨c, e, h, he, hh⟩
    exact ⟨c, (fun k l ↦ ⟨e k l, (sub_eq_zero.mp (he k l)).symm⟩),
      fun j ↦ ⟨h j, (sub_eq_zero.mp (hh j)).symm⟩⟩

/-- A finite polynomial inverse certificate for fixed relations descends to a stage.
This concerns polynomial equations and ideal memberships, and makes no assertion
about etaleness or about a presented target algebra.

Source: Stacks Project, Algebra, proof of Tag 07RI, lines 47654-47662.
(blueprint: lem-weil-pbc-etale-polynomial-certificate-colimit).

Proof: expand each membership in the relation ideal as a sum e_klj f_j, and each
membership in its square as a sum h_jab f_a f_b. There are finitely many polynomials
c, e and h in finitely many variables. Polynomial scalar extension identifies the
coefficient-base-changed polynomial algebra with T tensor P₀, where
P₀ = B₀[x₁,...,x_n]. Elementwise tensor-colimit descent represents every one of
these polynomials at a stage. Directedness places these representatives together
above i₀. Coefficientwise transition maps preserve f_j and commute with partial
derivatives. Thus the finitely many differences between the two sides of the
expanded equations map to zero at the colimit. Elementwise eventual vanishing
and directedness kill all these differences at one later stage. The resulting
c, e and h give the two required ideal memberships there. When either finite
index set is empty, no coefficients or equations need lifting; i₀ suffices for
an empty list and the same construction handles the remaining equations. -/
theorem exists_stage_etalePolynomialCertificate
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ : Type v) [CommRing B₀] [Algebra (F.obj i₀) B₀]
    (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) B₀) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (colimit.ι F i₀).hom.toAlgebra
    EtalePolynomialCertificate
      (fun j ↦ MvPolynomial.map
        (Algebra.TensorProduct.includeRight.toRingHom :
          B₀ →+* (colimit F : CommRingCat.{u}) ⊗[F.obj i₀] B₀) (f j)) →
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
      EtalePolynomialCertificate
        (fun j ↦ MvPolynomial.map
          (Algebra.TensorProduct.includeRight.toRingHom :
            B₀ →+* F.obj i ⊗[F.obj i₀] B₀) (f j)) := by
  classical
  let : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
    (colimit.ι F i₀).hom.toAlgebra
  intro hc
  let V := (Fin m × Fin n) ⊕ ((Fin n × Fin n × Fin m) ⊕ (Fin m × (Fin m × Fin m)))
  let E := (Fin n × Fin n) ⊕ Fin m
  let C (j : Fin m) (k : Fin n) : MvPolynomial V (MvPolynomial (Fin n) B₀) :=
    MvPolynomial.X (.inl (j, k))
  let D (k l : Fin n) (j : Fin m) : MvPolynomial V (MvPolynomial (Fin n) B₀) :=
    MvPolynomial.X (.inr (.inl (k, l, j)))
  let H (j : Fin m) (ab : Fin m × Fin m) :
      MvPolynomial V (MvPolynomial (Fin n) B₀) :=
    MvPolynomial.X (.inr (.inr (j, ab)))
  let q : E → MvPolynomial V (MvPolynomial (Fin n) B₀) := fun b ↦
    match b with
    | .inl (k, l) =>
      (∑ j, C j k * MvPolynomial.C (MvPolynomial.pderiv l (f j))) -
        (if k = l then 1 else 0) - ∑ j, D k l j * MvPolynomial.C (f j)
    | .inr j =>
      (∑ k, MvPolynomial.C (MvPolynomial.pderiv k (f j)) *
        ∑ j', C j' k * MvPolynomial.C (f j')) - MvPolynomial.C (f j) -
        ∑ ab, H j ab * (MvPolynomial.C (f ab.1) * MvPolynomial.C (f ab.2))
  obtain ⟨c, e, h, he, hh⟩ := (certificate_iff_equations _).mp hc
  let x : V → MvPolynomial (Fin n) ((colimit F : CommRingCat.{u}) ⊗[F.obj i₀] B₀) :=
    fun a ↦ match a with
    | .inl (j, k) => c j k
    | .inr (.inl (k, l, j)) => e k l j
    | .inr (.inr (j, ab)) => h j ab
  have hx : ∀ b, MvPolynomial.eval₂Hom
      (MvPolynomial.map (Algebra.TensorProduct.includeRight.toRingHom :
        B₀ →+* (colimit F : CommRingCat.{u}) ⊗[F.obj i₀] B₀)) x (q b) = 0 := by
    intro b
    cases b with
    | inl kl =>
      rcases kl with ⟨k, l⟩
      simpa [q, C, D, x, MvPolynomial.pderiv_map, MvPolynomial.eval₂_sub,
        MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, apply_ite] using he k l
    | inr j =>
      simpa [q, C, H, x, MvPolynomial.pderiv_map, MvPolynomial.eval₂_sub,
        MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, apply_ite] using hh j
  obtain ⟨i, hi, y, hy⟩ :=
    exists_stage_tensorPolynomialEquations F i₀ B₀ n q ⟨x, hx⟩
  let : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
  refine ⟨i, hi, (certificate_iff_equations _).mpr ?_⟩
  refine ⟨(fun j k ↦ y (.inl (j, k))),
    (fun k l j ↦ y (.inr (.inl (k, l, j)))),
    (fun j ab ↦ y (.inr (.inr (j, ab)))), ?_, ?_⟩
  · intro k l
    simpa [q, C, D, MvPolynomial.pderiv_map, MvPolynomial.eval₂_sub,
        MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, apply_ite] using hy (.inl (k, l))
  · intro j
    simpa [q, C, H, MvPolynomial.pderiv_map, MvPolynomial.eval₂_sub,
        MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, apply_ite] using hy (.inr j)

end Algebra
