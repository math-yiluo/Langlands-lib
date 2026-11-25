/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.Derivation.Localization
import WeilConjectures.RingTheory.PolynomialLinearFiberQuotient

/-!
# Linear polynomial formal fibres as hypersurfaces

Source: Stacks Project, More on Algebra, proof of Lemma 07PU, second paragraph.
(blueprint: lem-weil-pbc-polynomial-linear-formal-fibre-presentation)
-/

@[expose] public section

universe u

namespace Polynomial

private theorem extend_absolute_derivation {B S : Type u} [CommRing B] [CommRing S]
    [Algebra B S] (W : Submonoid B) [IsLocalization W S] (D : Derivation ℤ B B) :
    ∃ Ds : Derivation ℤ S S,
      ∀ b, Ds (algebraMap B S b) = algebraMap B S (D b) := by
  let ψ : S →+* S := RingHom.id S
  let δ : B →+ S := (algebraMap B S).toAddMonoidHom.comp
    D.toLinearMap.toAddMonoidHom
  have hδ : ∀ x y, δ (x * y) = ψ (algebraMap B S x) • δ y +
      ψ (algebraMap B S y) • δ x := by
    intro x y
    change algebraMap B S (D (x * y)) = _
    rw [D.leibniz]
    simp [δ, ψ, smul_eq_mul]
  let d : S →+ S := IsLocalization.extendDerivation W ψ δ hδ
  let Ds : Derivation ℤ S S :=
    { toFun := d
      map_add' := d.map_add
      map_smul' := by
        intro n x
        rw [Algebra.smul_def]
        simpa using d.map_zsmul n x
      map_one_eq_zero' := by
        have h := IsLocalization.extendDerivation_mul W ψ δ hδ 1 1
        simp only [ψ, RingHom.id_apply, one_smul, one_mul] at h
        exact add_eq_left.mp h.symm
      leibniz' := by
        intro x y
        simpa [d, ψ, smul_eq_mul] using
          IsLocalization.extendDerivation_mul W ψ δ hδ x y }
  exact ⟨Ds, fun b ↦ IsLocalization.extendDerivation_algebraMap W ψ δ hδ b⟩

/-- If the residue field of a polynomial prime above zero is a fraction field of the
coefficient domain, its completed fibre is a hypersurface with derivative one in the
coefficient generic fibre.
Source: Stacks Project, More on Algebra, proof of Lemma 07PU, second paragraph.
(blueprint: lem-weil-pbc-polynomial-linear-formal-fibre-presentation)

Proof:
Set K = κ(0_A), and use the canonical fraction-field isomorphism e : κ(r) → K.
Write ξ = e(X), x for the image of X in C, and f = 1 tensor x - ξ tensor 1.
The general linear-fibre quotient theorem gives R/(f) ≃ κ(r) tensor over A[X] with C:
it constructs inverse tensor maps using the single relation X = ξ. Extend d/dX first
to A[X]_q using the localization derivation construction, then to C using Tag 07PE.
The coefficient generic fibre R is a localization of C at nonzero elements of A by
localization base change, so extend once more to R. The extension formulas show that
D(x) = 1 and D annihilates A. The two derivations from K to R, k ↦ D(k tensor 1)
and the zero derivation, agree on A; localization derivation uniqueness makes them
equal. Thus D(ξ tensor 1) = 0 and D(f) = 1. All constructions work in the zero-fibre
case as well. The assumptions hr and hrA are preserved; the fraction-field hypothesis
alone suffices for the actual argument. -/
theorem linear_formalFiber_hypersurface
    (A : Type u) [CommRing A] [IsDomain A]
    (q : Ideal (Polynomial A)) [q.IsPrime]
    (r : Ideal (Polynomial A)) [r.IsPrime]
    [IsFractionRing A r.ResidueField]
    (hr : r ≠ ⊥) (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    let R := (⊥ : Ideal A).Fiber C
    letI : CommSemiring R := (inferInstance : CommRing R).toCommSemiring
    letI : AddCommMonoid R := (inferInstance : CommRing R).toAddCommGroup.toAddCommMonoid
    letI : Algebra ℤ R := Ring.toIntAlgebra R
    ∃ (f : R) (D : Derivation ℤ R R), D f = 1 ∧
      Nonempty ((R ⧸ Ideal.span ({f} : Set R)) ≃+* r.Fiber C) := by
  have _hr := hr
  have _hrA := hrA
  let B := Localization.AtPrime q
  let C := AdicCompletion (IsLocalRing.maximalIdeal B) B
  let K := (⊥ : Ideal A).ResidueField
  let R := (⊥ : Ideal A).Fiber C
  let : Algebra C R := Algebra.TensorProduct.rightAlgebra
  let : Algebra ℤ R := Ring.toIntAlgebra R
  let Dp : Derivation ℤ (Polynomial A) (Polynomial A) :=
    (Polynomial.derivative' (R := A)).restrictScalars ℤ
  obtain ⟨Db, hb⟩ := extend_absolute_derivation (S := B) q.primeCompl Dp
  obtain ⟨Dc, _, hc, _, _⟩ :=
    (Derivation.exists_completion_and_unique_localization B Db).1
      (IsLocalRing.maximalIdeal B)
  obtain ⟨D, hD⟩ := extend_absolute_derivation (S := R)
    (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)) Dc
  let e : r.ResidueField ≃ₐ[A] K :=
    IsLocalization.algEquiv (nonZeroDivisors A) r.ResidueField K
  let ξ : K := e (algebraMap (Polynomial A) r.ResidueField X)
  let x : C := algebraMap (Polynomial A) C X
  let f : R := algebraMap C R x - Algebra.TensorProduct.includeLeft (S := A) ξ
  have hx : D (algebraMap C R x) = 1 := by
    rw [hD]
    dsimp [x]
    rw [IsScalarTower.algebraMap_apply (Polynomial A) B C, hc, hb]
    simp [Dp, Polynomial.derivative']
  have hA : ∀ a : A, Dc (algebraMap A C a) = 0 := by
    intro a
    rw [IsScalarTower.algebraMap_apply A B C, hc,
      IsScalarTower.algebraMap_apply A (Polynomial A) B, hb]
    simp [Dp, Polynomial.derivative']
  have hK : ∀ k : K, D (Algebra.TensorProduct.includeLeft (S := A) k) = 0 := by
    have heq := IsLocalization.derivation_ext (nonZeroDivisors A)
      ((Algebra.TensorProduct.includeLeft (S := A)).toRingHom : K →+* R)
      (δ₁ := fun k ↦ D (Algebra.TensorProduct.includeLeft (S := A) k)) (δ₂ := fun _ ↦ 0)
      (by intro a b; rw [map_mul, D.leibniz]; rfl)
      (by intro a b; simp)
      (by
        intro a
        rw [Algebra.TensorProduct.includeLeft.commutes]
        rw [IsScalarTower.algebraMap_apply A C R, hD, hA, map_zero])
    exact congrFun heq
  refine ⟨f, D, ?_, ?_⟩
  · change D (algebraMap C R x -
      Algebra.TensorProduct.includeLeft (S := A) ξ) = 1
    rw [map_sub, hx, hK, sub_zero]
  · exact linear_fiber_quotient A r C

end Polynomial
