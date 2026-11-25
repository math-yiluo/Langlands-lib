/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Kähler differentials of a polynomial algebra over an algebra

Let `R → A` be a ring map and `B = A[X_σ]` a polynomial algebra over `A` in finitely many
variables. We show that the `B`-linear map
`(B ⊗[A] Ω[A⁄R]) × (σ → B) → Ω[B⁄R]`, `(b ⊗ dα, (b_j)) ↦ b dα + ∑ b_j dX_j`, is an isomorphism.
In particular, if `Ω[A⁄R]` is free of rank `d`, then `Ω[A[X_1, …, X_e]⁄R]` is free of rank `d + e`.

## Main results

* `KaehlerDifferential.mvPolynomialKaehlerMap_bijective`: the map above is bijective.
* `KaehlerDifferential.mvPolynomialKaehlerEquiv`: the corresponding linear equivalence.
* `KaehlerDifferential.mvPolynomialBasisOfBasis`: a basis of `Ω[A[X_1, …, X_e]⁄R]` indexed by
  `Fin (d + e)` from a basis of `Ω[A⁄R]` indexed by `Fin d`.
* `KaehlerDifferential.mvPolynomial_kaehler_bijective_and_basis`: the blueprint statement.
-/

@[expose] public section

open TensorProduct MvPolynomial Module

namespace KaehlerDifferential

variable (R A σ : Type*) [CommRing R] [CommRing A] [Algebra R A] [Fintype σ]

/-- For `B = A[X_σ]`, the `B`-linear map `(B ⊗[A] Ω[A⁄R]) × (σ → B) → Ω[B⁄R]`,
`(b ⊗ dα, (b_j)) ↦ b dα + ∑ b_j dX_j`. -/
noncomputable def mvPolynomialKaehlerMap :
    (MvPolynomial σ A ⊗[A] Ω[A⁄R]) × (σ → MvPolynomial σ A) →ₗ[MvPolynomial σ A]
      Ω[MvPolynomial σ A⁄R] :=
  (mapBaseChange R A (MvPolynomial σ A)).coprod
    (Fintype.linearCombination (MvPolynomial σ A) fun j => D R (MvPolynomial σ A) (X j))

lemma mvPolynomialKaehlerMap_apply (x : MvPolynomial σ A ⊗[A] Ω[A⁄R])
    (b : σ → MvPolynomial σ A) :
    mvPolynomialKaehlerMap R A σ (x, b) =
      mapBaseChange R A (MvPolynomial σ A) x + ∑ j, b j • D R (MvPolynomial σ A) (X j) := by
  simp [mvPolynomialKaehlerMap, Fintype.linearCombination_apply]

/-- For `B = A[X_σ]` with `σ` finite, the map `(B ⊗[A] Ω[A⁄R]) × Bᵉ → Ω[B⁄R]`,
`(b ⊗ dα, (b_j)) ↦ b dα + ∑ b_j dX_j` is bijective. -/
theorem mvPolynomialKaehlerMap_bijective :
    Function.Bijective (mvPolynomialKaehlerMap R A σ) := by
  set B := MvPolynomial σ A
  let bas := mvPolynomialBasis A σ
  have hvs : ∀ b : σ → B, map R A B B (∑ j, b j • D R B (X j)) = ∑ j, b j • bas j := by
    intro b
    simp [bas, map_sum]
    all_goals rfl
  have hex := exact_mapBaseChange_map R A B
  have huinj : Function.Injective (mapBaseChange R A B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
    rw [Subsingleton.elim x 0, map_zero]
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨x, b⟩ h
    rw [mvPolynomialKaehlerMap_apply] at h
    have h' := congrArg (map R A B B) h
    rw [map_add, hex.apply_apply_eq_zero, zero_add, hvs, map_zero] at h'
    have hb : b = 0 := funext (Fintype.linearIndependent_iff.mp bas.linearIndependent b h')
    subst hb
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at h
    rw [huinj (h.trans (map_zero _).symm)]
    rfl
  · intro ω
    let b : σ → B := fun j => bas.repr (map R A B B ω) j
    have hmem : map R A B B (ω - ∑ j, b j • D R B (X j)) = 0 := by
      rw [map_sub, hvs, bas.sum_repr, sub_self]
    obtain ⟨x, hx⟩ := (hex _).mp hmem
    refine ⟨(x, b), ?_⟩
    rw [mvPolynomialKaehlerMap_apply, hx, sub_add_cancel]

/-- For `B = A[X_σ]` with `σ` finite, the isomorphism `(B ⊗[A] Ω[A⁄R]) × Bᵉ ≃ Ω[B⁄R]`,
`(b ⊗ dα, (b_j)) ↦ b dα + ∑ b_j dX_j`. -/
noncomputable def mvPolynomialKaehlerEquiv :
    ((MvPolynomial σ A ⊗[A] Ω[A⁄R]) × (σ → MvPolynomial σ A)) ≃ₗ[MvPolynomial σ A]
      Ω[MvPolynomial σ A⁄R] :=
  LinearEquiv.ofBijective _ (mvPolynomialKaehlerMap_bijective R A σ)

variable {R A} in
/-- If `Ω[A⁄R]` has a basis indexed by `Fin d`, then `Ω[A[X_1, …, X_e]⁄R]` has a basis indexed
by `Fin (d + e)`. -/
noncomputable def mvPolynomialBasisOfBasis {d : ℕ} (b : Basis (Fin d) A Ω[A⁄R]) (e : ℕ) :
    Basis (Fin (d + e)) (MvPolynomial (Fin e) A) Ω[MvPolynomial (Fin e) A⁄R] :=
  (((Algebra.TensorProduct.basis (MvPolynomial (Fin e) A) b).prod
    (Pi.basisFun (MvPolynomial (Fin e) A) (Fin e))).map
      (mvPolynomialKaehlerEquiv R A (Fin e))).reindex finSumFinEquiv

/-- **Kähler differentials of a polynomial algebra over an algebra.** Let `R → A` be a ring map,
`e : ℕ` and `B = A[X_1, …, X_e]`. Then the `B`-linear map
`(B ⊗[A] Ω[A⁄R]) × Bᵉ → Ω[B⁄R]`, `(b ⊗ dα, (b_j)) ↦ b dα + ∑ b_j dX_j`, is bijective; in
particular, if `Ω[A⁄R]` is a free `A`-module of rank `d`, then `Ω[B⁄R]` is a free `B`-module of
rank `d + e`. (blueprint: `theorem-finite-etale-covers-proper-henselian--2`) -/
theorem mvPolynomial_kaehler_bijective_and_basis (e : ℕ) :
    Function.Bijective (mvPolynomialKaehlerMap R A (Fin e)) ∧
      ∀ d : ℕ, Nonempty (Basis (Fin d) A Ω[A⁄R]) →
        Nonempty (Basis (Fin (d + e)) (MvPolynomial (Fin e) A) Ω[MvPolynomial (Fin e) A⁄R]) :=
  ⟨mvPolynomialKaehlerMap_bijective R A (Fin e), fun _ ⟨b⟩ => ⟨mvPolynomialBasisOfBasis b e⟩⟩

end KaehlerDifferential
