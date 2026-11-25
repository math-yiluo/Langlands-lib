/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import WeilConjectures.RingTheory.PopescuAuxiliaryQuotientSmooth
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import WeilConjectures.RingTheory.SingularIdealLocalizationSmooth

/-!
# Singular elements in the height-zero auxiliary algebra

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FA, auxiliary algebra construction.
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-witnesses)
-/

@[expose] public section

universe u v t

open scoped BigOperators

namespace Algebra

/-- The auxiliary algebra transports a singular element of an intermediate algebra and
powers of finitely many singular elements of the original algebra.

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FA, construction and the two
localizations in its proof.
(blueprint: lem-weil-pbc-popescu-height-zero-auxiliary-witnesses)

Proof: Since A is Noetherian and C is finitely presented over R, the map A to C makes
C a finitely presented A-algebra. Choose C = A[x_k]/(f_j), and lift c to a polynomial p.
For the indices i in s, put L = product of the lambda_i. Each lambda_i annihilates
alpha(a_i)^(n_i), so L does too. Construct the actual quotient
B = A[x_k,y_i,z,t_ij]/(f_j - sum_i y_i*t_ij, z*y_i).
Its structure map from A and the evaluation x_k at their images in Lambda, y_i at
alpha(a_i)^(n_i), z at L, and t_ij at zero give beta and delta; the relations vanish.
B is finitely presented over R by the finite polynomial presentation and composition.
Let c' be the class of p. The first auxiliary localization identifies B_z with
C[t_ij,z]_z, respecting c'. Since c belongs to the singular ideal of C, C_c is smooth
over R by the singular-ideal localization theorem. Polynomial extension and localization
are smooth over C_c, so the localization of B at z*c' is smooth over R. Thus z*c'
belongs to the singular ideal of B. Its image is L*gamma(c), which gives b.
For each i, the second auxiliary localization identifies B_(y_i) with a localization
of a polynomial algebra over A. Localizing further at beta(a_i) gives a smooth algebra
over A_(a_i). Since a_i belongs to the singular ideal of A, A_(a_i) is smooth over R.
Composition of these smooth maps and the iterated-localization isomorphism show that
B_(beta(a_i)*y_i) is smooth over R. Thus beta(a_i)*y_i belongs to the singular ideal
of B. Take this element as d_i: its image is alpha(a_i)^(n_i+1).
For s empty the construction is C[z] and only b is required; all products are one.
No witness is chosen as definition data: B is the polynomial quotient just described.
-/
theorem exists_popescu_height_zero_auxiliary_witnesses
    {R : Type u} {A : Type v} {Λ : Type t} {C : Type (max u v)}
    [CommRing R] [CommRing A] [CommRing Λ] [CommRing C]
    [Algebra R A] [Algebra R Λ] [Algebra R C]
    [IsNoetherianRing R] [FinitePresentation R A] [FinitePresentation R C]
    (α : A →ₐ[R] Λ) (β : A →ₐ[R] C) (γ : C →ₐ[R] Λ)
    (hcomp : γ.comp β = α) (s : Finset A)
    (hs : ∀ a ∈ s, a ∈ singularIdeal R A)
    (n : s → ℕ) (ell : s → Λ)
    (hkill : ∀ a : s, ell a * α a.val ^ n a = 0)
    (c : C) (hc : c ∈ singularIdeal R C) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      ∃ (β' : A →ₐ[R] B) (δ : B →ₐ[R] Λ),
        FinitePresentation R B ∧ δ.comp β' = α ∧
        (∃ b ∈ singularIdeal R B, δ b = (∏ a : s, ell a) * γ c) ∧
        (∀ a : s, ∃ d ∈ singularIdeal R B, δ d = α a.val ^ (n a + 1)) := by
  classical
  by_cases hs0 : s = ∅
  · subst s
    refine ⟨C, inferInstance, inferInstance, β, γ, inferInstance, hcomp, ?_, ?_⟩
    · exact ⟨c, hc, by simp⟩
    · intro a
      exact False.elim (Finset.notMem_empty a.val a.property)
  have : Nonempty s := Finset.nonempty_coe_sort.mpr (Finset.nonempty_iff_ne_empty.mpr hs0)
  let : Algebra A C := β.toRingHom.toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algHom β
  let : FinitePresentation A C :=
    FinitePresentation.of_restrict_scalars_finitePresentation R A C
  obtain ⟨k, q, hq, hqker⟩ := FinitePresentation.out (R := A) (A := C)
  obtain ⟨m, f, hker⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hqker
  obtain ⟨p, hp⟩ := hq c
  let P := PopescuAuxPoly.{u} A s k m
  let I : Ideal P := popescuAuxIdeal A s k m f
  let B := P ⧸ I
  let mk : P →ₐ[A] B := Ideal.Quotient.mkₐ A I
  let z : P := MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl ⟨()⟩)))
  let y : s → P := fun a ↦ MvPolynomial.X (Sum.inr (Sum.inl a))
  let L : Λ := ∏ a : s, ell a
  let vals : PopescuAuxVars.{u} s k m → Λ := fun j ↦
    match j with
    | Sum.inl j => γ (q (MvPolynomial.X j))
    | Sum.inr (Sum.inl a) => α a.val ^ n a
    | Sum.inr (Sum.inr (Sum.inl _)) => L
    | Sum.inr (Sum.inr (Sum.inr _)) => 0
  let ev : P →ₐ[R] Λ := MvPolynomial.aevalTower α vals
  have hevX (j : PopescuAuxVars.{u} s k m) : ev (MvPolynomial.X j) = vals j := by
    exact MvPolynomial.aevalTower_X α vals j
  have hevIncl : ev.comp ((popescuAuxIncl A s k m).restrictScalars R) =
      γ.comp (q.restrictScalars R) := by
    apply MvPolynomial.algHom_ext'
    · ext a
      change ev (popescuAuxIncl A s k m (MvPolynomial.C a)) = γ (q (MvPolynomial.C a))
      simp only [popescuAuxIncl, MvPolynomial.algHom_C]
      change ev (MvPolynomial.C a) = γ (β a)
      rw [show ev (MvPolynomial.C a) = α a from MvPolynomial.aevalTower_C α vals a]
      exact (AlgHom.congr_fun hcomp a).symm
    · intro j
      change ev (popescuAuxIncl A s k m (MvPolynomial.X j)) = γ (q (MvPolynomial.X j))
      simp only [popescuAuxIncl, MvPolynomial.aeval_X]
      rw [hevX]
  have hevf (j : Fin m) : ev (popescuAuxIncl A s k m (f j)) = 0 := by
    have hf : f j ∈ RingHom.ker q.toRingHom := by
      rw [← hker]
      exact Submodule.subset_span ⟨j, rfl⟩
    have hf0 : q (f j) = 0 := RingHom.mem_ker.mp hf
    have h := AlgHom.congr_fun hevIncl (f j)
    change ev (popescuAuxIncl A s k m (f j)) = γ (q (f j)) at h
    rw [h, hf0, map_zero]
  have hL (a : s) : L * α a.val ^ n a = 0 := by
    obtain ⟨l, hl⟩ := Finset.dvd_prod_of_mem ell (Finset.mem_univ a)
    change (∏ a : s, ell a) * α a.val ^ n a = 0
    rw [hl]
    calc
      ell a * l * α a.val ^ n a = l * (ell a * α a.val ^ n a) := by ring
      _ = 0 := by rw [hkill, mul_zero]
  have hI : ∀ x ∈ I, ev x = 0 := by
    apply (Ideal.span_le.mpr ?_ : I ≤ RingHom.ker ev.toRingHom)
    rintro x (⟨j, rfl⟩ | ⟨a, rfl⟩)
    · change ev (popescuAuxIncl A s k m (f j) -
        ∑ a : s, MvPolynomial.X (Sum.inr (Sum.inl a)) *
          MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr (a, j))))) = 0
      rw [map_sub, hevf, map_sum]
      simp only [map_mul, hevX, vals, mul_zero, Finset.sum_const_zero, sub_zero]
    · change ev (z * y a) = 0
      rw [map_mul]
      change ev (MvPolynomial.X _) * ev (MvPolynomial.X _) = 0
      rw [hevX, hevX]
      exact hL a
  let δ : B →ₐ[R] Λ := Ideal.Quotient.liftₐ I ev hI
  let β' : A →ₐ[R] B := IsScalarTower.toAlgHom R A B
  have hδmk (x : P) : δ (mk x) = ev x := by
    exact Ideal.Quotient.lift_mk I ev.toRingHom hI
  have hδβ : δ.comp β' = α := by
    ext a
    change δ (mk (MvPolynomial.C a)) = α a
    rw [hδmk]
    exact MvPolynomial.aevalTower_C α vals a
  let : FinitePresentation R P := FinitePresentation.mvPolynomial R A _
  let : IsNoetherianRing P := FiniteType.isNoetherianRing R P
  have hfp : FinitePresentation R B := FinitePresentation.quotient
    ((inferInstance : IsNoetherianRing P).noetherian I)
  have hsmooth := popescuAuxQuot_smooth_localizations R A C s k m f q hq hker p
    (by rw [hp]; exact smooth_localization_of_mem_singularIdeal R C c hc)
    (fun a : s ↦ a.val)
    (fun a ↦ smooth_localization_of_mem_singularIdeal R A a.val (hs a.val a.property))
  refine ⟨B, inferInstance, inferInstance, β', δ, hfp, hδβ, ?_, ?_⟩
  · refine ⟨mk z * mk (popescuAuxIncl A s k m p), ?_, ?_⟩
    · apply Ideal.le_radical
      apply Ideal.subset_span
      exact hsmooth.1
    · rw [map_mul, hδmk, hδmk]
      have hpe := AlgHom.congr_fun hevIncl p
      change ev (popescuAuxIncl A s k m p) = γ (q p) at hpe
      change ev (MvPolynomial.X _) * ev (popescuAuxIncl A s k m p) = L * γ c
      rw [hevX, hpe, hp]
  · intro a
    refine ⟨β' a.val * mk (y a), ?_, ?_⟩
    · apply Ideal.le_radical
      apply Ideal.subset_span
      exact hsmooth.2 a
    · rw [map_mul, hδmk]
      have hβ := AlgHom.congr_fun hδβ a.val
      change δ (β' a.val) = α a.val at hβ
      rw [hβ]
      change α a.val * ev (MvPolynomial.X _) = α a.val ^ (n a + 1)
      rw [hevX]
      change α a.val * α a.val ^ n a = α a.val ^ (n a + 1)
      rw [pow_succ, mul_comm]

end Algebra
