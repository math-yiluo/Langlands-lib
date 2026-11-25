/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import WeilConjectures.RingTheory.PopescuZeroBaseSingleChartPolynomial
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Polynomial model of a partial Popescu chart after killing pi

Source: Stacks Project, Tag 07CP, the calculation of the partial chart modulo pi.
(blueprint: lem-weil-pbc-popescu-partial-chart-polynomial).
-/

@[expose] public section

set_option autoImplicit false

universe a c b

open scoped TensorProduct

namespace Algebra

/-- Killing pi and inverting a_k turns the partial chart into a polynomial algebra.

Source: Stacks Project, Tag 07CP (lemma-lifting), the calculation of D_k/pi D_k.
(blueprint: lem-weil-pbc-popescu-partial-chart-polynomial).

Proof: Scalar extension to B sets pi to zero. The selected u_j become f_j for
j in E_k; the other chart equations become a_k z_l minus the indicated linear sum.
After inverting a_k, the cleared relations a_k f_l = sum h_klj f_j + pi^2 g_kl
show that the ideal of all original f_l equals the ideal of the selected f_j.
This identifies the coefficient quotient with the scalar extension of the reduced
quotient localized at a_k. Each equation outside E_k solves uniquely for z_l as
a_k inverse times sum h_klj z_j, and leaves the z_j in E_k free. Define the forward
map by these substitutions and the inverse by the original variables and free z_j.
The relations vanish under both maps, and checking x_i and all z_l proves their
composites are identities. Renumber the free variables using the finite-set
bijection with Fin(card E_k), and the ambient variables using finSumFinEquiv.
This argument also covers E_k empty or all auxiliary variables, and the zero
coefficient algebra. It uses no flatness, dimension equality or full-chart relation.
-/
theorem popescu_partial_chart_polynomial (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (B : Type b) [CommRing B] [Algebra R B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r)
    (F : Fin d.m → MvPolynomial (Fin (d.n + d.m)) R)
    (hF : ∀ l, F l = MvPolynomial.rename finSumFinEquiv
      (if l ∈ d.E k then d.equation (.inl l) else d.equation (.inr (k, l)))) :
    let S := MvPolynomial (Fin (d.n + d.m)) R ⧸ Ideal.span (Set.range F)
    let s : S := Ideal.Quotient.mk _
      (MvPolynomial.rename finSumFinEquiv (d.includeX (d.a k)))
    Nonempty (MvPolynomial (Fin (d.E k).card)
      (B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)]
        Localization.Away (d.reducedElement k)) ≃ₐ[B]
      Localization.Away (Algebra.TensorProduct.includeRight (R := R) (A := B) s)) := by
  classical
  dsimp only
  let I := Ideal.span (Set.range F)
  let S := MvPolynomial (Fin (d.n + d.m)) R ⧸ I
  let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
    match i with
    | .inl j => d.equation (.inl j)
    | .inr l => d.equation (.inr (k, l))))
  let Dk := ULift.{0} (d.polynomial ⧸ J)
  let ren := MvPolynomial.renameEquiv R (finSumFinEquiv :
    Fin d.n ⊕ Fin d.m ≃ Fin (d.n + d.m))
  let q : d.polynomial →ₐ[R] S := (Ideal.Quotient.mkₐ R I).comp ren.toAlgHom
  have hFJ (l : Fin d.m) : ren.symm (F l) ∈ J := by
    rw [hF l]
    change ren.symm (ren _) ∈ J
    rw [ren.symm_apply_apply]
    by_cases hl : l ∈ d.E k
    · simp only [ite_eq_left hl]
      exact Ideal.subset_span ⟨.inl l, rfl⟩
    · simp only [ite_eq_right hl]
      exact Ideal.subset_span ⟨.inr l, rfl⟩
  let ψ : MvPolynomial (Fin (d.n + d.m)) R →ₐ[R] Dk :=
    (ULift.algEquiv (R := R)).symm.toAlgHom.comp
      ((Ideal.Quotient.mkₐ R J).comp ren.symm.toAlgHom)
  have hI : ∀ p, p ∈ I → ψ p = 0 := by
    have hi : I ≤ RingHom.ker ψ.toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨l, rfl⟩
      change ULift.up (Ideal.Quotient.mk J (ren.symm (F l))) = (0 : Dk)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hFJ l)]
      rfl
    exact fun p hp ↦ hi hp
  let φ : S →ₐ[R] Dk := Ideal.Quotient.liftₐ I ψ hI
  have hφq (p : d.polynomial) : φ (q p) = ULift.up (Ideal.Quotient.mk J p) := by
    change ULift.up (Ideal.Quotient.mk J (ren.symm (ren p))) = _
    rw [ren.symm_apply_apply]
  have hφ : Function.Surjective φ := by
    rintro ⟨x⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨q p, hφq p⟩
  let A := B ⊗[R] S
  let inc : S →ₐ[R] A := Algebra.TensorProduct.includeRight
  let t : A := inc (q (d.includeX (d.a k)))
  let L := Localization.Away t
  let ev : d.polynomial →ₐ[R] L :=
    (IsScalarTower.toAlgHom R A L).comp (inc.comp q)
  let ex : MvPolynomial (Fin d.n) R →ₐ[R] L := ev.comp d.includeX
  have hπL : algebraMap R L π = 0 := by
    rw [IsScalarTower.algebraMap_apply R B L, hπ, map_zero]
  have hevπ : ev (MvPolynomial.C π) = 0 := by
    exact ev.commutes π |>.trans hπL
  have hu (l : Fin d.m) : ev (d.equation (.inl l)) = ex (d.f l) := by
    simp [PopescuLiftPresentation.equation, map_sub, map_mul, hevπ, ex]
  have hpartial (l : Fin d.m) :
      ev (if l ∈ d.E k then d.equation (.inl l) else d.equation (.inr (k, l))) = 0 := by
    have hq : q (if l ∈ d.E k then d.equation (.inl l)
        else d.equation (.inr (k, l))) = 0 := by
      change Ideal.Quotient.mk I (ren _) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      change MvPolynomial.rename finSumFinEquiv _ ∈ I
      rw [← hF l]
      exact Ideal.subset_span ⟨l, rfl⟩
    change algebraMap A L (inc (q _)) = 0
    rw [hq, map_zero, map_zero]
  have hselected (l : Fin d.m) (hl : l ∈ d.E k) : ex (d.f l) = 0 := by
    have hh := hpartial l
    rw [ite_eq_left hl, hu l] at hh
    exact hh
  have ha : IsUnit (ex (d.a k)) := by
    exact IsLocalization.Away.algebraMap_isUnit (S := L) t
  have hall (l : Fin d.m) : ex (d.f l) = 0 := by
    have hr := congrArg ex (hd.relation k l)
    have hp : ex (MvPolynomial.C (π ^ 2)) = 0 := by
      exact (ex.commutes (π ^ 2)).trans (by rw [map_pow, hπL]; simp)
    simp only [map_mul, map_add, map_sum, hp, zero_mul, add_zero] at hr
    have hz : ex (d.a k) * ex (d.f l) = 0 := by
      rw [hr]
      apply Finset.sum_eq_zero
      intro j hj
      rw [hselected j hj, mul_zero]
    exact (ha.mul_right_eq_zero).mp hz
  have hJ : J ≤ RingHom.ker ev.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl l =>
      change ev (d.equation (.inl l)) = 0
      rw [hu l, hall l]
    | inr l =>
      change ev (d.equation (.inr (k, l))) = 0
      by_cases hl : l ∈ d.E k
      · have hz : d.equation (.inr (k, l)) = 0 := by
          simp [PopescuLiftPresentation.equation, hd.normalized_g k l hl,
            hd.normalized_h k l hl, apply_ite, hl]
        rw [hz, map_zero]
      · simpa only [ite_eq_right hl] using hpartial l
  let f : A →ₐ[B] B ⊗[R] Dk := Algebra.TensorProduct.map (AlgHom.id B B) φ
  have hf : Function.Surjective f :=
    Algebra.TensorProduct.map_surjective (AlgHom.id B B) φ Function.surjective_id hφ
  have hker : ∀ x, f x = 0 → algebraMap A L x = 0 := by
    have hmap : RingHom.ker f = (RingHom.ker φ).map inc :=
      Algebra.TensorProduct.lTensor_ker (A := B) φ hφ
    have hle : RingHom.ker f ≤ RingHom.ker (algebraMap A L) := by
      rw [hmap, Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hp : ren.symm p ∈ J :=
        Ideal.Quotient.eq_zero_iff_mem.mp (congrArg ULift.down hx)
      have hev : ev (ren.symm p) = 0 := hJ hp
      change algebraMap A L (inc (Ideal.Quotient.mk I p)) = 0
      change algebraMap A L (inc (Ideal.Quotient.mk I (ren (ren.symm p)))) = 0 at hev
      simpa only [ren.apply_symm_apply] using hev
    exact fun x hx ↦ hle hx
  have hbij : Function.Bijective (IsLocalization.Away.mapₐ
      L (Localization.Away (f t)) f t) := by
    constructor
    · change Function.Injective (IsLocalization.Away.map
        L (Localization.Away (f t)) f.toRingHom t)
      apply (IsLocalization.Away.map_injective_iff (Localization.Away (f t))
        f.toRingHom t).mpr
      intro x hx
      obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff
        (Submonoid.powers t) L x).mp (hker x hx)
      obtain ⟨n, hn⟩ := u.property
      exact ⟨n, by simpa only [← hn] using hu⟩
    · exact IsLocalization.Away.mapₐ_surjective_of_surjective t hf
  let e' := AlgEquiv.ofBijective
    (IsLocalization.Away.mapₐ L (Localization.Away (f t)) f t) hbij
  have hft : f t = Algebra.TensorProduct.includeRight (R := R) (A := B)
      (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k)))) := by
    change f (Algebra.TensorProduct.includeRight (q (d.includeX (d.a k)))) = _
    change Algebra.TensorProduct.includeRight (φ (q (d.includeX (d.a k)))) = _
    rw [hφq]
  obtain ⟨e⟩ := d.zero_base_single_chart_polynomial R Cbar π hd.normalized_h B hπ k
  change MvPolynomial (d.E k) _ ≃ₐ[B]
    Localization.Away (Algebra.TensorProduct.includeRight (R := R) (A := B)
      (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k))))) at e
  rw [← hft] at e
  let K := B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)]
    Localization.Away (d.reducedElement k)
  let er := (MvPolynomial.renameEquiv K (d.E k).equivFin.symm).restrictScalars B
  exact ⟨er.trans (e.trans e'.symm)⟩

end Algebra
