/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal
import WeilConjectures.RingTheory.PopescuZeroBaseSingleChartUnlocalized

/-! # Scalar extension and localization of the single-chart presentation

Source: Stacks Project, Tag 07CP, first two lines of the calculation modulo pi.
(blueprint: lem-weil-pbc-popescu-zero-base-single-chart-presentation).
-/

@[expose] public section

universe a c b

open scoped TensorProduct

namespace Algebra.PopescuLiftPresentation

variable {R : Type a} {Cbar : Type c} [CommRing R] [CommRing Cbar] {π : R}
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]

/-- The explicit coefficient map: reduce, quotient, localize, and extend scalars. -/
noncomputable def singleChartCoefficient (d : PopescuLiftPresentation R Cbar π)
    (B : Type b) [CommRing B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B] (k : Fin d.r) :
    MvPolynomial (Fin d.n) R →+*
      B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)] Localization.Away (d.reducedElement k) :=
  (Algebra.TensorProduct.includeRight (R := R ⧸ Ideal.span ({π ^ 2} : Set R))
    (A := B)).toRingHom.comp
      ((algebraMap d.reducedQuotient (Localization.Away (d.reducedElement k))).comp
        ((Ideal.Quotient.mk d.reducedIdeal).comp
          (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R))))))

/-- The linear relations over the explicitly localized coefficient ring. -/
noncomputable def singleChartLinearIdeal (d : PopescuLiftPresentation R Cbar π)
    (B : Type b) [CommRing B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B] (k : Fin d.r) :
    Ideal (MvPolynomial (Fin d.m)
      (B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)] Localization.Away (d.reducedElement k))) :=
  Ideal.span (Set.range (fun l ↦
    MvPolynomial.C (d.singleChartCoefficient B k (d.a k)) * MvPolynomial.X l -
      ∑ j : d.E k, MvPolynomial.C (d.singleChartCoefficient B k (d.h k l j)) *
        MvPolynomial.X (j : Fin d.m)))

set_option backward.isDefEq.respectTransparency false in
private theorem localized_polynomial_quotient
    {A : Type*} {K : Type*} {S : Type*} {σ : Type*}
    [CommRing A] [CommRing K] [CommRing S] [Algebra S A] [Algebra S K]
    [Algebra A K] [IsScalarTower S A K] (s : A) [IsLocalization.Away s K]
    (I : Ideal (MvPolynomial σ A)) :
    Nonempty ((MvPolynomial σ K ⧸ I.map (MvPolynomial.map (algebraMap A K))) ≃ₐ[S]
      Localization.Away (Ideal.Quotient.mk I (MvPolynomial.C s))) := by
  let : Algebra (MvPolynomial σ A) (MvPolynomial σ K) := MvPolynomial.algebraMvPolynomial
  have : IsLocalization.Away (MvPolynomial.C (σ := σ) s) (MvPolynomial σ K) := by
    simpa only [IsLocalization.Away, Submonoid.map_powers] using
      (inferInstance : IsLocalization ((Submonoid.powers s).map MvPolynomial.C)
        (MvPolynomial σ K))
  have : IsScalarTower S (MvPolynomial σ A ⧸ I)
      (MvPolynomial σ K ⧸ I.map (algebraMap (MvPolynomial σ A) (MvPolynomial σ K))) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change Ideal.Quotient.mk _ (algebraMap S (MvPolynomial σ K) r) =
        algebraMap (MvPolynomial σ A ⧸ I) _
          (Ideal.Quotient.mk I (algebraMap S (MvPolynomial σ A) r))
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      congr 1
      simp only [MvPolynomial.algebraMap_def, MvPolynomial.algebraMap_apply, MvPolynomial.map_C,
        IsScalarTower.algebraMap_apply S A K]
  have : IsLocalization.Away (Ideal.Quotient.mk I (MvPolynomial.C s))
      (MvPolynomial σ K ⧸ I.map (algebraMap (MvPolynomial σ A) (MvPolynomial σ K))) := by
    have hh := (inferInstance : IsLocalization
      (Algebra.algebraMapSubmonoid (MvPolynomial σ A ⧸ I)
        (Submonoid.powers (MvPolynomial.C (σ := σ) s)))
      (MvPolynomial σ K ⧸ I.map (algebraMap (MvPolynomial σ A) (MvPolynomial σ K))))
    rw [Algebra.algebraMapSubmonoid_powers] at hh
    have hm : algebraMap (MvPolynomial σ A) (MvPolynomial σ A ⧸ I) =
        Ideal.Quotient.mk I := by
      exact Ideal.Quotient.algebraMap_eq I
    rw [hm] at hh
    exact hh
  exact ⟨(IsLocalization.algEquiv
    (Submonoid.powers (Ideal.Quotient.mk I (MvPolynomial.C s)))
    (MvPolynomial σ K ⧸ I.map (algebraMap (MvPolynomial σ A) (MvPolynomial σ K)))
    (Localization.Away (Ideal.Quotient.mk I (MvPolynomial.C s)))).restrictScalars S⟩

private theorem localized_equiv {S P Q : Type*}
    [CommRing S] [CommRing P] [CommRing Q]
    [Algebra S P] [Algebra S Q] (e : P ≃ₐ[S] Q) (t : P) (u : Q) (h : e t = u) :
    Nonempty (Localization.Away t ≃ₐ[S] Localization.Away u) := by
  exact ⟨IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers t) (T := Submonoid.powers u)
    (Localization.Away t) (Localization.Away u) e (by rw [Submonoid.map_powers, h])⟩

set_option synthInstance.maxSize 512 in
/-- Scalar extension killing pi and localization give the displayed linear presentation.

Source: Stacks Project, Tag 07CP, first two lines of the calculation modulo pi.
(blueprint: lem-weil-pbc-popescu-zero-base-single-chart-presentation).

Proof: Split the original and auxiliary polynomial variables using the polynomial
universal property. Tensoring with B replaces coefficients by their images in B.
Because pi maps to zero, the original equations become f_l and the selected chart's
equations become a_k z_l minus the sum of h_klj z_j. First quotient by all the f_l
in the coefficient ring; reducing coefficients modulo pi squared is invisible in B,
so this is B tensor over R/(pi squared) with reducedQuotient. Inverting the image
of a_k commutes with scalar extension, polynomial extension, and the remaining
quotient: each assertion follows by constructing maps in both directions from their
universal properties and checking them on the coefficient ring and variables.
The resulting coefficient ring is K below, and its coefficient map is exactly
singleChartCoefficient. The remaining equations are exactly the generators of I.
Remove ULift by its canonical algebra equivalence. The two presentation maps fix
coefficients and each auxiliary variable; quotient and localization uniqueness show
that their composites are identities. Normalization of h is not required: this
statement retains every linear relation, including the free-variable relations. -/
theorem zero_base_single_chart_presentation (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π)
    (B : Type b) [CommRing B] [Algebra R B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r) :
    let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
      match i with
      | .inl j => d.equation (.inl j)
      | .inr l => d.equation (.inr (k, l))))
    Nonempty ((MvPolynomial (Fin d.m)
      (B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)] Localization.Away (d.reducedElement k))
        ⧸ d.singleChartLinearIdeal B k) ≃ₐ[B]
      Localization.Away (Algebra.TensorProduct.includeRight (R := R) (A := B)
        (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k)))))) := by
  classical
  let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
    match i with
    | .inl j => d.equation (.inl j)
    | .inr l => d.equation (.inr (k, l))))
  let R₂ := R ⧸ Ideal.span ({π ^ 2} : Set R)
  let A := d.reducedQuotient
  let L := B ⊗[R₂] A
  let : CommRing L := inferInstance
  let K := B ⊗[R₂] Localization.Away (d.reducedElement k)
  let : CommRing K := inferInstance
  let β : MvPolynomial (Fin d.n) R →+* L :=
    (Algebra.TensorProduct.includeRight (R := R₂) (A := B)).toRingHom.comp
      ((Ideal.Quotient.mk d.reducedIdeal).comp
        (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R)))))
  let I : Ideal (MvPolynomial (Fin d.m) L) := Ideal.span (Set.range (fun l ↦
    MvPolynomial.C (σ := Fin d.m) (β (d.a k)) * MvPolynomial.X l -
      ∑ j : d.E k, MvPolynomial.C (β (d.h k l j)) * MvPolynomial.X (j : Fin d.m)))
  let : CommRing (MvPolynomial (Fin d.m) L ⧸ I) :=
    Ideal.Quotient.commRing (R := MvPolynomial (Fin d.m) L) I
  let ρ : L →ₐ[B] K := Algebra.TensorProduct.map (AlgHom.id B B)
    (IsScalarTower.toAlgHom R₂ A (Localization.Away (d.reducedElement k)))
  let : Algebra L K := ρ.toAlgebra
  have : IsScalarTower B L K :=
    IsScalarTower.of_algebraMap_eq (R := B) (S := L) (A := K) fun b ↦ by
    change b ⊗ₜ[R₂] (1 : Localization.Away (d.reducedElement k)) = ρ (b ⊗ₜ[R₂] 1)
    change b ⊗ₜ[R₂] (1 : Localization.Away (d.reducedElement k)) =
      b ⊗ₜ[R₂] algebraMap A (Localization.Away (d.reducedElement k)) 1
    rw [map_one]
  have : IsLocalization.Away (β (d.a k)) K := by
    have h := IsLocalization.tensorProduct_tensorProduct_right R₂ B
      (Submonoid.powers (d.reducedElement k)) (Localization.Away (d.reducedElement k))
      (by
        apply RingHom.ext
        intro x
        change ρ (1 ⊗ₜ[R₂] x) = 1 ⊗ₜ[R₂] (algebraMap A _ x)
        rfl)
    have hb : β (d.a k) =
        Algebra.TensorProduct.includeRight (R := R₂) (A := B) (d.reducedElement k) := rfl
    rw [hb]
    simpa only [IsLocalization.Away, Submonoid.map_powers] using h
  have hβ (p : MvPolynomial (Fin d.n) R) :
      algebraMap L K (β p) = d.singleChartCoefficient B k p := by
    change ρ (1 ⊗ₜ[R₂] Ideal.Quotient.mk d.reducedIdeal (d.reduced p)) =
      1 ⊗ₜ[R₂] algebraMap A _ (Ideal.Quotient.mk d.reducedIdeal (d.reduced p))
    rfl
  let : Algebra (MvPolynomial (Fin d.m) L) (MvPolynomial (Fin d.m) K) :=
    MvPolynomial.algebraMvPolynomial
  have hI : I.map (MvPolynomial.map (algebraMap L K)) =
      d.singleChartLinearIdeal B k := by
    simp only [I, singleChartLinearIdeal, Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext l
    simp only [Function.comp_apply, map_sub, map_mul, map_sum,
      MvPolynomial.map_C, MvPolynomial.map_X, hβ]
    rfl
  obtain ⟨el⟩ := localized_polynomial_quotient (S := B) (K := K) (β (d.a k)) I
  obtain ⟨e, he⟩ := zero_base_single_chart_unlocalized R Cbar π d B hπ k
  change (MvPolynomial (Fin d.m) L ⧸ I) ≃ₐ[B] B ⊗[R] ULift (d.polynomial ⧸ J) at e
  change ∀ p, e (Ideal.Quotient.mk I (MvPolynomial.C (β p))) =
    Algebra.TensorProduct.includeRight (R := R) (A := B)
      (ULift.up (Ideal.Quotient.mk J (d.includeX p))) at he
  obtain ⟨er⟩ := localized_equiv e
    (Ideal.Quotient.mk I (MvPolynomial.C (β (d.a k))))
    (Algebra.TensorProduct.includeRight (R := R) (A := B)
      (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k))))) (he (d.a k))
  exact ⟨(Ideal.quotientEquivAlgOfEq B hI.symm).trans (el.trans er)⟩

end Algebra.PopescuLiftPresentation
