/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.RingTheory.PopescuStandardReductionFactorCore

/-! A reduced factorization through one standard smooth algebra. -/

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

noncomputable def reducedAlgHom
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (A : Type w) [CommRing A] [Algebra R A]
    (φ : A →ₐ[R] Λ) : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I]
      (Λ ⧸ I.map (algebraMap R Λ)) := by
  let hmap : I.map (algebraMap R A) ≤
      (I.map (algebraMap R Λ)).comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change φ (algebraMap R A r) ∈ I.map (algebraMap R Λ)
    rw [show φ (algebraMap R A r) = algebraMap R Λ r by simp]
    exact Ideal.mem_map_of_mem (algebraMap R Λ) hr
  let f := Ideal.Quotient.liftₐ (I.map (algebraMap R A))
    (Ideal.Quotient.mkₐ R (I.map (algebraMap R Λ)) |>.comp φ)
    (fun a ha ↦ (Ideal.Quotient.eq_zero_iff_mem).2 (hmap ha))
  exact
    { toRingHom := f.toRingHom
      commutes' := by
        intro r
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        simp [f] }

/--
The construction is the finite-presentation factorization in Tag 07CK. Apply the
finite-presentation factorization criterion to the reduced map and retain the chosen
standard smooth stage and its two factor maps.
(blueprint: new-lem-popescu-reduction-factor)
-/
theorem exists_popescu_reduction_factor
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ IsStandardSmooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (A : Type w) [CommRing A] [Algebra R A] [FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    ∃ (C : Type (max u v w)) (_ : CommRing C) (_ : Algebra (R ⧸ I) C),
      IsStandardSmooth (R ⧸ I) C ∧
        ∃ (β : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] C)
          (δ : C →ₐ[R ⧸ I] Λ ⧸ I.map (algebraMap R Λ)),
          δ.comp β = reducedAlgHom R Λ I A φ := by
  obtain ⟨C, hCcomm, hCalg, hfp, ι, φ', hcomp, hstd⟩ :=
    exists_standardSmooth_reduction_factorization_core R Λ I hΛ A φ
  let J : Ideal C := I.map (algebraMap R C)
  let Q : Type (max u v w) := C ⧸ J
  set_option linter.style.haveILetI false in
  letI : CommRing Q := inferInstance
  set_option linter.style.haveILetI false in
  letI : Algebra R Q := Ideal.Quotient.algebra R
  have hJ : ∀ r : R, r ∈ I → algebraMap R Q r = 0 := by
    intro r hr
    apply (Ideal.Quotient.eq_zero_iff_mem).2
    exact Ideal.mem_map_of_mem (algebraMap R C) hr
  let qC : C →ₐ[R] Q := Ideal.Quotient.mkₐ R J
  let qι : A →ₐ[R] Q := qC.comp ι
  have hιJ : I.map (algebraMap R A) ≤ J.comap ι.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change ι (algebraMap R A r) ∈ J
    rw [ι.commutes]
    exact Ideal.mem_map_of_mem (algebraMap R C) hr
  have hqι : ∀ a ∈ I.map (algebraMap R A), qι a = 0 := by
    intro a ha
    apply (Ideal.Quotient.eq_zero_iff_mem).2
    change ι a ∈ J
    exact hιJ ha
  let bRing : (A ⧸ I.map (algebraMap R A)) →+* Q :=
    Ideal.Quotient.lift _ qι.toRingHom hqι
  let β : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] Q :=
    { toRingHom := bRing
      commutes' := by
        intro r
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        change bRing (Ideal.Quotient.mk _ (algebraMap R A r)) =
          algebraMap (R ⧸ I) Q (Ideal.Quotient.mk I r)
        rw [Ideal.Quotient.lift_mk]
        exact (qι.commutes r).trans (Ideal.Quotient.lift_mk _ _ _).symm }
  have hJmap : J ≤ (I.map (algebraMap R Λ)).comap φ'.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change φ' (algebraMap R C r) ∈ I.map (algebraMap R Λ)
    rw [φ'.commutes]
    exact Ideal.mem_map_of_mem (algebraMap R Λ) hr
  have hφ' : ∀ c ∈ J, Ideal.Quotient.mk (I.map (algebraMap R Λ)) (φ' c) = 0 := by
    intro c hc
    apply (Ideal.Quotient.eq_zero_iff_mem).2
    exact hJmap hc
  let dRing : Q →+* (Λ ⧸ I.map (algebraMap R Λ)) :=
    Ideal.Quotient.lift J ((Ideal.Quotient.mk (I.map (algebraMap R Λ))).comp φ'.toRingHom)
      hφ'
  let δ : Q →ₐ[R ⧸ I] (Λ ⧸ I.map (algebraMap R Λ)) :=
    { toRingHom := dRing
      commutes' := by
        intro r
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        change ((Ideal.Quotient.mk _).comp φ'.toRingHom) (algebraMap R C r) = _
        change Ideal.Quotient.mk _ (φ' (algebraMap R C r)) = _
        rw [φ'.commutes]
        rfl }
  refine ⟨Q, inferInstance, inferInstance, ?_, β, δ, ?_⟩
  · simpa only [J] using hstd
  · ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change dRing (bRing (Ideal.Quotient.mk _ x)) =
      reducedAlgHom R Λ I A φ (Ideal.Quotient.mk _ x)
    change Ideal.Quotient.mk _ (φ' (ι x)) = _
    rw [← hcomp]
    rfl

end Algebra
