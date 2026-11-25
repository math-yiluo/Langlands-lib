/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.PopescuLifting
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.PopescuSmoothQuotientFactor

@[expose] public section

universe u v
open CategoryTheory
open scoped nonZeroDivisors

private theorem annihilator_span_eq_bot_of_nonzerodivisor
    (S : Type*) [CommRing S] (x : S) (hx : x ∈ S⁰) :
    Module.annihilator S (Ideal.span {x}) = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  apply (mul_right_mem_nonZeroDivisors_eq_zero_iff hx).mp
  have h := (Module.mem_annihilator.mp ha) ⟨x, Ideal.subset_span (by simp)⟩
  exact congrArg Subtype.val h

private theorem smoothAtPrime_of_smooth
    (S : Type*) (C : Type*) [CommRing S] [CommRing C] [Algebra S C]
    [Algebra.Smooth S C] (q : PrimeSpectrum C) : Algebra.IsSmoothAtPrime S q := by
  refine ⟨1, q.asIdeal.one_notMem, ?_⟩
  let : Algebra.Smooth C (Localization.Away (1 : C)) :=
    Algebra.Smooth.of_isLocalization_Away 1
  exact Algebra.Smooth.comp S C _

/-- Auxiliary output of the Popescu lifting construction, including pointwise smoothness.

(blueprint: lem-weil-pbc-popescu-smooth-lift-data)

Proof: Construct a finite polynomial presentation and apply `popescu_lifting` as in
Stacks Project Lemma 07F5. Injectivity of multiplication by `π` gives the required
annihilator equalities. The quotient maps give the compatible map modulo `π⁴`.
Clause (b) of the lifting lemma handles primes away from `π`; clause (c), together
with smoothness of the chosen smooth quotient algebra, handles primes over `π`.
Thus the resulting finitely presented algebra is smooth at every prime.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07F5, proof (blueprint:
lem-weil-pbc-popescu-smooth-lift-modulo-eight).
The construction produces a finitely presented algebra, a compatible map modulo π⁴,
and smoothness at every prime; the detailed polynomial construction is the content of
this intermediate assertion. -/
theorem exists_popescu_smooth_lift_data
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (α : A →ₐ[R] Λ) (π : R) (hπ : π ∈ R⁰) (hπΛ : algebraMap R Λ π ∈ Λ⁰)
    (hmod : ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} (R ⧸ Ideal.span {π ^ 8}) ↦
        Algebra.Smooth (R ⧸ Ideal.span {π ^ 8}) B)
      (CommAlgCat.of (R ⧸ Ideal.span {π ^ 8})
        (Λ ⧸ (Ideal.span {π ^ 8}).map (algebraMap R Λ)))) :
    ∃ (D : Type (max u v)) (_ : CommRing D) (_ : Algebra R D)
      (_ : Algebra.FinitePresentation R D) (δ : D →ₐ[R] Λ),
      (∀ q : PrimeSpectrum D, Algebra.IsSmoothAtPrime R q) ∧
      ∃ φ : (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (D ⧸ Ideal.span {(algebraMap R D π) ^ 4}),
        ∀ (a : A) (d : D),
          φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ d →
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
            Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (δ d) := by
  obtain ⟨C, _instC, _algC, _algQC, _towerC, _smoothC, β, j, hj⟩ :=
    exists_popescu_smooth_quotient_factor R Λ A α (π ^ 4) (by
      rw [← pow_mul, show 4 * 2 = 8 from rfl]; exact hmod)
  let : CommRing C := _instC
  let : Algebra R C := _algC
  let : Algebra (R ⧸ Ideal.span {(π ^ 4) ^ 2}) C := _algQC
  let : IsScalarTower R (R ⧸ Ideal.span {(π ^ 4) ^ 2}) C := _towerC
  let : Algebra.Smooth (R ⧸ Ideal.span {(π ^ 4) ^ 2}) C := _smoothC
  have hπ4 : π ^ 4 ∈ R⁰ := pow_mem hπ 4
  have hπ8 : (π ^ 4) ^ 2 ∈ R⁰ := pow_mem hπ4 2
  have hΛ4 : algebraMap R Λ (π ^ 4) ∈ Λ⁰ := by
    simpa only [map_pow] using pow_mem hπΛ 4
  have hΛ8 : algebraMap R Λ ((π ^ 4) ^ 2) ∈ Λ⁰ := by
    simpa only [map_pow] using pow_mem hΛ4 2
  obtain ⟨D, _instD, _algD, δ, ψ, red, c, cmod, hfp, hψ, hred, hc,
      _hcmod, haway, hover, _hrelative⟩ := Algebra.popescu_lifting R Λ C (π ^ 4)
    (by rw [annihilator_span_eq_bot_of_nonzerodivisor R _ hπ4,
      annihilator_span_eq_bot_of_nonzerodivisor R _ hπ8])
    (by rw [annihilator_span_eq_bot_of_nonzerodivisor Λ _ hΛ4,
      annihilator_span_eq_bot_of_nonzerodivisor Λ _ hΛ8]) j
  let : CommRing D := _instD
  let : Algebra R D := _algD
  let : Algebra.FinitePresentation R D := hfp
  revert ψ red c cmod haway
  rw [map_pow (algebraMap R D), map_pow (algebraMap R Λ) π 4]
  intro ψ red c cmod hψ hred hc _hcmod haway hover _hrelative
  have hsmooth : ∀ q : PrimeSpectrum D, Algebra.IsSmoothAtPrime R q := by
    intro q
    by_cases hq : (algebraMap R D π) ^ 4 ∈ q.asIdeal
    · have hle : Ideal.span {(algebraMap R D π) ^ 4} ≤ q.asIdeal :=
        (Ideal.span_singleton_le_iff_mem _).mpr hq
      have hrange : q ∈ Set.range (PrimeSpectrum.comap
          (Ideal.Quotient.mk (Ideal.span {(algebraMap R D π) ^ 4}))) := by
        rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
        rw [Ideal.mk_ker]
        exact hle
      obtain ⟨qbar, rfl⟩ := hrange
      exact hover qbar (smoothAtPrime_of_smooth _ C _)
    · exact haway q hq
  let f := c.comp β
  have hkill : ∀ a ∈ Ideal.span {(algebraMap R A π) ^ 4}, f a = 0 := by
    change Ideal.span {(algebraMap R A π) ^ 4} ≤ RingHom.ker f.toRingHom
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    change f ((algebraMap R A π) ^ 4) = 0
    calc
      f ((algebraMap R A π) ^ 4) =
          Ideal.Quotient.mk _ ((algebraMap R D π) ^ 4) := by
        simp only [map_pow, f.commutes, Ideal.Quotient.mk_algebraMap]
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  let φ := Ideal.Quotient.liftₐ _ f hkill
  refine ⟨D, inferInstance, inferInstance, inferInstance, δ, hsmooth, φ, ?_⟩
  intro a d had
  have hfa : f a = Ideal.Quotient.mk _ d := by
    exact had
  have hcompat : ψ (f a) = Ideal.Quotient.mk _ (α a) := by
    change (ψ.comp c.toRingHom) (β a) = _
    rw [hc]
    change red (j (β a)) = _
    rw [hj]
    exact DFunLike.congr_fun hred (α a)
  have hd : ψ (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ (δ d) :=
    DFunLike.congr_fun hψ d
  exact hcompat.symm.trans ((congrArg ψ hfa).trans hd)
