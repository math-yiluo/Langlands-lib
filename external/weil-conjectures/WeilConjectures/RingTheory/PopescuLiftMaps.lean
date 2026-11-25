/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.LinearCombination

/-! # The diagram for the explicit Popescu quotient

Source: Stacks Project, Tag 07CP, the construction of D → Λ and Cbar → D/πD.
(blueprint: lem-weil-pbc-popescu-lift-maps).
-/

@[expose] public section

universe a b c

namespace Algebra

/-- Construct the compatible maps for the prepared polynomial quotient.

Source: Stacks Project, Tag 07CP, the paragraph after the definition of p_{kl};
the original blueprint steps 6 and 7.
(blueprint: lem-weil-pbc-popescu-lift-maps).

Proof: Lift the finitely many images j(ε(X_i)) to λ_i in Λ. Since ε kills the
reduced f_j, evaluating f_j at λ lies in π²Λ; choose μ_j with f_j(λ)=π²μ_j.
Evaluate the polynomial ring Q by x_i ↦ λ_i and z_j ↦ πμ_j. The equations
f_j-πz_j vanish. Evaluating a_k f_l=Σ h_{klj}f_j+π²g_{kl} shows that
Y=a_k(λ)μ_l-Σ h_{klj}(λ)μ_j-g_{kl}(λ) is killed by π². The annihilator
hypothesis then gives πY=0, so p_{kl} vanishes too. Factor this evaluation
through Q/J and transport along ULift to obtain φ. It induces ψ modulo π.
The canonical reduction modulo π² then π gives red. Sending x_i to the class
of x_i in D/πD kills π² and all f_j, so it factors through the surjection ε
whose kernel is the ideal of the reduced f_j, yielding c. This c kills πCbar
and therefore induces cmod. Their composites with quotient maps give the
three quotient compatibilities. The right square agrees on ε(X_i) and on
scalars; since ε is surjective, this proves the final diagram equality.
The construction of c gives exactly the displayed generator equation.
-/
theorem exists_popescu_lift_maps (R : Type a) (Λ : Type b) (Cbar : Type c)
    [CommRing R] [CommRing Λ] [CommRing Cbar] [Algebra R Λ] [Algebra R Cbar]
    (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (hAnnΛ : Module.annihilator Λ (Ideal.span ({algebraMap R Λ π} : Set Λ)) =
      Module.annihilator Λ (Ideal.span ({algebraMap R Λ (π ^ 2)} : Set Λ)))
    (j : Cbar →ₐ[R] (Λ ⧸ Ideal.span ({algebraMap R Λ (π ^ 2)} : Set Λ))) :
    ∃ (φ : d.liftingAlgebra →ₐ[R] Λ)
      (ψ : (d.liftingAlgebra ⧸ Ideal.span ({algebraMap R d.liftingAlgebra π} :
        Set d.liftingAlgebra)) →+* (Λ ⧸ Ideal.span ({algebraMap R Λ π} : Set Λ)))
      (red : (Λ ⧸ Ideal.span ({algebraMap R Λ (π ^ 2)} : Set Λ)) →+*
        (Λ ⧸ Ideal.span ({algebraMap R Λ π} : Set Λ)))
      (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
        Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
      (cmod : (Cbar ⧸ Ideal.span ({algebraMap R Cbar π} : Set Cbar)) →+*
        (d.liftingAlgebra ⧸
          Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra))),
      ψ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp φ.toRingHom ∧
      red.comp (Ideal.Quotient.mk _) = Ideal.Quotient.mk _ ∧
      ψ.comp c.toRingHom = red.comp j.toRingHom ∧
      cmod.comp (Ideal.Quotient.mk _) = c.toRingHom ∧
      (∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i)) := by
  classical
  let D := d.liftingAlgebra
  let L₁ := Ideal.span ({algebraMap R Λ π} : Set Λ)
  let L₂ := Ideal.span ({algebraMap R Λ (π ^ 2)} : Set Λ)
  let D₁ := Ideal.span ({algebraMap R D π} : Set D)
  let R₂ := Ideal.span ({π ^ 2} : Set R)
  let q₂ := Ideal.Quotient.mkₐ R L₂
  let q₁ := Ideal.Quotient.mkₐ R L₁
  let qD := Ideal.Quotient.mkₐ R D₁
  let mapBar := MvPolynomial.mapAlgHom (σ := Fin d.n) (Ideal.Quotient.mkₐ R R₂)
  let pres := (d.ε.restrictScalars R).comp mapBar
  have hlam : ∀ i : Fin d.n, ∃ lam : Λ, q₂ lam = j (d.ε (MvPolynomial.X i)) := by
    intro i
    exact Ideal.Quotient.mk_surjective _
  choose lam hlam using hlam
  let evP : MvPolynomial (Fin d.n) R →ₐ[R] Λ := MvPolynomial.aeval lam
  have hevP : q₂.comp evP = j.comp pres := by
    ext i
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    simp only [evP, MvPolynomial.aeval_X]
    change q₂ (lam i) = j (d.ε (mapBar (MvPolynomial.X i)))
    have hm : mapBar (MvPolynomial.X i) = MvPolynomial.X i := by
      simp [mapBar, MvPolynomial.mapAlgHom_apply]
    rw [hm]
    exact hlam i
  have hfzero : ∀ l : Fin d.m, pres (d.f l) = 0 := by
    intro l
    change d.ε (d.reduced (d.f l)) = 0
    apply RingHom.mem_ker.mp
    change d.reduced (d.f l) ∈ RingHom.ker d.ε.toRingHom
    rw [hd.kernel]
    exact Ideal.subset_span ⟨l, rfl⟩
  have hμ : ∀ l : Fin d.m, ∃ μ : Λ,
      evP (d.f l) = algebraMap R Λ π ^ 2 * μ := by
    intro l
    have hz : q₂ (evP (d.f l)) = 0 := by
      change (q₂.comp evP) (d.f l) = 0
      rw [hevP]
      change j (pres (d.f l)) = 0
      rw [hfzero, map_zero]
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
    obtain ⟨μ, hμ⟩ := Ideal.mem_span_singleton.mp hmem
    exact ⟨μ, by simpa [map_pow] using hμ⟩
  choose μ hμ using hμ
  let pπ := algebraMap R Λ π
  let evQ : d.polynomial →ₐ[R] Λ :=
    MvPolynomial.aeval (Sum.elim lam (fun l ↦ pπ * μ l))
  have hincl : evQ.comp d.includeX = evP := by
    ext i
    simp [evQ, PopescuLiftPresentation.includeX, evP]
  have hkill : d.definingIdeal ≤ RingHom.ker evQ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨t, rfl⟩
    change evQ (d.equation t) = 0
    cases t with
    | inl l =>
      rw [PopescuLiftPresentation.equation, map_sub, map_mul]
      simp only [evQ, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Sum.elim_inr]
      change evQ (d.includeX (d.f l)) - pπ * (pπ * μ l) = 0
      have he : evQ (d.includeX (d.f l)) = evP (d.f l) := congrArg (fun f ↦ f (d.f l)) hincl
      rw [he, hμ]
      dsimp [pπ]
      ring
    | inr kl =>
      rcases kl with ⟨k, l⟩
      let Y := evP (d.a k) * μ l - (∑ j ∈ d.E k, evP (d.h k l j) * μ j) -
        evP (d.g k l)
      have hrel := congrArg evP (hd.relation k l)
      simp only [map_mul, map_add, map_sum] at hrel
      rw [show evP (MvPolynomial.C (π ^ 2)) = pπ ^ 2 by simp [evP, pπ]] at hrel
      have hY : Y * pπ ^ 2 = 0 := by
        dsimp [Y]
        simp only [sub_mul, Finset.sum_mul]
        have ht : ∀ j, evP (d.h k l j) * μ j * pπ ^ 2 =
            evP (d.h k l j) * evP (d.f j) := by
          intro j
          rw [hμ]
          dsimp [pπ]
          ring
        simp_rw [ht]
        rw [hμ] at hrel
        dsimp [pπ] at *
        linear_combination hrel
      have hAnn : Y ∈ Module.annihilator Λ (Ideal.span ({pπ ^ 2} : Set Λ)) :=
        (Submodule.mem_annihilator_span_singleton _ _).mpr hY
      have hAnn' : Y ∈ Module.annihilator Λ (Ideal.span ({pπ} : Set Λ)) := by
        rw [hAnnΛ]
        simpa [pπ, map_pow] using hAnn
      have hY' : Y * pπ = 0 := (Submodule.mem_annihilator_span_singleton _ _).mp hAnn'
      rw [PopescuLiftPresentation.equation]
      simp only [map_sub, map_mul, map_sum]
      have he : ∀ u, evQ (d.includeX u) = evP u := fun u ↦ congrArg (fun f ↦ f u) hincl
      simp_rw [he]
      simp only [evQ, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Sum.elim_inr]
      change evP (d.a k) * (pπ * μ l) -
        (∑ j ∈ d.E k, evP (d.h k l j) * (pπ * μ j)) - pπ * evP (d.g k l) = 0
      have ht : ∀ j, evP (d.h k l j) * (pπ * μ j) = pπ * (evP (d.h k l j) * μ j) := by
        intro j
        ring
      simp_rw [ht]
      rw [← Finset.mul_sum]
      dsimp [Y] at hY'
      linear_combination hY'
  let φ₀ := Ideal.Quotient.liftₐ d.definingIdeal evQ hkill
  let φ : D →ₐ[R] Λ := φ₀.comp ULift.algEquiv.toAlgHom
  have hπD : qD (algebraMap R D π) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hπ : algebraMap R (D ⧸ D₁) π = 0 := hπD
  have hb : R₂ ≤ RingHom.ker (Algebra.ofId R (D ⧸ D₁)).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    change algebraMap R (D ⧸ D₁) (π ^ 2) = 0
    rw [map_pow, hπ, zero_pow (by decide)]
  let base := Ideal.Quotient.liftₐ R₂ (Algebra.ofId R (D ⧸ D₁)) hb
  let : Algebra (R ⧸ R₂) (D ⧸ D₁) := base.toRingHom.toAlgebra
  have : IsScalarTower R (R ⧸ R₂) (D ⧸ D₁) := IsScalarTower.of_algHom base
  let evBar : MvPolynomial (Fin d.n) (R ⧸ R₂) →ₐ[R ⧸ R₂] (D ⧸ D₁) :=
    MvPolynomial.aeval (fun i ↦ qD (d.x i))
  let qQ : d.polynomial →ₐ[R] D :=
    ULift.algEquiv.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R d.definingIdeal)
  let evX : MvPolynomial (Fin d.n) R →ₐ[R] (D ⧸ D₁) := (qD.comp qQ).comp d.includeX
  have hebar : (evBar.restrictScalars R).comp mapBar = evX := by
    ext i
    simp [evBar, evX, qQ, PopescuLiftPresentation.includeX,
      PopescuLiftPresentation.x, AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply,
      mapBar]
    rfl
  have hzero : ∀ l : Fin d.m, evX (d.f l) = 0 := by
    intro l
    have hQ : qQ (d.equation (.inl l)) = 0 := by
      have hmem : d.equation (.inl l) ∈ d.definingIdeal :=
        Ideal.subset_span ⟨.inl l, rfl⟩
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      exact congrArg (ULift.algEquiv (R := R)).symm hz
    have hD := congrArg qD hQ
    rw [PopescuLiftPresentation.equation, map_sub, map_mul] at hD
    simp only [map_sub, map_mul, map_zero] at hD
    have hC : qD (qQ (MvPolynomial.C π)) = 0 := by
      change qD (qQ (algebraMap R d.polynomial π)) = 0
      rw [qQ.commutes, hπD]
    rw [hC, zero_mul, sub_zero] at hD
    exact hD
  have hk : RingHom.ker d.ε.toRingHom ≤ RingHom.ker evBar.toRingHom := by
    rw [hd.kernel]
    apply Ideal.span_le.mpr
    rintro _ ⟨l, rfl⟩
    change evBar (mapBar (d.f l)) = 0
    have hh := congrArg (fun f ↦ f (d.f l)) hebar
    change evBar (mapBar (d.f l)) = evX (d.f l) at hh
    rw [hh, hzero]
  let cbar := (AlgHom.liftOfSurjective d.ε hd.surjective evBar hk).restrictScalars R
  have hc : ∀ i : Fin d.n, cbar (d.ε (MvPolynomial.X i)) = qD (d.x i) := by
    intro i
    change AlgHom.liftOfSurjective d.ε hd.surjective evBar hk (d.ε (MvPolynomial.X i)) = _
    rw [AlgHom.liftOfSurjective_apply]
    exact MvPolynomial.aeval_X _ _
  have hred : L₂ ≤ RingHom.ker q₁.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    change q₁ (algebraMap R Λ (π ^ 2)) = 0
    rw [map_pow, map_pow]
    have hp : q₁ (algebraMap R Λ π) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [hp, zero_pow (by decide)]
  let red := Ideal.Quotient.liftₐ L₂ q₁ hred
  have hψ : D₁ ≤ RingHom.ker (q₁.comp φ).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    change q₁ (φ (algebraMap R D π)) = 0
    rw [φ.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let ψ := Ideal.Quotient.liftₐ D₁ (q₁.comp φ) hψ
  have hcm : Ideal.span ({algebraMap R Cbar π} : Set Cbar) ≤
      RingHom.ker cbar.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    change cbar (algebraMap R Cbar π) = 0
    rw [cbar.commutes]
    exact hπ
  let cmod := Ideal.Quotient.lift _ cbar.toRingHom hcm
  have hφx : ∀ i : Fin d.n, φ (d.x i) = lam i := by
    intro i
    change φ₀ (Ideal.Quotient.mk d.definingIdeal (MvPolynomial.X (.inl i))) = lam i
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact MvPolynomial.aeval_X _ _
  have hs : (ψ.comp cbar).comp pres = (red.comp j).comp pres := by
    ext i
    change ψ (cbar (pres (MvPolynomial.X i))) = red (j (pres (MvPolynomial.X i)))
    have hpresX : pres (MvPolynomial.X i) = d.ε (MvPolynomial.X i) := by
      change d.ε (mapBar (MvPolynomial.X i)) = _
      simp [mapBar, MvPolynomial.mapAlgHom_apply]
    rw [hpresX, hc]
    change q₁ (φ (d.x i)) = red (j (d.ε (MvPolynomial.X i)))
    rw [hφx, ← hlam]
    rfl
  have hpres : Function.Surjective pres :=
    hd.surjective.comp (MvPolynomial.map_surjective _ (Ideal.Quotient.mk_surjective))
  have hsquare : ψ.comp cbar = red.comp j := by
    apply AlgHom.ext
    intro z
    obtain ⟨u, rfl⟩ := hpres z
    exact congrArg (fun f ↦ f u) hs
  refine ⟨φ, ψ.toRingHom, red.toRingHom, cbar, cmod, ?_, ?_, ?_, ?_, hc⟩
  · ext z
    rfl
  · ext z
    rfl
  · exact congrArg AlgHom.toRingHom hsquare
  · ext z
    rfl

end Algebra
