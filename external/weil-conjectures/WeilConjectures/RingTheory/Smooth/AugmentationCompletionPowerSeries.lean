/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.Defs

import WeilConjectures.RingTheory.Smooth.AugmentationFirstOrderCoordinates
import WeilConjectures.RingTheory.Smooth.AugmentationPolynomialTruncations
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Power-series coordinates on the completion of a smooth augmented algebra

Source: Stacks Project, Tag 05D5.
(blueprint: lem-sbc-smooth-augmentation-completion-power-series)
-/

@[expose] public section

universe u

namespace Algebra

private theorem eval_factor {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal S) {m k : ℕ} (h : m ≤ k)
    (x : AdicCompletion I S) :
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) (AdicCompletion.evalₐ I k x) =
      AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on I S with
  | h a =>
    simp only [AdicCompletion.evalₐ_mk]
    exact AdicCompletion.Ideal.mk_eq_mk I h a

/-- Compatible bijections on all polynomial truncations induce completion coordinates.

Source: Stacks Project, Tag 05D5, final inverse-limit paragraph.

Proof: Put I = ker ε and J the variables ideal. The truncation bijections are
compatible by construction, because they are all induced by the same evaluation map f.
Taking inverse limits gives an algebra equivalence between the I-adic completion of C
and the J-adic completion of the multivariate polynomial ring. The canonical equivalence
`MvPowerSeries.toAdicCompletionAlgEquiv` identifies the latter with the multivariate
power-series ring. Under the quotient maps modulo I, respectively J, the evaluation map
is the identity on B; applying constant coefficient therefore gives ε on every element
of C. This also covers n = 0, where both inverse systems have positive levels B. -/
private theorem exists_completion_algEquiv_of_bijective_truncations
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    (ε : C →ₐ[B] B) (n : ℕ)
    (f : MvPolynomial (Fin n) B →ₐ[B] C)
    (hf : MvPolynomial.idealOfVars (Fin n) B ≤
      (RingHom.ker ε.toRingHom).comap f.toRingHom)
    (htrunc : ∀ k : ℕ, Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ k) f
        ((pow_le_pow_left' hf k).trans (Ideal.le_comap_pow f.toRingHom k)))) :
    ∃ e : AdicCompletion (RingHom.ker ε.toRingHom) C ≃ₐ[B]
        MvPowerSeries (Fin n) B,
      ∀ c : C, MvPowerSeries.constantCoeff
        (e (algebraMap C (AdicCompletion (RingHom.ker ε.toRingHom) C) c)) = ε c := by
  classical
  let I := RingHom.ker ε.toRingHom
  let J := MvPolynomial.idealOfVars (Fin n) B
  let q (k : ℕ) : MvPolynomial (Fin n) B ⧸ J ^ k →ₐ[B] C ⧸ I ^ k :=
    Ideal.quotientMapₐ (I ^ k) f
      ((pow_le_pow_left' hf k).trans (Ideal.le_comap_pow f.toRingHom k))
  let e (k : ℕ) := AlgEquiv.ofBijective (q k) (htrunc k)
  have hq {m k : ℕ} (h : m ≤ k) (x : MvPolynomial (Fin n) B ⧸ J ^ k) :
      Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right h) (e k x) =
        e m (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right h) x) := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have he {m k : ℕ} (h : m ≤ k) (x : C ⧸ I ^ k) :
      Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right h) ((e k).symm x) =
        (e m).symm (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right h) x) := by
    apply (e m).injective
    rw [← hq h, (e k).apply_symm_apply, (e m).apply_symm_apply]
  let g := AdicCompletion.liftAlgHom I
    (fun k ↦ (e k).toAlgHom.comp ((AdicCompletion.evalₐ J k).restrictScalars B))
    (fun {m k} h ↦ AlgHom.ext fun x ↦ by
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom]
      rw [hq h, eval_factor J h])
  let g' := AdicCompletion.liftAlgHom J
    (fun k ↦ (e k).symm.toAlgHom.comp ((AdicCompletion.evalₐ I k).restrictScalars B))
    (fun {m k} h ↦ AlgHom.ext fun x ↦ by
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom]
      rw [he h, eval_factor I h])
  have hg (x : AdicCompletion J (MvPolynomial (Fin n) B)) : g' (g x) = x := by
    apply AdicCompletion.ext_evalₐ
    intro k
    simp [g, g', AdicCompletion.evalₐ_liftAlgHom]
  have hg' (x : AdicCompletion I C) : g (g' x) = x := by
    apply AdicCompletion.ext_evalₐ
    intro k
    simp [g, g', AdicCompletion.evalₐ_liftAlgHom]
  let E : AdicCompletion J (MvPolynomial (Fin n) B) ≃ₐ[B] AdicCompletion I C :=
    { g with invFun := g', left_inv := hg, right_inv := hg' }
  let P := (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) B).restrictScalars B
  refine ⟨E.symm.trans P.symm, ?_⟩
  intro c
  let x := algebraMap C (AdicCompletion I C) c
  let t := P.symm (g' x)
  have ht : P t = g' x := P.apply_symm_apply _
  have h₁ : e 1 (Ideal.Quotient.mk (J ^ 1) (t.truncTotal 1)) =
      Ideal.Quotient.mk (I ^ 1) c := by
    have h := congrArg (fun z ↦ AdicCompletion.evalₐ J 1 z) ht
    have hleft : AdicCompletion.evalₐ J 1 (P t) =
        Ideal.Quotient.mk (J ^ 1) (t.truncTotal 1) := by
      change AdicCompletion.evalₐ J 1 (MvPowerSeries.toAdicCompletion (Fin n) B t) = _
      exact AdicCompletion.evalₐ_liftAlgHom _ (MvPowerSeries.truncTotalAlgHom (Fin n) B)
        (fun h ↦ AlgHom.ext fun _ ↦ by
          simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
            MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) _) 1 t
    rw [hleft] at h
    have hright : AdicCompletion.evalₐ J 1 (g' x) =
        (e 1).symm (Ideal.Quotient.mk (I ^ 1) c) := by
      simp [g', x, AdicCompletion.algebraMap_apply]
    rw [hright] at h
    simpa only [AlgEquiv.apply_symm_apply] using congrArg (e 1) h
  have hpoly : ε.toRingHom.comp f.toRingHom = MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp
    · intro i
      have hi : f (MvPolynomial.X i) ∈ I :=
        hf (Ideal.subset_span ⟨i, rfl⟩)
      rw [RingHom.comp_apply, MvPolynomial.constantCoeff_X]
      change ε (f (MvPolynomial.X i)) = 0
      exact RingHom.mem_ker.mp hi
  have hval : MvPolynomial.constantCoeff (t.truncTotal 1) = ε c := by
    let l := Ideal.Quotient.lift (I ^ 1) ε.toRingHom (by
      intro a ha
      exact (show a ∈ I from (by simpa using ha)))
    have h := congrArg l h₁
    change ε (f (t.truncTotal 1)) = ε c at h
    exact (RingHom.congr_fun hpoly (t.truncTotal 1)).symm.trans h
  change MvPowerSeries.constantCoeff t = ε c
  rw [← hval]
  change MvPowerSeries.constantCoeff t = AddMonoidAlgebra.coeff (t.truncTotal 1) 0
  rw [MvPowerSeries.coeff_truncTotal _ (by simp)]
  exact (MvPowerSeries.coeff_zero_eq_constantCoeff_apply t).symm

/-- The augmentation-adic completion of a smooth algebra over a local ring has
power-series coordinates preserving the augmentation.

Source: Stacks Project, Tag 05D5, including its explicit choice of generators.
(blueprint: lem-sbc-smooth-augmentation-completion-power-series)

Proof: Put I = ker ε. The split conormal sequence identifies I/I² with
Ω[C/B] ⊗[C,ε] B, a finite projective B-module. Over the local ring it is free
of some finite rank n. Lift a basis to I. Sending the variables to these lifts
induces Ψ : B[[X₁,...,Xₙ]] → Ĉ. Modulo the squares of the two ideals Ψ is an
isomorphism. Inductively, formal smoothness lifts the inverse modulo the k-th
power to the next power. The resulting composite on truncated power series
sends Xᵢ to Xᵢ plus a term of degree at least k; subtracting these terms gives
its inverse. Surjectivity of Ψ on each truncation then makes the lifted map an
inverse of Ψ. These inverses are compatible, so inverse limits give an algebra
isomorphism. Take its inverse for e. Because the chosen lifts lie in I,
constant coefficient after e agrees with ε on C. Rank zero is allowed and
produces the constant power-series ring. -/
theorem exists_augmented_completion_powerSeries
    (B C : Type u) [CommRing B] [IsLocalRing B] [CommRing C] [Algebra B C]
    [Smooth B C] (ε : C →ₐ[B] B) :
    ∃ (n : ℕ) (e : AdicCompletion (RingHom.ker ε.toRingHom) C ≃ₐ[B]
        MvPowerSeries (Fin n) B),
      ∀ c : C, MvPowerSeries.constantCoeff
        (e (algebraMap C (AdicCompletion (RingHom.ker ε.toRingHom) C) c)) = ε c := by
  obtain ⟨n, f, hf, h₂⟩ := exists_augmented_firstOrder_polynomial_coordinates B C ε
  obtain ⟨e, he⟩ := exists_completion_algEquiv_of_bijective_truncations B C ε n f hf
    (bijective_augmented_polynomial_truncations B C ε n f hf h₂)
  exact ⟨n, e, he⟩

end Algebra
