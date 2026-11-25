/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import WeilConjectures.RingTheory.Smooth.AugmentationPolynomialTruncationsSurjective

@[expose] public section

universe u

namespace Algebra

/-- The augmentation identifies the degree-one quotient with the base ring. -/
private theorem injective_augmented_polynomial_truncations_low_degree
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    (ε : C →ₐ[B] B) (n : ℕ)
    (f : MvPolynomial (Fin n) B →ₐ[B] C)
    (hf : MvPolynomial.idealOfVars (Fin n) B ≤
      (RingHom.ker ε.toRingHom).comap f.toRingHom) :
    ∀ k : ℕ, k < 2 → Function.Injective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ k) f
        ((pow_le_pow_left' hf k).trans (Ideal.le_comap_pow f.toRingHom k))) := by
  have he : ε.toRingHom.comp f.toRingHom = MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp
    · intro i
      have hXi : MvPolynomial.X i ∈ MvPolynomial.idealOfVars (Fin n) B :=
        Ideal.subset_span ⟨i, rfl⟩
      change ε (f (MvPolynomial.X i)) = MvPolynomial.constantCoeff (MvPolynomial.X i)
      rw [MvPolynomial.constantCoeff_X]
      exact hf hXi
  intro k hk
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · exact Ideal.quotientMap_injective'
      (H := (pow_le_pow_left' hf 0).trans (Ideal.le_comap_pow f.toRingHom 0)) (by simp)
  · apply Ideal.quotientMap_injective'
      (H := (pow_le_pow_left' hf 1).trans (Ideal.le_comap_pow f.toRingHom 1))
    intro p hp
    simp only [pow_one] at hp ⊢
    have hp' : MvPolynomial.constantCoeff p = 0 := by
      rw [← he]
      exact hp
    rw [← pow_one (MvPolynomial.idealOfVars (Fin n) B)]
    apply (MvPolynomial.mem_pow_idealOfVars_iff' 1 p).mpr
    intro d hd
    have hd' : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst d
    exact hp'

/-- Ideal-power induction makes a sufficiently small correction injective. -/
private theorem injective_near_identity_nilpotent
    {A : Type u} [CommRing A] (L : Ideal A) (r : ℕ) (hr : 2 ≤ r)
    (e : A →+* A) (he : ∀ x, e x - x ∈ L ^ r) (hnil : L ^ (r + 1) = ⊥) :
    Function.Injective e := by
  have hfil : ∀ k : ℕ, ∀ x ∈ L ^ (k + 1), e x - x ∈ L ^ (r + k) := by
    intro k
    induction k with
    | zero =>
      intro x _
      simpa only [Nat.add_zero] using he x
    | succ k ih =>
      intro x hx
      rw [pow_succ'] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        have heb : e b ∈ L ^ (k + 1) := by
          have hdb := Ideal.pow_le_pow_right (show k + 1 ≤ r + k by omega) (ih b hb)
          simpa only [sub_add_cancel] using (L ^ (k + 1)).add_mem hdb hb
        have h₁ : (e a - a) * e b ∈ L ^ (r + (k + 1)) := by
          rw [pow_add]
          exact Ideal.mul_mem_mul (he a) heb
        have h₂ : a * (e b - b) ∈ L ^ (r + (k + 1)) := by
          have hh : a * (e b - b) ∈ L ^ 1 * L ^ (r + k) :=
            Ideal.mul_mem_mul (by simpa only [pow_one] using ha) (ih b hb)
          rw [← pow_add] at hh
          convert hh using 1
          congr 1
          omega
        convert (L ^ (r + (k + 1))).add_mem h₁ h₂ using 1
        rw [map_mul]
        ring
      · intro a b ha hb
        convert (L ^ (r + (k + 1))).add_mem ha hb using 1
        rw [map_add]
        ring
  intro x y hxy
  let z := x - y
  have hz : e z = 0 := by simp only [z, map_sub, hxy, sub_self]
  have hzr : z ∈ L ^ r := by
    have hh := he z
    rw [hz, zero_sub] at hh
    exact (L ^ r).neg_mem_iff.mp hh
  have hh := hfil (r - 1) z (by rw [Nat.sub_add_cancel (by omega)]; exact hzr)
  have hh' : e z - z ∈ L ^ (r + 1) :=
    Ideal.pow_le_pow_right (show r + 1 ≤ r + (r - 1) by omega) hh
  rw [hnil, Ideal.mem_bot, hz, zero_sub, neg_eq_zero] at hh'
  exact sub_eq_zero.mp hh'

/-- Apply the nilpotent correction estimate to the image of the variables ideal. -/
private theorem injective_polynomial_truncation_near_identity
    (B : Type u) [CommRing B] (n r : ℕ) (hr : 2 ≤ r)
    (e : (MvPolynomial (Fin n) B ⧸ MvPolynomial.idealOfVars (Fin n) B ^ (r + 1))
      →ₐ[B] (MvPolynomial (Fin n) B ⧸ MvPolynomial.idealOfVars (Fin n) B ^ (r + 1)))
    (he : (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right r.le_succ)).comp e =
      Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right r.le_succ)) :
    Function.Injective e := by
  let J := MvPolynomial.idealOfVars (Fin n) B
  let L := J.map (Ideal.Quotient.mk (J ^ (r + 1)))
  let π : (MvPolynomial (Fin n) B ⧸ J ^ (r + 1)) →ₐ[B]
      (MvPolynomial (Fin n) B ⧸ J ^ r) :=
    Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right r.le_succ)
  have hnil : L ^ (r + 1) = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have he' : ∀ x, e x - x ∈ L ^ r := by
    intro x
    have hx := AlgHom.congr_fun he x
    change π (e x) = π x at hx
    have hd : e x - x ∈ RingHom.ker π.toRingHom := by
      change π (e x - x) = 0
      rw [map_sub, hx, sub_self]
    have hker : RingHom.ker π.toRingHom = (J ^ r).map
        (Ideal.Quotient.mk (J ^ (r + 1))) :=
      Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right r.le_succ)
    rw [hker, Ideal.map_pow] at hd
    exact hd
  exact injective_near_identity_nilpotent L r hr e.toRingHom he' hnil

/-- Lift the degree-r inverse and descend it through the next augmentation power. -/
private theorem exists_augmented_truncation_inverse_lift
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    [FormallySmooth B C] (ε : C →ₐ[B] B) (n r : ℕ) (hr : 2 ≤ r)
    (f : MvPolynomial (Fin n) B →ₐ[B] C)
    (hf : MvPolynomial.idealOfVars (Fin n) B ≤
      (RingHom.ker ε.toRingHom).comap f.toRingHom)
    (hbij : Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ r) f
        ((pow_le_pow_left' hf r).trans (Ideal.le_comap_pow f.toRingHom r)))) :
    ∃ g : (C ⧸ (RingHom.ker ε.toRingHom) ^ (r + 1)) →ₐ[B]
        (MvPolynomial (Fin n) B ⧸ MvPolynomial.idealOfVars (Fin n) B ^ (r + 1)),
      (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right r.le_succ)).comp
        (g.comp (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ (r + 1)) f
          ((pow_le_pow_left' hf (r + 1)).trans
            (Ideal.le_comap_pow f.toRingHom (r + 1))))) =
      Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right r.le_succ)  := by
  classical
  let P := MvPolynomial (Fin n) B
  let J : Ideal P := MvPolynomial.idealOfVars (Fin n) B
  let I : Ideal C := RingHom.ker ε.toRingHom
  let π : (P ⧸ J ^ (r + 1)) →ₐ[B] (P ⧸ J ^ r) :=
    Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right r.le_succ)
  let f₀ := Ideal.quotientMapₐ (I ^ r) f
    ((pow_le_pow_left' hf r).trans (Ideal.le_comap_pow f.toRingHom r))
  let e := AlgEquiv.ofBijective f₀ hbij
  let q := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ B (I ^ r))
  have hπsurj : Function.Surjective π :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right r.le_succ)
  have hπker : RingHom.ker π.toRingHom = (J ^ r).map
      (Ideal.Quotient.mk (J ^ (r + 1))) := by
    exact Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right r.le_succ)
  have hπnil : IsNilpotent (RingHom.ker π.toRingHom) := by
    refine ⟨2, ?_⟩
    change RingHom.ker π.toRingHom ^ 2 = ⊥
    rw [hπker, ← Ideal.map_pow, ← pow_mul, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact Ideal.pow_le_pow_right (by omega)
  let t := FormallySmooth.liftOfSurjective q π hπsurj hπnil
  have ht : ∀ c, π (t c) = q c :=
    FormallySmooth.liftOfSurjective_apply q π hπsurj hπnil
  have htJ : I ≤ (J.map (Ideal.Quotient.mk (J ^ (r + 1)))).comap t.toRingHom := by
    intro c hc
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (t c)
    have hred : Ideal.Quotient.mk (J ^ r) p = e.symm (Ideal.Quotient.mk (I ^ r) c) := by
      have hh := ht c
      rw [← hp] at hh
      exact hh
    have hfp : Ideal.Quotient.mk (I ^ r) (f p) = Ideal.Quotient.mk (I ^ r) c := by
      change f₀ (Ideal.Quotient.mk (J ^ r) p) = _
      rw [← AlgEquiv.ofBijective_apply f₀ hbij]
      change e (Ideal.Quotient.mk (J ^ r) p) = _
      rw [hred]
      exact e.apply_symm_apply _
    have hfc : f p ∈ I := by
      have hdiff := (Ideal.Quotient.eq (I := I ^ r)).mp hfp
      have hh := I.add_mem (Ideal.pow_le_self (by omega) hdiff) hc
      simpa only [sub_add_cancel] using hh
    have hinj := injective_augmented_polynomial_truncations_low_degree B C ε n f hf 1
      (by omega)
    have hpJ : p ∈ J := by
      have hz : Ideal.Quotient.mk (J ^ 1) p = 0 := by
        apply hinj
        rw [map_zero]
        change Ideal.Quotient.mk (I ^ 1) (f p) = 0
        rw [pow_one]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hfc
      simpa only [pow_one] using (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    change t c ∈ J.map (Ideal.Quotient.mk (J ^ (r + 1)))
    rw [← hp]
    exact Ideal.mem_map_of_mem _ hpJ
  have htNil : I ^ (r + 1) ≤ RingHom.ker t.toRingHom := by
    have hh := (pow_le_pow_left' htJ (r + 1)).trans
      (Ideal.le_comap_pow t.toRingHom (r + 1))
    rw [← Ideal.map_pow, Ideal.map_quotient_self] at hh
    exact hh
  let g := Ideal.Quotient.liftₐ (I ^ (r + 1)) t htNil
  refine ⟨g, ?_⟩
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change π (t (f p)) = Ideal.Quotient.mk (J ^ r) p
  rw [ht]
  change e.symm (f₀ (Ideal.Quotient.mk (J ^ r) p)) = _
  exact AlgEquiv.ofBijective_symm_apply_apply f₀ hbij _

/-- Formal smoothness gives injectivity of the augmented polynomial truncations.

Source: Stacks Project, Tag 05D5, lifting and correction in the truncation induction.
(blueprint: lem-sbc-formally-smooth-augmentation-truncations-injective)

Proof: The surjectivity component gives surjectivity at every degree. At degree zero
both quotients are zero, and at degree one both augmentations identify the quotients
with B; degree two is the given bijection. Assume bijectivity at degree r ≥ 2.
Lift its inverse composed with C → C/I^r to C → B[X]/J^(r+1) by formal smoothness.
The projection kernel J^r/J^(r+1) is square-zero. Reduction to B shows that this lift
sends I into J/J^(r+1), so it descends through C/I^(r+1). Its composite with f sends
each variable Xᵢ to Xᵢ + δᵢ, with δᵢ in J^r/J^(r+1). Substitution Xᵢ ↦ Xᵢ - δᵢ
inverts this composite: substitution changes a degree-r correction only in degrees
at least 2r-1 ≥ r+1. Thus the composite is injective, and so is f at degree r+1.
Combine this with the separately known surjectivity to continue the induction.
The same calculation uses empty sums for n = 0 and also covers the zero base ring. -/
theorem bijective_augmented_polynomial_truncations_injective
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    [FormallySmooth B C] (ε : C →ₐ[B] B) (n : ℕ)
    (f : MvPolynomial (Fin n) B →ₐ[B] C)
    (hf : MvPolynomial.idealOfVars (Fin n) B ≤
      (RingHom.ker ε.toRingHom).comap f.toRingHom)
    (h₂ : Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ 2) f
        ((pow_le_pow_left' hf 2).trans (Ideal.le_comap_pow f.toRingHom 2)))) :
    ∀ k : ℕ, Function.Injective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ k) f
        ((pow_le_pow_left' hf k).trans (Ideal.le_comap_pow f.toRingHom k))) := by
  have hsurj := bijective_augmented_polynomial_truncations_surjective B C ε n f hf h₂.2
  have hhigh : ∀ r : ℕ, 2 ≤ r → Function.Injective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ r) f
        ((pow_le_pow_left' hf r).trans (Ideal.le_comap_pow f.toRingHom r))) := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => exact h₂.1
    | succ r hr ih =>
      obtain ⟨g, hg⟩ := exists_augmented_truncation_inverse_lift B C ε n r hr f hf
        ⟨ih, hsurj r⟩
      have hinj := injective_polynomial_truncation_near_identity B n r hr
        (g.comp (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ (r + 1)) f
          ((pow_le_pow_left' hf (r + 1)).trans
            (Ideal.le_comap_pow f.toRingHom (r + 1))))) hg
      exact Function.Injective.of_comp hinj
  intro k
  by_cases hk : k < 2
  · exact injective_augmented_polynomial_truncations_low_degree B C ε n f hf k hk
  · exact hhigh k (Nat.le_of_not_gt hk)

end Algebra
