/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Defs

import Mathlib.RingTheory.LocalRing.Module

/-!
# First-order coordinates for a smooth augmented algebra

Source: Stacks Project, Tag 05D5, the choice of basis lifts and the map Ψ₂.
(blueprint: lem-sbc-smooth-augmentation-first-order-coordinates)
-/

@[expose] public section

universe u

namespace Algebra

-- The section splits the conormal map. A retract of the finite projective
-- pulled-back differentials is finite projective, hence free over the local base.
private theorem augmented_cotangent_finite_free
    (B C : Type u) [CommRing B] [IsLocalRing B] [CommRing C] [Algebra B C]
    [Smooth B C] (ε : C →ₐ[B] B) :
    Module.Finite B (RingHom.ker ε.toRingHom).Cotangent ∧
      Module.Free B (RingHom.ker ε.toRingHom).Cotangent := by
  let : Algebra C B := ε.toAlgebra
  let : IsScalarTower B C B := IsScalarTower.of_algebraMap_eq' ε.comp_algebraMap.symm
  have hsurj : Function.Surjective (algebraMap C B) := by
    intro r
    exact ⟨algebraMap B C r, ε.commutes r⟩
  let Q := C ⧸ RingHom.ker ε.toRingHom ^ 2
  let g : B →ₐ[B] Q := Algebra.ofId B Q
  have hg : (IsScalarTower.toAlgHom B C B).kerSquareLift.comp g = AlgHom.id B B := by
    exact Subsingleton.elim _ _
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := B)
    (P := C) (S := B) hsurj).symm ⟨g, hg⟩
  let i := (KaehlerDifferential.kerCotangentToTensor B C B).restrictScalars B
  let s := l.restrictScalars B
  have hsplit : s.comp i = LinearMap.id := by
    ext x
    exact LinearMap.congr_fun hl x
  let : Module.Finite B (RingHom.ker ε.toRingHom).Cotangent :=
    Module.Finite.of_surjective s (fun x ↦ ⟨i x, LinearMap.congr_fun hsplit x⟩)
  let : Module.Projective B (RingHom.ker ε.toRingHom).Cotangent :=
    Module.Projective.of_split i s hsplit
  exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩

private theorem firstOrder_remainder {R : Type u} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) :
    p - (MvPolynomial.C (p.coeff 0) +
      ∑ i, MvPolynomial.C (p.coeff (Finsupp.single i 1)) * MvPolynomial.X i) ∈
      MvPolynomial.idealOfVars (Fin n) R ^ 2 := by
  classical
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro d hd
  have hd' : d.degree = 0 ∨ d.degree = 1 := by omega
  rcases hd' with h0 | h1
  · have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    subst d
    simp [MvPolynomial.coeff_C_mul]
  · have hdmem : d ∈ Set.range (fun i : Fin n ↦ Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]
      exact h1
    obtain ⟨i, rfl⟩ := hdmem
    have hi : Finsupp.single i 1 ≠ (0 : Fin n →₀ ℕ) := by simp
    simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C,
      MvPolynomial.coeff_X, Ne.symm hi, Finsupp.single_eq_single_iff]

/-- Polynomial coordinates on the square-zero augmentation quotient.

Source: Stacks Project, Tag 05D5, proof through the assertion that Ψ₂ is an isomorphism.
(blueprint: lem-sbc-smooth-augmentation-first-order-coordinates)

Proof: Write I = ker ε. The split conormal sequence for B → C → B identifies I/I²
with Ω[C/B] tensored along ε with B. Smoothness makes this module finite projective.
Since B is local, it is free of finite rank n. Lift a basis to elements fᵢ of I and
let f be polynomial evaluation at these elements. Thus f sends the variables ideal
J into I. The augmentation splits C/I² as B ⊕ I/I², with square-zero second summand.
Likewise B[X]/J² is B ⊕ Bⁿ, with square-zero second summand. Evaluation is the identity
on B and the chosen basis map on the second summands, hence bijective. If n = 0,
both second summands vanish and evaluation on these quotients is the identity of B.
No finite generation of I itself or Noetherian hypothesis is used. -/
theorem exists_augmented_firstOrder_polynomial_coordinates
    (B C : Type u) [CommRing B] [IsLocalRing B] [CommRing C] [Algebra B C]
    [Smooth B C] (ε : C →ₐ[B] B) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) B →ₐ[B] C)
      (hf : MvPolynomial.idealOfVars (Fin n) B ≤
        (RingHom.ker ε.toRingHom).comap f.toRingHom),
      Function.Bijective (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ 2) f
        ((pow_le_pow_left' hf 2).trans (Ideal.le_comap_pow f.toRingHom 2))) := by
  classical
  let I := RingHom.ker ε.toRingHom
  obtain ⟨hfinite, hfree⟩ := augmented_cotangent_finite_free B C ε
  let : Module.Finite B I.Cotangent := hfinite
  let : Module.Free B I.Cotangent := hfree
  let n := Module.finrank B I.Cotangent
  let b : Module.Basis (Fin n) B I.Cotangent := Module.finBasis B I.Cotangent
  choose x hx using fun i ↦ I.toCotangent_surjective (b i)
  let f : MvPolynomial (Fin n) B →ₐ[B] C := MvPolynomial.aeval fun i ↦ (x i : C)
  have hf : MvPolynomial.idealOfVars (Fin n) B ≤ I.comap f.toRingHom := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change f (MvPolynomial.X i) ∈ I
    simp only [f, MvPolynomial.aeval_X]
    exact (x i).property
  have hpow := (pow_le_pow_left' hf 2).trans (Ideal.le_comap_pow f.toRingHom 2)
  have hmap (p : MvPolynomial (Fin n) B) (hp : p ∈ MvPolynomial.idealOfVars (Fin n) B ^ 2) :
      f p ∈ I ^ 2 := hpow hp
  have hεx (i : Fin n) : ε (x i) = 0 := (x i).property
  have hcot (v : Fin n → B) :
      I.toCotangent (∑ i, v i • x i) = ∑ i, v i • b i := by
    simp only [map_sum, LinearMap.map_smul_of_tower, hx]
  refine ⟨n, f, hf, ?_, ?_⟩
  · apply (injective_iff_map_eq_zero _).mpr
    intro q hq
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hp : f p ∈ I ^ 2 := by
      change Ideal.Quotient.mk (I ^ 2) (f p) = 0 at hq
      exact Ideal.Quotient.eq_zero_iff_mem.mp hq
    let v : Fin n → B := fun i ↦ p.coeff (Finsupp.single i 1)
    have hr := firstOrder_remainder p
    have hn : f (MvPolynomial.C (p.coeff 0) +
        ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i) ∈ I ^ 2 := by
      have hh := (I ^ 2).sub_mem hp (hmap _ hr)
      convert hh using 1
      rw [map_sub]
      ring
    have h0 : p.coeff 0 = 0 := by
      have hh : ε (f (MvPolynomial.C (p.coeff 0) +
          ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i)) = 0 :=
        Ideal.pow_le_self two_ne_zero hn
      simpa [f, hεx] using hh
    have hz : ((∑ i, v i • x i : I) : C) ∈ I ^ 2 := by
      simpa [f, h0, Algebra.smul_def] using hn
    have hvsum : (∑ i, v i • b i) = 0 := by
      rw [← hcot]
      exact (I.toCotangent_eq_zero _).mpr hz
    have hv (i : Fin n) : v i = 0 := by
      have hh := congrArg (fun t ↦ b.repr t i) hvsum
      simpa [Module.Basis.repr_sum_self, Finsupp.single_apply,
        Finsupp.finsetSum_apply] using hh
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hv' (i : Fin n) : p.coeff (Finsupp.single i 1) = 0 := hv i
    simpa [hv', h0] using hr
  · intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    have ha : a - algebraMap B C (ε a) ∈ I := by
      change ε (a - algebraMap B C (ε a)) = 0
      simp
    let z : I := ⟨a - algebraMap B C (ε a), ha⟩
    let v : Fin n → B := fun i ↦ b.repr (I.toCotangent z) i
    have hz : I.toCotangent (∑ i, v i • x i) = I.toCotangent z := by
      rw [hcot]
      exact b.sum_repr _
    have hdiff : ((∑ i, v i • x i : I) : C) - (z : C) ∈ I ^ 2 :=
      I.toCotangent_eq.mp hz
    refine ⟨Ideal.Quotient.mk (MvPolynomial.idealOfVars (Fin n) B ^ 2)
      (MvPolynomial.C (ε a) + ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i), ?_⟩
    change Ideal.Quotient.mk (I ^ 2) (f _) = Ideal.Quotient.mk (I ^ 2) a
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    convert hdiff using 1
    simp only [f, map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Submodule.coe_sum, Submodule.coe_smul_of_tower, Algebra.smul_def, z]
    ring

end Algebra
