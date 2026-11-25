/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.Algebra.MvPolynomial.PDeriv
import WeilConjectures.RingTheory.PopescuDelocalizeDenominators

/-!
# Polynomial certificates for delocalization

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07F4.
(blueprint: lem-weil-pbc-popescu-delocalize-certificate).
-/

@[expose] public section

universe u v w x

namespace Algebra

open MvPolynomial

private theorem product_mul_mem_scaled_span
    {R : Type u} [CommRing R] {N c : ℕ}
    (f : Fin c → MvPolynomial (Fin N) R) (d : Fin c → R)
    {p : MvPolynomial (Fin N) R} (hp : p ∈ Ideal.span (Set.range f)) :
    C (∏ j, d j) * p ∈ Ideal.span (Set.range (fun j ↦ C (d j) * f j)) := by
  classical
  let I : Ideal (MvPolynomial (Fin N) R) :=
    Ideal.span (Set.range (fun j ↦ C (d j) * f j))
  have hj (j : Fin c) : C (∏ k, d k) * f j ∈ I := by
    have hm := I.mul_mem_left (C (∏ k ∈ Finset.univ.erase j, d k))
      (Ideal.subset_span (show C (d j) * f j ∈ Set.range (fun j ↦ C (d j) * f j)
        from ⟨j, rfl⟩))
    rwa [← mul_assoc, ← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ j)] at hm
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hj j
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using I.add_mem hx hy
  | smul a x _ hx =>
    simpa only [smul_eq_mul, mul_left_comm] using I.mul_mem_left a hx

/-- Turn the denominator-clearing data into polynomial certificates for the quotient.
The output consists entirely of polynomials and their evaluation and ideal identities;
no factorization algebra is chosen here.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07F4, the quotient
construction and the last paragraph verifying the product of denominators.
(blueprint: lem-weil-pbc-popescu-delocalize-certificate).

Proof: take `f`, `l`, `s₀`, `a₀`, `a`, `sg`, `sf` from
`exists_delocalization_denominator_data`. Put the first `c` relations of `F` equal to
`C (sf j).val * f j` and the last `t` equal to the renamed original relations. Their
evaluations vanish: the first ones by the denominator data, the last ones because `l`
agrees with `α` on the generators of `A`. Put `ug = ∏ sg`, `uf = ∏ sf`, and
`s = s₀ * ug * uf`. Every `C uf.val * f j` belongs to the initial relation ideal,
since `uf` is divisible by `sf j`; span induction gives the same assertion for every
polynomial in the ideal `(f)`. Applying this to `∑ a j * f j` and multiplying by `ug`
converts the denominator identity into the Jacobian congruence for `F`: the derivative
of `C (sf j).val * f j` is `C (sf j).val` times the derivative of `f j`, so its determinant
is `C uf.val` times the old determinant. Applying the same span argument to each
`C (sg j).val * g j`, then multiplying by `s₀` and all the other `sg` factors, gives
the remaining-relation condition. Finite products and empty determinants make this
argument valid for empty families as well. -/
theorem exists_delocalization_polynomial_certificate
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    (α : A →ₐ[R] Λ) (S : Submonoid R) {n t m c : ℕ}
    (P : Presentation R A (Fin n) (Fin t)) (hc : c ≤ n + m)
    {D : Type x} [CommRing D] [Algebra (Localization S) D]
    (Q : SubmersivePresentation (Localization S) D (Fin (n + m)) (Fin c))
    (β : Localization (algebraMapSubmonoid A S) →ₐ[Localization S] D)
    (γ : D →ₐ[Localization S] Localization (algebraMapSubmonoid Λ S))
    (hfactor : γ.comp β =
      IsLocalization.mapₐ S (Localization S)
        (Localization (algebraMapSubmonoid A S)) (Localization (algebraMapSubmonoid Λ S)) α)
    (hmap : Q.map = Fin.castLE hc)
    (hval : ∀ i : Fin n, Q.val (Fin.castAdd m i) =
      β (algebraMap A (Localization (algebraMapSubmonoid A S)) (P.val i))) :
    ∃ (F : Fin (c + t) → MvPolynomial (Fin (n + m)) R)
      (l : Fin (n + m) → Λ) (s : S) (a₀ : MvPolynomial (Fin (n + m)) R),
      (∀ i : Fin n, l (Fin.castAdd m i) = α (P.val i)) ∧
      (∀ j : Fin t, F (Fin.natAdd c j) = rename (Fin.castAdd m) (P.relation j)) ∧
      (∀ j, aeval l (F j) = 0) ∧
      C s.val - a₀ * Matrix.det (fun i j : Fin c ↦
        pderiv (Fin.castLE hc i) (F (Fin.castAdd t j))) ∈ Ideal.span (Set.range F) ∧
      ∀ j : Fin (c + t), c ≤ j.val → C s.val * F j ∈
        Ideal.span {f | ∃ k : Fin (c + t), k.val < c ∧ f = F k} := by
  classical
  obtain ⟨f, l, s₀, a₀, a, sg, sf, hl, hidentity, hg, hf⟩ :=
    exists_delocalization_denominator_data α S P hc Q β γ hfactor hmap hval
  let Fs : Fin c → MvPolynomial (Fin (n + m)) R := fun j ↦ C (sf j).val * f j
  let F : Fin (c + t) → MvPolynomial (Fin (n + m)) R :=
    Fin.addCases Fs (fun j ↦ rename (Fin.castAdd m) (P.relation j))
  let ug : S := ∏ j, sg j
  let uf : S := ∏ j, sf j
  let s : S := s₀ * ug * uf
  let I : Ideal (MvPolynomial (Fin (n + m)) R) := Ideal.span (Set.range Fs)
  have hI : I ≤ Ideal.span {p | ∃ k : Fin (c + t), k.val < c ∧ p = F k} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply Ideal.subset_span
    exact ⟨Fin.castAdd t j, j.isLt, by simp [F]⟩
  have hIJ : I ≤ Ideal.span (Set.range F) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨Fin.castAdd t j, by simp [F]⟩
  have hΔ : Matrix.det (fun i j : Fin c ↦
        pderiv (Fin.castLE hc i) (F (Fin.castAdd t j))) =
      C uf.val * Matrix.det (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j)) := by
    simp only [F, Fs, Fin.addCases_left, pderiv_C_mul]
    have hM : Matrix.of (fun i j : Fin c ↦ C (sf j).val *
        pderiv (Fin.castLE hc i) (f j)) =
        (fun i j : Fin c ↦ C (sf j).val * pderiv (Fin.castLE hc i) (f j)) := by
      apply Matrix.ext
      intro i j
      exact Matrix.of_apply _ i j
    rw [← hM, Matrix.det_mul_row]
    simp [uf, map_prod]
  refine ⟨F, l, s, C ug.val * a₀, hl, ?_, ?_, ?_, ?_⟩
  · intro j
    simp [F]
  · intro j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · simpa [F, Fs] using hf j
    · simp only [F, Fin.addCases_right, aeval_rename]
      have he : aeval (l ∘ Fin.castAdd m) = α.comp (aeval P.val) := by
        ext i
        simpa using hl i
      rw [he]
      simp
  · have hsum : (∑ j, a j * f j) ∈ Ideal.span (Set.range f) := by
      apply Ideal.sum_mem
      intro j _
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have hu : C uf.val * (∑ j, a j * f j) ∈ I := by
      simpa [I, Fs, uf] using product_mul_mem_scaled_span f (fun j ↦ (sf j).val) hsum
    have hh := hIJ (I.mul_mem_left (C ug.val) hu)
    convert hh using 1
    rw [hΔ]
    simp only [s, Submonoid.coe_mul, map_mul]
    rw [hidentity]
    ring
  · intro j
    refine Fin.addCases (fun j hj ↦ ?_) (fun j hj ↦ ?_) j
    · simp only [Fin.val_castAdd] at hj
      omega
    · have hu : C uf.val * (C (sg j).val *
          rename (Fin.castAdd m) (P.relation j)) ∈ I := by
        simpa [I, Fs, uf] using
          product_mul_mem_scaled_span f (fun j ↦ (sf j).val) (hg j)
      have hh := hI (I.mul_mem_left (C s₀.val *
        C ((∏ k ∈ Finset.univ.erase j, sg k) : S).val) hu)
      convert hh using 1
      simp only [F, Fin.addCases_right, s, Submonoid.coe_mul, map_mul]
      have hprod :
          C ((∏ k ∈ Finset.univ.erase j, sg k) : S).val * C (sg j).val =
            (C ug.val : MvPolynomial (Fin (n + m)) R) := by
        rw [← map_mul, ← Submonoid.coe_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      rw [← hprod]
      ring

end Algebra
