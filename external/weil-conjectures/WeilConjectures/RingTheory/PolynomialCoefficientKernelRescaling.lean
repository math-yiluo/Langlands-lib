/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial.Localization
import WeilConjectures.RingTheory.RegularSequencePolynomialVariables
import WeilConjectures.RingTheory.RegularSequencePowers
import WeilConjectures.AlgebraicGeometry.Ogoma

/-!
# Rescaling polynomial coefficients to stabilize multiplication kernels

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, justification of item 12.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory.Sequence

open scoped Pointwise

private theorem regular_ofFn_mul_units
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {d : ℕ} (f s : Fin d → R) (hs : ∀ i, IsUnit (s i))
    (h : IsRegular M (List.ofFn f)) :
    IsRegular M (List.ofFn (fun i ↦ s i * f i)) := by
  induction d generalizing M with
  | zero => simpa using h
  | succ d ih =>
    rw [List.ofFn_succ, isRegular_cons_iff] at h ⊢
    refine ⟨((hs 0).isSMulRegular M).mul h.1, ?_⟩
    have heq : (s 0 * f 0) • (⊤ : Submodule R M) = f 0 • ⊤ := by
      rw [← Submodule.ideal_span_singleton_smul,
        Ideal.span_singleton_mul_left_unit (hs 0), Submodule.ideal_span_singleton_smul]
    let E := Submodule.quotEquivOfEq _ _ heq
    apply (E.isRegular_congr _).mpr
    exact ih (fun i ↦ f i.succ) (fun i ↦ s i.succ) (fun i ↦ hs i.succ) h.2

private theorem ofList_take_ofFn
    {R : Type u} [CommRing R] {d : ℕ} (f : Fin d → R) (i : Fin d) :
    Ideal.ofList ((List.ofFn f).take i.val) =
      Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧ y = f j} := by
  apply congrArg Ideal.span
  ext y
  simp only [Set.mem_ofPred_eq, List.mem_take_iff_getElem, List.length_ofFn,
    Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨⟨j, hj.trans i.isLt⟩, hj, by simpa using h.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.val, hj, by simp⟩

private theorem exists_factor_of_polynomial_regular
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (d : ℕ) (f : Fin d → R)
    (hpoly : IsRegular (MvPolynomial (Fin d) (Localization.AtPrime p))
      (List.ofFn (fun j ↦ MvPolynomial.C (algebraMap R (Localization.AtPrime p) (f j)) *
        MvPolynomial.X j))) (e : ℕ) (he : 0 < e) (i : Fin d) :
    ∃ s : R, s ∉ p ∧
      (∀ x : MvPolynomial (Fin d) R ⧸ Ideal.span
        {y | ∃ j : Fin d, j.val < i.val ∧
          y = (MvPolynomial.C (f j) * MvPolynomial.X j) ^ e},
        (MvPolynomial.C (s * f i) * MvPolynomial.X i) • x = 0 ↔
          (MvPolynomial.C (s * f i) * MvPolynomial.X i) ^ 2 • x = 0) := by
  classical
  let A := Localization.AtPrime p
  let T := MvPolynomial (Fin d) R
  let B := MvPolynomial (Fin d) A
  let : Algebra T B := MvPolynomial.algebraMvPolynomial
  let S : Submonoid T := p.primeCompl.map MvPolynomial.C
  have : IsLocalization S B := inferInstance
  let γ : Fin d → T := fun j ↦ MvPolynomial.C (f j) * MvPolynomial.X j
  let I : Ideal T := Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧ y = γ j ^ e}
  let J : Ideal B := I.map (algebraMap T B)
  let g : Fin d → B := fun j ↦ algebraMap T B (γ j) ^ (if j = i then 1 else e)
  have hγ (j : Fin d) : algebraMap T B (γ j) =
      MvPolynomial.C (algebraMap R A (f j)) * MvPolynomial.X j := by
    change MvPolynomial.map (algebraMap R A)
      (MvPolynomial.C (f j) * MvPolynomial.X j) = _
    simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  have hpowers : IsRegular B (List.ofFn g) := by
    apply (isRegular_ofFn_pow_iff B (fun j ↦ algebraMap T B (γ j))
      (fun j ↦ if j = i then 1 else e) (fun j ↦ by split <;> omega)).mp
    simpa only [hγ] using hpoly
  have hJ : Ideal.ofList ((List.ofFn g).take i.val) = J := by
    rw [ofList_take_ofFn]
    change _ = Ideal.map (algebraMap T B) I
    dsimp only [I]
    rw [Ideal.map_span]
    apply congrArg Ideal.span
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨γ j ^ e, ⟨j, hj, rfl⟩, ?_⟩
      have hne : j ≠ i := by intro h; subst j; omega
      simp [g, hne]
    · rintro ⟨z, ⟨j, hj, rfl⟩, rfl⟩
      refine ⟨j, hj, ?_⟩
      have hne : j ≠ i := by intro h; subst j; omega
      simp [g, hne]
  have hreg : IsSMulRegular (B ⧸ J) (algebraMap T B (γ i)) := by
    have h := hpowers.toIsWeaklyRegular.regular_mod_prev i.val (by simp)
    rw [hJ, Ideal.smul_eq_mul, Ideal.mul_top] at h
    simpa [g] using h
  let : Algebra (T ⧸ I) (B ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let F : T ⧸ I →ₗ[T] B ⧸ J := (IsScalarTower.toAlgHom T (T ⧸ I) (B ⧸ J)).toLinearMap
  have : IsLocalizedModule S F := inferInstance
  let E := IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (T ⧸ I)) F
  have hreg' : IsSMulRegular (B ⧸ J) (γ i) := by
    intro x y h
    exact hreg h
  have hreg'' : IsSMulRegular (LocalizedModule S (T ⧸ I)) (γ i) :=
    (E.isSMulRegular_congr (γ i)).mpr hreg'
  have heq : {x : LocalizedModule S (T ⧸ I) | γ i • x = 0} =
      {x : LocalizedModule S (T ⧸ I) | γ i • (γ i • x) = 0} := by
    ext x
    change (γ i • x = 0) ↔ γ i • (γ i • x) = 0
    constructor
    · intro h
      simp only [h, smul_zero]
    · intro h
      exact hreg'' (by simpa only [smul_zero] using h)
  obtain ⟨t, ht⟩ := ogoma_lemma S (γ i) heq
  obtain ⟨s, hs, hst⟩ := t.property
  refine ⟨s, hs, ?_⟩
  intro x
  have h := Set.ext_iff.mp (ht 1 (by decide)) x
  have hscalar : (t : T) * γ i = MvPolynomial.C (s * f i) * MvPolynomial.X i := by
    rw [← hst]
    simp only [γ, map_mul, mul_assoc]
    rfl
  simpa only [Set.mem_ofPred_eq, pow_one, hscalar] using h

/-- Rescale a family regular in every order at a prime by coefficient factors outside that
prime so that the first and square polynomial multiplication kernels agree globally.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, justification of item 12;
Algebra, Tags 07DW and 07DV; Smoothing Ring Maps, Tag 07FC.
(blueprint: lem-weil-pbc-polynomial-coefficient-kernel-rescaling).

Proof: Write S = R \ p and T = R[X_i]. Localizing T at the image of S under C gives
R_p[X_i]. The hypothesis and Tag 07DW make the family C(f_i)X_i regular there.
Induct on t from zero to d, maintaining the kernel equalities at indices below t and
replacing only f_t at the next step. Every factor chosen lies in S, so its image in R_p
is a unit: all permutations of the localized coefficient family remain regular, as do
the polynomial family and the powered prefixes. Tag 07DV, with exponent e on earlier
terms and exponent one on the current term, makes multiplication by the current term
injective on the localized quotient by the earlier e-th powers. Thus its first and
square kernels agree on this quotient. The ring T is Noetherian, and the unlocalized
quotient is a finite T-module. Apply Ogoma (07FC) with the coefficient-image submonoid
C(S), and take exponent one, to obtain a factor C(s_t) with s_t outside p equalizing
these kernels before localization. Replace f_t by s_t f_t. The earlier equalities
involve only earlier coefficients and hence remain unchanged. All localized regularity
hypotheses persist because s_t is a unit there. At t=d the accumulated factors give the
assertion. For d=0 choose the empty family; every conclusion is vacuous. -/
theorem exists_polynomial_coefficient_kernel_rescaling
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (d : ℕ) (f : Fin d → R)
    (hperm : ∀ l : List (Localization.AtPrime p),
      (List.ofFn (fun i ↦ algebraMap R (Localization.AtPrime p) (f i))).Perm l →
        IsRegular (Localization.AtPrime p) l)
    (e : ℕ) (he : 0 < e) :
    ∃ s : Fin d → R, (∀ i, s i ∉ p) ∧
      (∀ (i : Fin d)
        (x : MvPolynomial (Fin d) R ⧸ Ideal.span
          {y | ∃ j : Fin d, j.val < i.val ∧
            y = (MvPolynomial.C (s j * f j) * MvPolynomial.X j) ^ e}),
        (MvPolynomial.C (s i * f i) * MvPolynomial.X i) • x = 0 ↔
          (MvPolynomial.C (s i * f i) * MvPolynomial.X i) ^ 2 • x = 0) := by
  classical
  let K (s : Fin d → R) (i : Fin d) : Prop :=
    ∀ x : MvPolynomial (Fin d) R ⧸ Ideal.span
      {y | ∃ j : Fin d, j.val < i.val ∧
        y = (MvPolynomial.C (s j * f j) * MvPolynomial.X j) ^ e},
      (MvPolynomial.C (s i * f i) * MvPolynomial.X i) • x = 0 ↔
        (MvPolynomial.C (s i * f i) * MvPolynomial.X i) ^ 2 • x = 0
  have congrK (s s' : Fin d → R) (i : Fin d)
      (hs : ∀ j : Fin d, j.val ≤ i.val → s j = s' j) : K s i ↔ K s' i := by
    have hI : Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧
        y = (MvPolynomial.C (s j * f j) * MvPolynomial.X j) ^ e} =
        Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧
        y = (MvPolynomial.C (s' j * f j) * MvPolynomial.X j) ^ e} := by
      apply congrArg Ideal.span
      ext y
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, by rw [hs j (Nat.le_of_lt hj)]⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, by rw [hs j (Nat.le_of_lt hj)]⟩
    dsimp only [K]
    rw [hI, hs i le_rfl]
  have induction_claim (n : ℕ) (hn : n ≤ d) :
      ∃ s : Fin d → R, (∀ i, s i ∉ p) ∧ ∀ i : Fin d, i.val < n → K s i := by
    induction n with
    | zero =>
      refine ⟨fun _ ↦ 1, (fun _ ↦ p.ne_top_iff_one.mp (inferInstance : p.IsPrime).ne_top), ?_⟩
      intro i hi
      omega
    | succ n ih =>
      obtain ⟨s, hs, hk⟩ := ih (by omega)
      let i : Fin d := ⟨n, by omega⟩
      let A := Localization.AtPrime p
      let g : Fin d → A := fun j ↦ algebraMap R A (s j * f j)
      have hregular : IsRegular A (List.ofFn g) := by
        have h := regular_ofFn_mul_units
          (fun j ↦ algebraMap R A (f j)) (fun j ↦ algebraMap R A (s j))
          (fun j ↦ IsLocalization.map_units A (⟨s j, hs j⟩ : p.primeCompl))
          (hperm _ (List.Perm.refl _))
        simpa only [g, map_mul] using h
      have hproper : Ideal.ofList (List.ofFn g) ≠ ⊤ := by
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top, ne_eq, eq_comm]
          using hregular.top_ne_smul
      have horders : ∀ l : List A, (List.ofFn g).Perm l → IsRegular A l := by
        intro l hl
        exact IsLocalRing.isRegular_of_perm hregular hl
      have hiff := isRegular_permutations_subsequences_polynomial_iff d g hproper
      have hpoly := hiff.2.mp (hiff.1.mp horders)
      obtain ⟨t, ht, hfactor⟩ :=
        exists_factor_of_polynomial_regular p d (fun j ↦ s j * f j) hpoly e he i
      let s' := Function.update s i (t * s i)
      have hs' : ∀ j : Fin d, s' j ∉ p := by
        intro j
        by_cases hji : j = i
        · subst j
          simpa [s'] using p.primeCompl.mul_mem ht (hs i)
        · simpa [s', hji] using hs j
      refine ⟨s', hs', ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        have hI : Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧
            y = (MvPolynomial.C (s' j * f j) * MvPolynomial.X j) ^ e} =
            Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧
            y = (MvPolynomial.C (s j * f j) * MvPolynomial.X j) ^ e} := by
          apply congrArg Ideal.span
          ext y
          have heq (j : Fin d) (hj : j.val < i.val) : s' j = s j := by
            have hne : j ≠ i := by intro h; subst j; omega
            simp [s', hne]
          constructor
          · rintro ⟨j, hj, rfl⟩
            exact ⟨j, hj, by rw [heq j hj]⟩
          · rintro ⟨j, hj, rfl⟩
            exact ⟨j, hj, by rw [heq j hj]⟩
        dsimp only [K]
        rw [hI]
        simpa [s', mul_assoc] using hfactor
      · have hjn : j.val < n := by
          have hne : j.val ≠ n := by
            intro h
            exact hji (Fin.ext h)
          omega
        apply (congrK s s' j ?_).mp (hk j hjn)
        intro k hk
        have hne : k ≠ i := by
          intro h
          subst k
          have : i.val = n := rfl
          omega
        simp [s', hne]
  obtain ⟨s, hs, hk⟩ := induction_claim d le_rfl
  exact ⟨s, hs, fun i ↦ hk i i.isLt⟩

end RingTheory.Sequence
