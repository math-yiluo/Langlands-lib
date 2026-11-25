/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import WeilConjectures.RingTheory.GradedNakayamaGeneration

/-!
# Existence of minimal finite graded free presentations

Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, graded Nakayama construction of a
minimal presentation, expanded from the blueprint (blueprint:
lem-sc-p1-minimal-graded-presentation-exists).
-/

@[expose] public section

universe u

namespace MvPolynomial

-- The shifted-grading construction follows the proved private helpers in
-- WeilConjectures.RingTheory.GradedFreeCover. It is repeated locally because
-- those helpers are private; no additional generation theorem is needed here.
private noncomputable def flatten {k : Type u} [Field k] {r : ℕ} :
    (Fin r →₀ MvPolynomial (Fin 2) k) ≃ₗ[k] (Fin r × (Fin 2 →₀ ℕ) →₀ k) :=
  (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv k)).trans
    (Finsupp.curryLinearEquiv k).symm

private noncomputable def shiftedGrade {k : Type u} [Field k] {r : ℕ}
    (e : Fin r → ℤ) (j : ℤ) : Submodule k (Fin r →₀ MvPolynomial (Fin 2) k) :=
  (Finsupp.supported k k {z | (z.2.degree : ℤ) + e z.1 = j}).comap
    flatten.toLinearMap

private theorem mem_variables_of_constantCoeff_zero {k : Type u} [Field k]
    (f : MvPolynomial (Fin 2) k) (hf : constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) := by
  change f ∈ idealOfVars (Fin 2) k
  rw [← pow_one (idealOfVars (Fin 2) k), mem_pow_idealOfVars_iff']
  intro t ht
  have hz : t = 0 := (Finsupp.degree_eq_zero_iff t).mp (by omega)
  subst t
  exact hf

private theorem quotient_smul_constantCoeff {k : Type u} [Field k]
    {N : Type u} [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    [Module k N] [IsScalarTower k (MvPolynomial (Fin 2) k) N]
    (f : MvPolynomial (Fin 2) k) (x : N) :
    let I := Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) N)
    I.mkQ (f • x) = constantCoeff f • I.mkQ x := by
  intro I
  have hd : f - C (constantCoeff f) ∈
      Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) :=
    mem_variables_of_constantCoeff_zero _ (by simp)
  have hz : I.mkQ ((f - C (constantCoeff f)) • x) = 0 :=
    (Submodule.Quotient.mk_eq_zero I).mpr (Submodule.smul_mem_smul hd (Submodule.mem_top))
  rw [sub_smul, map_sub, sub_eq_zero] at hz
  rw [hz]
  change I.mkQ ((algebraMap k (MvPolynomial (Fin 2) k) (constantCoeff f)) • x) = _
  rw [IsScalarTower.algebraMap_smul]
  exact (I.mkQ.restrictScalars k).map_smul _ _

private theorem exists_homogeneous_quotient_basis {k : Type u} [Field k]
    {N : Type u} [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    [Module k N] [IsScalarTower k (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N)
    (hN : ∃ s : Set N, s.Finite ∧
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤) :
    let I := Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
      (⊤ : Submodule (MvPolynomial (Fin 2) k) N)
    ∃ (r : ℕ) (n : Fin r → N) (d : Fin r → ℤ),
      (∀ i, n i ∈ ℳ (d i)) ∧
      Submodule.span k (Set.range (fun i ↦ I.mkQ (n i))) = ⊤ ∧
      LinearIndependent k (fun i ↦ I.mkQ (n i)) := by
  classical
  intro I
  obtain ⟨s, hs, hhom, hspan⟩ := hN
  let U := Submodule.span k (I.mkQ '' s)
  have hmem (x : N) (hx : x ∈ Submodule.span (MvPolynomial (Fin 2) k) s) :
      I.mkQ x ∈ U := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa using U.add_mem ihx ihy
    | smul f x hx ih =>
      rw [quotient_smul_constantCoeff]
      exact U.smul_mem _ ih
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := I.mkQ_surjective y
    exact hmem x (by rw [hspan]; trivial)
  obtain ⟨t, hts, htsSpan, htli⟩ := exists_linearIndependent k (I.mkQ '' s)
  have htfin : t.Finite := (hs.image I.mkQ).subset hts
  let : Fintype t := htfin.fintype
  let r := Fintype.card t
  let e : Fin r ≃ t := (Fintype.equivFin t).symm
  have hlift (i : Fin r) : ∃ x ∈ s, I.mkQ x = (e i).val := hts (e i).property
  choose n hn hqn using hlift
  have hdegrees (i : Fin r) : ∃ j, n i ∈ ℳ j := hhom (n i) (hn i)
  choose d hd using hdegrees
  refine ⟨r, n, d, hd, ?_, ?_⟩
  · have heRange : Set.range (fun i ↦ I.mkQ (n i)) = t := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        change I.mkQ (n i) ∈ t
        rw [hqn]
        exact (e i).property
      · intro hy
        obtain ⟨i, hi⟩ := e.surjective ⟨y, hy⟩
        exact ⟨i, (hqn i).trans (congrArg Subtype.val hi)⟩
    rw [heRange, htsSpan]
    exact hU
  · have heq : (fun i ↦ I.mkQ (n i)) = (fun z : t ↦ (z : N ⧸ I)) ∘ e := by
      funext i
      exact hqn i
    rw [heq]
    exact htli.comp e e.injective

/-- Every finite homogeneous spanning set admits a minimal finite graded free presentation.
Source: step 1 of blueprint node `lem-sc-p1-graded-nakayama-free`, refining the graded Hilbert
syzygy argument cited in blueprint `theorem-riemann-roch-coherent-serre-duality`. The construction
below is the standard explicit expansion of that step, rather than a quoted blueprint proof.
(blueprint: lem-sc-p1-minimal-graded-presentation-exists)

Proof: restrict scalars along the constant-polynomial embedding to give `N` its `k`-module
structure. Put `I = (x₀,x₁)` and `Q = N/IN`. In `Q`, multiplication by a polynomial equals
multiplication by its constant coefficient: the difference lies in `I` and acts by zero. Hence
the images of the given finite homogeneous generating set span `Q` over `k`. Extract a basis
from this finite spanning family and retain its original homogeneous lifts `nᵢ`, with degrees
`dᵢ`. Set `F = Fin r → S`. Its degree-`j` subgroup consists of coefficient tuples whose ith
coordinate is homogeneous of degree `j-dᵢ` (zero if that degree is negative). Decompose every
polynomial coordinate into its homogeneous components, translate their degrees by `dᵢ`, and sum
over the finite union of these translated supports. Uniqueness of polynomial homogeneous
components gives uniqueness of this decomposition; homogeneous multiplication adds degrees.
The standard basis vector `eᵢ` has degree `dᵢ`. Define `q(a) = ∑ i, aᵢ • nᵢ`. Scalar
compatibility in `N` shows it preserves degrees. Graded Nakayama generation, applied to the
chosen lifts, makes `q` surjective. If `q(a)` belongs to `IN`, linear independence of the chosen
basis of `Q` forces every constant coefficient of `aᵢ` to vanish. Each `aᵢ` then lies in `I`,
so the finite basis expansion shows `a` belongs to `IF`. This proves minimality. For `Q = 0`,
the chosen basis is empty; graded Nakayama gives `N = 0`, yielding the zero presentation. -/
theorem exists_minimal_graded_presentation (k : Type u) [Field k]
    (N : Type u) [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : N),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j →
        f • x ∈ ℳ ((n : ℤ) + j))
    (hN : ∃ s : Set N, s.Finite ∧
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤) :
    ∃ (F : ModuleCat.{u} (MvPolynomial (Fin 2) k)) (ℱ : ℤ → AddSubgroup F),
      DirectSum.IsInternal ℱ ∧
      (∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : F),
        f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℱ j →
          f • x ∈ ℱ ((n : ℤ) + j)) ∧
      ∃ (r : ℕ) (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) F)
        (d : Fin r → ℤ),
        (∀ i : Fin r, b i ∈ ℱ (d i)) ∧
        ∃ q : F →ₗ[MvPolynomial (Fin 2) k] N,
          Function.Surjective q ∧
          (∀ (j : ℤ) (x : F), x ∈ ℱ j → q x ∈ ℳ j) ∧
          (∀ x : F,
            q x ∈ Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
              (⊤ : Submodule (MvPolynomial (Fin 2) k) N) →
            x ∈ Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
              (⊤ : Submodule (MvPolynomial (Fin 2) k) F)) := by
  classical
  have mem_shiftedGrade {k : Type u} [Field k] {r : ℕ}
      (e : Fin r → ℤ) (j : ℤ) (x : Fin r →₀ MvPolynomial (Fin 2) k) :
      x ∈ shiftedGrade e j ↔
        ∀ a t, (x a).coeff t ≠ 0 → (t.degree : ℤ) + e a = j := by
    simp only [shiftedGrade, Submodule.mem_comap, Finsupp.mem_supported,
      Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq,
      Prod.forall]
    rfl
  have shiftedGrade_internal {k : Type u} [Field k] {r : ℕ}
      (e : Fin r → ℤ) :
      DirectSum.IsInternal (fun j ↦ (shiftedGrade (k := k) e j).toAddSubgroup) := by
    classical
    let δ : Fin r × (Fin 2 →₀ ℕ) → ℤ := fun z ↦ (z.2.degree : ℤ) + e z.1
    let A : ℤ → Submodule k (Fin r × (Fin 2 →₀ ℕ) →₀ k) :=
      fun j ↦ Finsupp.supported k k {z | δ z = j}
    have hi : iSupIndep A := by
      intro j
      have hd : Disjoint (Finsupp.supported k k {z | δ z = j})
          (⨆ l : {l : ℤ // l ≠ j}, Finsupp.supported k k {z | δ z = l.1}) := by
        rw [← Finsupp.supported_iUnion]
        apply Finsupp.disjoint_supported_supported
        apply Set.disjoint_left.mpr
        intro z hj hn
        obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hn
        exact l.property (hl.symm.trans hj)
      simpa only [A, iSup_subtype] using hd
    have hs : iSup A = ⊤ := by
      change (⨆ j, Finsupp.supported k k {z | δ z = j}) = ⊤
      rw [← Finsupp.supported_iUnion]
      have hset : (⋃ j : ℤ, {z | δ z = j}) = Set.univ := by
        ext z
        simp
      rw [hset, Finsupp.supported_univ]
    let E := Submodule.orderIsoMapComap (flatten (k := k) (r := r)).symm
    have hEi : iSupIndep (fun j ↦ E (A j)) := hi.map_orderIso E
    have hEs : (⨆ j, E (A j)) = ⊤ := by
      rw [← E.map_iSup, hs, E.map_top]
    have hI := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hEi hEs
    have hE : (fun j ↦ E (A j)) = fun j ↦ shiftedGrade (k := k) e j := by
      funext j
      exact Submodule.map_equiv_eq_comap_symm _ _
    rw [hE] at hI
    exact hI
  have shiftedGrade_coefficient {k : Type u} [Field k] {r : ℕ}
      {e : Fin r → ℤ} {j : ℤ} {x : Fin r →₀ MvPolynomial (Fin 2) k}
      (hx : x ∈ shiftedGrade e j) (a : Fin r) :
      x a = 0 ∨ ∃ n : ℕ, (x a).IsHomogeneous n ∧ (n : ℤ) + e a = j := by
    classical
    by_cases hzero : x a = 0
    · exact Or.inl hzero
    · obtain ⟨t, ht⟩ := exists_coeff_ne_zero hzero
      have hx' := (mem_shiftedGrade e j x).mp hx
      refine Or.inr ⟨t.degree, ?_, hx' a t ht⟩
      intro d hd
      rw [Pi.one_def, ← Finsupp.degree_eq_weight_one]
      have hdt := hx' a d hd
      have htt := hx' a t ht
      omega
  have shiftedGrade_smul {k : Type u} [Field k] {r : ℕ}
      (e : Fin r → ℤ) (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k)
      (x : Fin r →₀ MvPolynomial (Fin 2) k)
      (hs : s ∈ homogeneousSubmodule (Fin 2) k n) (hx : x ∈ shiftedGrade e j) :
      s • x ∈ shiftedGrade e ((n : ℤ) + j) := by
    apply (mem_shiftedGrade _ _ _).mpr
    intro a t ht
    rw [Finsupp.smul_apply, smul_eq_mul] at ht
    rcases shiftedGrade_coefficient hx a with hz | ⟨m, hm, he⟩
    · simp [hz] at ht
    · have hmul := (hs : s.IsHomogeneous n).mul hm
      have hdeg := hmul ht
      rw [Pi.one_def, ← Finsupp.degree_eq_weight_one] at hdeg
      rw [hdeg, Nat.cast_add]
      omega
  have shiftedGrade_single {k : Type u} [Field k] {r : ℕ}
      (e : Fin r → ℤ) (a : Fin r) :
      Finsupp.single a (1 : MvPolynomial (Fin 2) k) ∈ shiftedGrade e (e a) := by
    classical
    apply (mem_shiftedGrade _ _ _).mpr
    intro a' t ht
    by_cases ha : a' = a
    · subst a'
      simp only [Finsupp.single_eq_same] at ht
      have hdeg := (isHomogeneous_one (Fin 2) k) ht
      rw [Pi.one_def, ← Finsupp.degree_eq_weight_one] at hdeg
      simp [hdeg]
    · simp [ha] at ht
  let S := MvPolynomial (Fin 2) k
  let : Module k N := Module.compHom N (algebraMap k S)
  let : IsScalarTower k S N := IsScalarTower.of_compHom k S N
  have : Module.Finite S N := Module.Finite.of_fg_top
    (Submodule.fg_def.mpr (by
      obtain ⟨s, hs, _, hspan⟩ := hN
      exact ⟨s, hs, hspan⟩))
  let I := Ideal.span (Set.range (X : Fin 2 → S)) • (⊤ : Submodule S N)
  obtain ⟨r, n, d, hd, hgen, hli⟩ := exists_homogeneous_quotient_basis ℳ hN
  have hn : ∀ i : Fin r, SetLike.IsHomogeneousElem ℳ (n i) := fun i ↦ ⟨d i, hd i⟩
  have hspan := graded_nakayama_generation ℳ hℳ hsmul r n hn hgen
  let F := ModuleCat.of S (Fin r →₀ S)
  let ℱ : ℤ → AddSubgroup F := fun j ↦ (shiftedGrade d j).toAddSubgroup
  let q : F →ₗ[S] N := Finsupp.linearCombination S n
  refine ⟨F, ℱ, shiftedGrade_internal d, ?_, r, Finsupp.basisSingleOne, d,
    shiftedGrade_single d, q, ?_, ?_, ?_⟩
  · exact shiftedGrade_smul d
  · exact (span_range_eq_top_iff_surjective_finsuppLinearCombination S).mp hspan
  · intro j x hx
    change Finsupp.linearCombination S n x ∈ ℳ j
    rw [Finsupp.linearCombination_apply]
    apply (ℳ j).sum_mem
    intro a ha
    rcases shiftedGrade_coefficient hx a with hz | ⟨m, hm, he⟩
    · change (x a) • n a ∈ ℳ j
      rw [hz, zero_smul]
      exact (ℳ j).zero_mem
    · rw [← he]
      exact hsmul m (d a) (x a) (n a) hm (hd a)
  · intro x hx
    have hqx : I.mkQ (q x) = 0 := (Submodule.Quotient.mk_eq_zero I).mpr hx
    have hsum : ∑ a : Fin r, constantCoeff (x a) • I.mkQ (n a) = 0 := by
      have hxe : x = ∑ a : Fin r, x a • Finsupp.single a 1 := by
        ext a
        simp
      have hqb (a : Fin r) : q (Finsupp.single a 1) = n a := by
        exact (Finsupp.linearCombination_single S (v := n) 1 a).trans (one_smul S (n a))
      have hqs : q x = ∑ a : Fin r, x a • n a := by
        conv_lhs => rw [hxe]
        rw [map_sum]
        simp only [map_smul, hqb]
      rw [hqs, map_sum] at hqx
      have he (a : Fin r) : I.mkQ ((x a) • n a) = constantCoeff (x a) • I.mkQ (n a) :=
        quotient_smul_constantCoeff (k := k) (x a) (n a)
      simp_rw [he] at hqx
      exact hqx
    have hcoeff : ∀ a : Fin r, constantCoeff (x a) = 0 :=
      Fintype.linearIndependent_iff.mp hli _ hsum
    have hxe : x = ∑ a : Fin r, x a • Finsupp.single a 1 := by
      ext a
      simp
    rw [hxe]
    apply Submodule.sum_mem
    intro a _
    exact Submodule.smul_mem_smul
      (mem_variables_of_constantCoeff_zero (x a) (hcoeff a)) Submodule.mem_top

end MvPolynomial
