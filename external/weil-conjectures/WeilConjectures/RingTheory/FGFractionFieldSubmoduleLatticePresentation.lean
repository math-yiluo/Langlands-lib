/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Localization.Integer

/-!
# Clearing denominators in a finitely generated fraction-field submodule

Source: Stacks Project, Algebra, Tag 00PE, proof, first and second paragraphs
(blueprint: lem-weil-pbc-fg-fraction-submodule-lattice-presentation).
-/

@[expose] public section

universe u v

namespace Submodule

open scoped Pointwise

private theorem exists_smul_mem_of_mem_fraction_span
    {R : Type u} [CommRing R] [IsDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (P : Submodule R V) (y : V) (hy : y ∈ Submodule.span K (P : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • y ∈ P := by
  classical
  induction hy using Submodule.closure_induction with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨a, ha, hay⟩ := ihy
    obtain ⟨b, hb, hbz⟩ := ihz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    apply P.add_mem
    · rw [mul_comm a b, mul_smul]
      exact P.smul_mem b hay
    · simpa [mul_smul] using P.smul_mem a hbz
  | smul_mem c y hy =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R c
    have hb' : algebraMap R K b ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    convert P.smul_mem a hy using 1
    simp only [← algebraMap_smul K b, ← algebraMap_smul K a, smul_smul]
    rw [mul_div_cancel₀ _ hb']

private theorem exists_integral_lattice_of_fg_of_span_eq_top
    {R : Type u} [CommRing R] [IsDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (s : ℕ) (P : Submodule R (Fin s → K)) (hP : P.FG)
    (hspan : Submodule.span K (P : Set (Fin s → K)) = ⊤) :
    ∃ N : Submodule R (Fin s → R), ∃ d : R,
      d ≠ 0 ∧ d • (⊤ : Submodule R (Fin s → R)) ≤ N ∧ Nonempty (P ≃ₗ[R] N) := by
  classical
  let ι : (Fin s → R) →ₗ[R] (Fin s → K) :=
    { toFun := fun m i ↦ algebraMap R K (m i)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp [Algebra.smul_def] }
  have hι : Function.Injective ι := by
    intro a b h
    ext i
    exact IsFractionRing.injective R K (congrFun h i)
  obtain ⟨t, ht⟩ := hP
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (fun i : t × Fin s ↦ (i.1 : Fin s → K) i.2)
  have ha0 : (a : R) ≠ 0 := nonZeroDivisors.ne_zero a.property
  let μ : (Fin s → K) →ₗ[R] (Fin s → K) := LinearMap.lsmul R _ (a : R)
  have hμ : Function.Injective μ := by
    intro m n he
    ext i
    apply mul_left_cancel₀ (show algebraMap R K (a : R) ≠ 0 by simp [ha0])
    simpa [μ, Algebra.smul_def] using congrFun he i
  have hPa : P.map μ ≤ ι.range := by
    rw [Submodule.map_le_iff_le_comap, ← ht, Submodule.span_le]
    intro m hm
    have hi (i : Fin s) := ha (⟨m, hm⟩, i)
    choose n hn using hi
    exact ⟨n, funext hn⟩
  let N : Submodule R (Fin s → R) := (P.map μ).comap ι
  have hNmap : N.map ι = P.map μ := by
    rw [Submodule.map_comap_eq]
    exact inf_eq_right.mpr hPa
  let e : P ≃ₗ[R] N :=
    Submodule.equivMapOfInjective μ hμ P ≪≫ₗ
      (LinearEquiv.ofEq _ _ hNmap.symm) ≪≫ₗ
        (Submodule.equivMapOfInjective ι hι N).symm
  have hb (i : Fin s) : ∃ b : R, b ≠ 0 ∧ b • ι (Pi.single i 1) ∈ P :=
    exists_smul_mem_of_mem_fraction_span P _ (by rw [hspan]; trivial)
  choose b hb0 hbi using hb
  let d : R := (a : R) * ∏ i : Fin s, b i
  have hd : d ≠ 0 := mul_ne_zero ha0 (Finset.prod_ne_zero_iff.mpr (by simp [hb0]))
  refine ⟨N, d, hd, ?_, ⟨e⟩⟩
  rintro m ⟨n, _, rfl⟩
  have hn : n = ∑ i : Fin s, n i • Pi.single i (1 : R) := by
    ext j
    simp [Pi.single_apply]
  change d • n ∈ N
  rw [hn, Finset.smul_sum]
  apply N.sum_mem
  intro i _
  rw [smul_comm d (n i)]
  apply N.smul_mem
  change ι (d • Pi.single i 1) ∈ P.map μ
  refine ⟨(∏ j ∈ Finset.univ.erase i, b j) • (b i • ι (Pi.single i 1)),
    P.smul_mem _ (hbi i), ?_⟩
  dsimp [μ, d]
  simp only [map_smul, ← mul_smul]
  congr 1
  rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

/-- A finite fraction-field submodule is isomorphic to a submodule of a free module of
rank at most the ambient dimension, containing a nonzero scalar multiple of that free module.
Source: Stacks Project, Algebra, Tag 00PE, proof, reduction to a spanning submodule and
clearing denominators in the finite case
(blueprint: lem-weil-pbc-fg-fraction-submodule-lattice-presentation).

Proof: Let V be the K-linear span of M inside K^r. Its dimension s is at most r. A
K-basis identifies V with K^s and transports M to a finitely generated R-submodule
spanning K^s. Write each coordinate of each of its finitely many generators as a
fraction of elements of R. Multiply by the product a of their nonzero denominators.
Then a is nonzero, and aM lies in the coordinatewise image of R^s in K^s. The algebra
map R → K is injective, so its coordinatewise map identifies aM with an R-submodule
N of R^s. Multiplication by a is an isomorphism onto its image because a is nonzero
in the field K; together these maps give M ≃ N. The transported module N still spans
K^s. Express each standard basis vector as a finite K-linear combination of elements
of N. Multiplying by a common nonzero denominator d makes all coefficients integral,
so d times every standard basis vector belongs to N. By R-linearity, dR^s ⊆ N.
For s = 0 the module is zero, take N = 0 and d = 1; an empty denominator product is 1.
No Noetherianity, locality, or dimension assumption is needed for this construction. -/
theorem exists_lattice_presentation_of_fg
    {R : Type u} [CommRing R] [IsDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (r : ℕ) (M : Submodule R (Fin r → K)) (hM : M.FG) :
    ∃ s : ℕ, s ≤ r ∧ ∃ N : Submodule R (Fin s → R),
      ∃ d : R, d ≠ 0 ∧ d • (⊤ : Submodule R (Fin s → R)) ≤ N ∧
        Nonempty (M ≃ₗ[R] N) := by
  classical
  let V : Submodule K (Fin r → K) := Submodule.span K (M : Set (Fin r → K))
  let s : ℕ := Module.finrank K V
  have hs : s ≤ r := by
    simpa [s] using V.finrank_le
  have hMV : M ≤ V.restrictScalars R := by
    simpa [V] using Submodule.span_le_restrictScalars R K (M : Set (Fin r → K))
  let j : M →ₗ[R] V := Submodule.inclusion hMV
  let eV : V ≃ₗ[K] (Fin s → K) := (Module.finBasis K V).equivFun
  let f : M →ₗ[R] (Fin s → K) := (eV.restrictScalars R).toLinearMap.comp j
  have hf : Function.Injective f :=
    eV.injective.comp (Submodule.inclusion_injective hMV)
  let P : Submodule R (Fin s → K) := f.range
  have : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  have hP : P.FG := Submodule.fg_range f
  have hj : Submodule.span K (Set.range j) = ⊤ :=
    Submodule.span_range_inclusion_eq_top M V hMV le_rfl
  have hPspan : Submodule.span K (P : Set (Fin s → K)) = ⊤ := by
    change Submodule.span K (Set.range f) = ⊤
    have hrange : Set.range f = eV '' Set.range j := by
      exact Set.range_comp (fun z : V ↦ eV z) (fun m : M ↦ j m)
    rw [hrange]
    change Submodule.span K (eV.toLinearMap '' Set.range j) = ⊤
    rw [← Submodule.map_span, hj]
    simp
  obtain ⟨N, d, hd, hdN, ⟨eP⟩⟩ :=
    exists_integral_lattice_of_fg_of_span_eq_top s P hP hPspan
  exact ⟨s, hs, N, d, hd, hdN, ⟨LinearEquiv.ofInjective f hf ≪≫ₗ eP⟩⟩

end Submodule

