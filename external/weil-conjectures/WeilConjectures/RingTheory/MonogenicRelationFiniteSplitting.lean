/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.RingTheory.NagataDomainN2
import WeilConjectures.RingTheory.FiniteOverNagata

/-! # Monogenic residue polynomial and finite splitting data
Source: Stacks Project, Algebra, Tag 0334, Step 5.
(blueprint: lem-weil-pbc-monogenic-relation-finite-splitting). -/

@[expose] public section

universe u

open scoped TensorProduct nonZeroDivisors

/-- Split a given monic relation by a finite normal Nagata coefficient extension.
The ideal need not be prime or maximal; evaluation membership is transported by the map.
Source: Stacks Project, Algebra, Tag 0334, Step 5.
(blueprint: lem-weil-pbc-monogenic-relation-finite-splitting).

Proof: Choose a finite splitting field L of f mapped to K. The roots are integral
over R because f is monic. The integral closure R' of R in L is finite by the N-2
condition, normal with fraction field L, and Nagata by finite ascent. Every root
belongs to R', and the factorization in L descends to R'[X] by injectivity. Write
z for the image of x and map R[x] injectively into R'[z]. To see finiteness, take
finite R-module generators b_i of R'. Every polynomial in z with coefficients in
R' is a sum of b_i times polynomials in z with coefficients in R, so these b_i
generate R'[z] over R[x]. Map f coefficientwise to R'. Evaluation commutes with
this map and the map R[x] to R'[z], so its evaluation belongs to the extension
of I. Mapping through the injective coefficient map preserves monicity and degree.
Use Frac(R) as the splitting-field base, so the constructed coefficient ring and
field stay in the same universe as R and K. -/
theorem exists_monogenic_relation_finite_splitting
    (R : Type u) (K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : IsNagataRing R) (x : K)
    (I : Ideal (Algebra.adjoin R ({x} : Set K))) (f : Polynomial R)
    (hf : f.Monic) (hd : 0 < f.natDegree)
    (heval : Polynomial.aeval
      (⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ :
        Algebra.adjoin R ({x} : Set K)) f ∈ I) :
    ∃ (R' K' : Type u) (_ : CommRing R') (_ : IsDomain R')
      (_ : IsIntegrallyClosed R') (_ : Field K') (_ : Algebra R' K')
      (_ : IsFractionRing R' K'),
      IsNagataRing R' ∧ ∃ (z : K')
        (g : Algebra.adjoin R ({x} : Set K) →+* Algebra.adjoin R' ({z} : Set K')),
        Function.Injective g ∧ g.Finite ∧ ∃ f' : Polynomial R',
          f'.Monic ∧ 0 < f'.natDegree ∧ f'.Splits ∧
          Polynomial.aeval
            (⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩ :
              Algebra.adjoin R' ({z} : Set K')) f' ∈ I.map g := by
  classical
  let F := FractionRing R
  let q : Polynomial F := f.map (algebraMap R F)
  let L := q.SplittingField
  let C := integralClosure R L
  let : Module.Finite R C := isN2_of_isNagataRing_domain R hR L
  let : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension F
  let : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension F L
  have hC : IsNagataRing C := (finite_over_nagata_is_nagata R C hR).1
  let φ : K →ₐ[R] L := (IsScalarTower.toAlgHom R F L).comp
    (IsLocalization.algEquiv R⁰ K F).toAlgHom
  let z : L := φ x
  let S := Algebra.adjoin R ({x} : Set K)
  let T := Algebra.adjoin C ({z} : Set L)
  have hsub : S ≤ (T.restrictScalars R).comap φ := by
    apply Algebra.adjoin_le
    intro a ha
    obtain rfl : a = x := Set.mem_singleton_iff.mp ha
    exact Algebra.subset_adjoin (Set.mem_singleton z)
  let g : S →ₐ[R] T := (φ.comp S.val).codRestrict (T.restrictScalars R)
    (fun a ↦ hsub a.property)
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    exact φ.injective (congrArg Subtype.val hab)
  let : Algebra S T := g.toRingHom.toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let b : C →ₐ[R] T := IsScalarTower.toAlgHom R C T
  let ψ : S ⊗[R] C →ₐ[S] T := (AlgHom.liftEquiv R S C T) b
  have hsurj : Function.Surjective ψ := by
    rintro ⟨t, ht⟩
    have hmem : (⟨t, ht⟩ : T) ∈ ψ.range := by
      induction ht using Algebra.adjoin_induction with
      | mem a ha =>
        obtain rfl : a = z := Set.mem_singleton_iff.mp ha
        exact ⟨(⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ : S) ⊗ₜ[R] 1,
          by
            ext
            change ↑(ψ _) = z
            rw [AlgHom.liftEquiv_tmul]
            change ↑(g ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ * b 1) = z
            simp only [map_one, mul_one]
            rfl⟩
      | algebraMap c =>
        exact ⟨1 ⊗ₜ[R] c, by ext; simp [ψ, b]⟩
      | add a b ha hb hia hib => exact ψ.range.add_mem hia hib
      | mul a b ha hb hia hib => exact ψ.range.mul_mem hia hib
    exact hmem
  have hgfin : g.toRingHom.Finite := by
    change Module.Finite S T
    exact Module.Finite.of_surjective ψ.toLinearMap hsurj
  have hRC : Function.Injective (algebraMap R C) := by
    have hinj : Function.Injective ((algebraMap C L).comp (algebraMap R C)) := by
      rw [← IsScalarTower.algebraMap_eq R C L, IsScalarTower.algebraMap_eq R F L]
      exact (algebraMap F L).injective.comp (IsFractionRing.injective R F)
    intro a b hab
    exact hinj (congrArg (algebraMap C L) hab)
  let f' := f.map (algebraMap R C)
  have hfs : f'.Splits := by
    apply Polynomial.Splits.of_splits_map_of_injective
      (i := algebraMap C L) (FaithfulSMul.algebraMap_injective C L)
    · simpa only [f', q, Polynomial.map_map, ← IsScalarTower.algebraMap_eq R C L,
        IsScalarTower.algebraMap_eq R F L] using Polynomial.SplittingField.splits q
    · intro a ha
      refine ⟨⟨a, ?_⟩, rfl⟩
      apply roots_mem_integralClosure hf
      simpa only [f', Polynomial.map_map, ← IsScalarTower.algebraMap_eq R C L,
        Polynomial.aroots_def] using ha
  refine ⟨C, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hC, z, g.toRingHom, hginj, hgfin, f', hf.map _, ?_, hfs, ?_⟩
  · simpa only [f', Polynomial.natDegree_map_eq_of_injective
      hRC] using hd
  · rw [Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval
      (g (⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ : S)) f ∈ I.map g.toRingHom
    rw [Polynomial.aeval_algHom_apply]
    exact Ideal.mem_map_of_mem g.toRingHom heval

