/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorConormalComparisonPredicate
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # A free presentation of the exterior conormal by Koszul wedge cycles

Source: Stacks Project, Tags 0622 and 0623; the exterior universal property.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- A wedge, its finite tuple of ideal elements, and its actual cycle after
base change to the quotient. All entries are concrete data, with the last field
certifying the chosen representative. 
(blueprint: new-e1-koszul-conormal-cycle-presentation)
-/
structure KoszulConormalWedgeCycle (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) where
  r : ℕ
  g : Fin r → I
  v : Fin n → (Fin r →₀ A)
  z : (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
    (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)))).cycles n
  hz : (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
    (ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)))).iCycles n z =
      (exteriorPower.ιMulti A n v) ⊗ₜ[A] (1 : A ⧸ I)

/-- Evaluate each Koszul wedge-cycle generator at its exterior conormal wedge. 
(blueprint: new-e1-koszul-conormal-cycle-presentation)
-/
noncomputable def koszulConormalCyclePresentation (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    (KoszulConormalWedgeCycle A I n →₀ A) →ₗ[A] conormalExteriorModule A I n :=
  Finsupp.linearCombination A fun s ↦ exteriorPower.ιMulti (A ⧸ I) n
    (fun j ↦ I.toCotangent (Finsupp.linearCombination A s.g (s.v j)))

private theorem koszulBoundary_wedge (A : Type u) [CommRing A]
    (r n : ℕ) (f : Fin r → A) (v : Fin (n + 1) → (Fin r →₀ A)) :
    ExteriorAlgebra.koszulBoundary A r f n (exteriorPower.ιMulti A (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : A) ^ (i.val + 2) *
        Finsupp.linearCombination A f (v i)) •
          exteriorPower.ιMulti A n (v ∘ i.succAbove) := by
  obtain ⟨D, _, _, huniq, _, _, _, hform, _, _⟩ :=
    ExteriorAlgebra.koszul_differential A (Fin r →₀ A) (Finsupp.linearCombination A f)
  have hD : CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A (Fin r →₀ A))) (Finsupp.linearCombination A f) = D := by
    apply huniq
    · exact CliffordAlgebra.contractLeft_one _ _
    · intro w x
      simpa only [Algebra.smul_def] using
        CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm A (Fin r →₀ A)))
          (Finsupp.linearCombination A f) w x
  apply Subtype.val_injective
  simpa [ExteriorAlgebra.koszulBoundary, hD, Algebra.smul_def] using hform n v

private theorem tensorKoszul_d_zero (A : Type u) [CommRing A]
    (I : Ideal A) (r : ℕ) (g : Fin r → I) (i j : ℕ) :
    (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
      (ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A)))).d i j = 0 := by
  classical
  by_cases hij : i = j + 1
  · subst i
    change (tensorRight (ModuleCat.of A (A ⧸ I))).map
      ((ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A))).d (j + 1) j) = 0
    simp only [ExteriorAlgebra.koszulComplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply LinearMap.ext
    intro y
    change ExteriorAlgebra.koszulBoundary A r (fun k ↦ (g k : A)) j
      (exteriorPower.ιMulti A (j + 1) v) ⊗ₜ[A] y = 0
    rw [koszulBoundary_wedge, TensorProduct.sum_tmul]
    apply Finset.sum_eq_zero
    intro k hk
    rw [TensorProduct.smul_tmul]
    have he : Finsupp.linearCombination A (fun k ↦ (g k : A)) =
        I.subtype.comp (Finsupp.linearCombination A g) := by
      ext k
      simp
    have hmem : Finsupp.linearCombination A (fun k ↦ (g k : A)) (v k) ∈ I := by
      rw [he]
      exact (Finsupp.linearCombination A g (v k)).property
    have hz : (((-1 : A) ^ (k.val + 2) *
        Finsupp.linearCombination A (fun k ↦ (g k : A)) (v k)) • y : A ⧸ I) = 0 := by
      change Ideal.Quotient.mk I _ * y = 0
      rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, mul_zero, zero_mul]
    rw [hz, TensorProduct.tmul_zero]
  · have hz := (ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A))).shape i j
      (by simpa [eq_comm] using hij)
    change (tensorRight (ModuleCat.of A (A ⧸ I))).map
      ((ExteriorAlgebra.koszulComplex A r (fun k ↦ (g k : A))).d i j) = 0
    rw [hz, Functor.map_zero]

/-- Koszul wedge cycles generate the exterior conormal over the ambient ring.
Source: Stacks Project, Tags 0622 and 0623; Mathlib's exterior-power spanning theorem.
(blueprint: new-e1-koszul-conormal-cycle-presentation).

Proof: Wedges of conormal elements span the exterior power over A/I. Lift every
conormal element to an element g_j of I. Use the tuple g indexed by Fin n and
choose v_j to be the j-th standard basis vector. After tensoring its Koszul
complex with A/I every differential is zero: the contraction formula is a sum
of terms with a coefficient g_j, and all these coefficients vanish in A/I.
Thus the tensor of the basis wedge with 1 has a cycle representative. Its
image under the displayed presentation is the prescribed conormal wedge.
Finally every coefficient in A/I lifts to A, so the same wedges span over A.
For n=0 the empty tuple supplies the unit; the argument includes I=0, I=A,
and rings of characteristic two without modification. -/
theorem koszulConormalCyclePresentation_surjective (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    Function.Surjective (koszulConormalCyclePresentation A I n) := by
  classical
  let φ := koszulConormalCyclePresentation A I n
  have hw (w : Fin n → I.Cotangent) :
      ∃ x, φ x = exteriorPower.ιMulti (A ⧸ I) n w := by
    choose g hg using fun j ↦ I.toCotangent_surjective (w j)
    let v : Fin n → (Fin n →₀ A) := fun j ↦ Finsupp.single j 1
    let L := (((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)).obj
      (ExteriorAlgebra.koszulComplex A n (fun j ↦ (g j : A))))
    let e := L.iCyclesIso n ((ComplexShape.down ℕ).next n) rfl
      (tensorKoszul_d_zero A I n g n ((ComplexShape.down ℕ).next n))
    let y := exteriorPower.ιMulti A n v ⊗ₜ[A] (1 : A ⧸ I)
    let z := e.inv y
    have hz : L.iCycles n z = y := by
      exact congrArg (fun f ↦ f y) e.inv_hom_id
    let s : KoszulConormalWedgeCycle A I n := ⟨n, g, v, z, hz⟩
    refine ⟨Finsupp.single s 1, ?_⟩
    simp only [φ, koszulConormalCyclePresentation, Finsupp.linearCombination_single, one_smul]
    change exteriorPower.ιMulti (A ⧸ I) n
      (fun j ↦ I.toCotangent (Finsupp.linearCombination A g (Finsupp.single j 1))) = _
    simp only [Finsupp.linearCombination_single, one_smul, hg]
  intro x
  have hx : x ∈ Submodule.span (A ⧸ I)
      (Set.range (exteriorPower.ιMulti (A ⧸ I) n (M := I.Cotangent))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    exact hw w
  | zero => exact ⟨0, map_zero φ⟩
  | add y z hy hz ihy ihz =>
    obtain ⟨a, ha⟩ := ihy
    obtain ⟨b, hb⟩ := ihz
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | smul b y hy ih =>
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨z, hz⟩ := ih
    refine ⟨a • z, ?_⟩
    rw [map_smul, hz, ← ha]
    rfl

end AlgebraicGeometry
